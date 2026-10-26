import V185TrunkScan23Chunk0169

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1005666 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1005666 : Nat := 118140960795 + 1005666 * 2 ^ 59
def prefixEnd_1005666 : Nat := 4983230072969 + 3 ^ 40 * 1005666 * 2
def baseEnd_1005666 : Nat := 516390035884567560850033

theorem tailTrace_1005666 : CollatzResearch.WordTrace tailWord_1005666 prefixEnd_1005666 516390035884567560850033 := by
  unfold tailWord_1005666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169913093662827730967213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24453101583100873949245901 9169913093662827730967213)
  ·
    refine ⟨3438717410123560399112705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9169913093662827730967213 3438717410123560399112705)
    ·
      refine ⟨2579038057592670299334529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3438717410123560399112705 2579038057592670299334529)
      ·
        refine ⟨1934278543194502724500897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2579038057592670299334529 1934278543194502724500897)
        ·
          refine ⟨1450708907395877043375673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934278543194502724500897 1450708907395877043375673)
          ·
            refine ⟨1088031680546907782531755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450708907395877043375673 1088031680546907782531755)
            ·
              refine ⟨1632047520820361673797633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088031680546907782531755 1632047520820361673797633)
              ·
                refine ⟨1224035640615271255348225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632047520820361673797633 1224035640615271255348225)
                ·
                  refine ⟨918026730461453441511169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1224035640615271255348225 918026730461453441511169)
                  ·
                    refine ⟨688520047846090081133377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 918026730461453441511169 688520047846090081133377)
                    ·
                      refine ⟨516390035884567560850033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688520047846090081133377 516390035884567560850033)
                      ·
                        rfl

theorem cell23_1005666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1005666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005666 prefixEnd_1005666 := by exact prefixLift 1005666
  have htrace : WordTrace (prefixWord ++ tailWord_1005666) baseStart_1005666 baseEnd_1005666 := by
    simpa [prefixWord, tailWord_1005666, baseEnd_1005666] using wordTrace_append hprefix tailTrace_1005666
  have hstable : (prefixWord ++ tailWord_1005666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005666).length < 2 ^ (prefixWord ++ tailWord_1005666).sum := by decide
  have hdescent : baseEnd_1005666 < baseStart_1005666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005725 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1005725 : Nat := 118140960795 + 1005725 * 2 ^ 59
def prefixEnd_1005725 : Nat := 4983230072969 + 3 ^ 40 * 1005725 * 2
def baseEnd_1005725 : Nat := 516420331243182830012261

theorem tailTrace_1005725 : CollatzResearch.WordTrace tailWord_1005725 prefixEnd_1005725 516420331243182830012261 := by
  unfold tailWord_1005725
  simp only [CollatzResearch.WordTrace]
  refine ⟨36681804281437564000266629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24454536187625042666844419 36681804281437564000266629)
  ·
    refine ⟨6877838302769543250049993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36681804281437564000266629 6877838302769543250049993)
    ·
      refine ⟨5158378727077157437537495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6877838302769543250049993 5158378727077157437537495)
      ·
        refine ⟨7737568090615736156306243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5158378727077157437537495 7737568090615736156306243)
        ·
          refine ⟨11606352135923604234459365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7737568090615736156306243 11606352135923604234459365)
          ·
            refine ⟨2176191025485675793961131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11606352135923604234459365 2176191025485675793961131)
            ·
              refine ⟨3264286538228513690941697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176191025485675793961131 3264286538228513690941697)
              ·
                refine ⟨2448214903671385268206273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3264286538228513690941697 2448214903671385268206273)
                ·
                  refine ⟨1836161177753538951154705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2448214903671385268206273 1836161177753538951154705)
                  ·
                    refine ⟨1377120883315154213366029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1836161177753538951154705 1377120883315154213366029)
                    ·
                      refine ⟨516420331243182830012261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1377120883315154213366029 516420331243182830012261)
                      ·
                        rfl

theorem cell23_1005725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1005725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005725 prefixEnd_1005725 := by exact prefixLift 1005725
  have htrace : WordTrace (prefixWord ++ tailWord_1005725) baseStart_1005725 baseEnd_1005725 := by
    simpa [prefixWord, tailWord_1005725, baseEnd_1005725] using wordTrace_append hprefix tailTrace_1005725
  have hstable : (prefixWord ++ tailWord_1005725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005725).length < 2 ^ (prefixWord ++ tailWord_1005725).sum := by decide
  have hdescent : baseEnd_1005725 < baseStart_1005725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005732 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_1005732 : Nat := 118140960795 + 1005732 * 2 ^ 59
def prefixEnd_1005732 : Nat := 4983230072969 + 3 ^ 40 * 1005732 * 2
def baseEnd_1005732 : Nat := 172141308535921434208243

theorem tailTrace_1005732 : CollatzResearch.WordTrace tailWord_1005732 prefixEnd_1005732 172141308535921434208243 := by
  unfold tailWord_1005732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18341029796206102097885725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24454706394941469463847633 18341029796206102097885725)
  ·
    refine ⟨6877886173577288286707147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18341029796206102097885725 6877886173577288286707147)
    ·
      refine ⟨10316829260365932430060721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6877886173577288286707147 10316829260365932430060721)
      ·
        refine ⟨7737621945274449322545541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10316829260365932430060721 7737621945274449322545541)
        ·
          refine ⟨1450804114738959247977289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7737621945274449322545541 1450804114738959247977289)
          ·
            refine ⟨1088103086054219435982967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450804114738959247977289 1088103086054219435982967)
            ·
              refine ⟨1632154629081329153974451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088103086054219435982967 1632154629081329153974451)
              ·
                refine ⟨2448231943621993730961677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632154629081329153974451 2448231943621993730961677)
                ·
                  refine ⟨918086978858247649110629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2448231943621993730961677 918086978858247649110629)
                  ·
                    refine ⟨172141308535921434208243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 918086978858247649110629 172141308535921434208243)
                    ·
                      rfl

theorem cell23_1005732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_1005732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005732 prefixEnd_1005732 := by exact prefixLift 1005732
  have htrace : WordTrace (prefixWord ++ tailWord_1005732) baseStart_1005732 baseEnd_1005732 := by
    simpa [prefixWord, tailWord_1005732, baseEnd_1005732] using wordTrace_append hprefix tailTrace_1005732
  have hstable : (prefixWord ++ tailWord_1005732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005732).length < 2 ^ (prefixWord ++ tailWord_1005732).sum := by decide
  have hdescent : baseEnd_1005732 < baseStart_1005732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005745 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 6]
def baseStart_1005745 : Nat := 118140960795 + 1005745 * 2 ^ 59
def prefixEnd_1005745 : Nat := 4983230072969 + 3 ^ 40 * 1005745 * 2
def baseEnd_1005745 : Nat := 57381177872919194640241

theorem tailTrace_1005745 : CollatzResearch.WordTrace tailWord_1005745 prefixEnd_1005745 57381177872919194640241 := by
  unfold tailWord_1005745
  simp only [CollatzResearch.WordTrace]
  refine ⟨36682533741365107415994689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24455022494243404943996459 36682533741365107415994689)
  ·
    refine ⟨27511900306023830561996017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36682533741365107415994689 27511900306023830561996017)
    ·
      refine ⟨20633925229517872921497013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27511900306023830561996017 20633925229517872921497013)
      ·
        refine ⟨1934430490267300586390345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20633925229517872921497013 1934430490267300586390345)
        ·
          refine ⟨1450822867700475439792759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934430490267300586390345 1450822867700475439792759)
          ·
            refine ⟨2176234301550713159689139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450822867700475439792759 2176234301550713159689139)
            ·
              refine ⟨3264351452326069739533709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176234301550713159689139 3264351452326069739533709)
              ·
                refine ⟨1224131794622276152325141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3264351452326069739533709 1224131794622276152325141)
                ·
                  refine ⟨57381177872919194640241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1224131794622276152325141 57381177872919194640241)
                  ·
                    rfl

theorem cell23_1005745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 6].length) (baseStart_1005745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005745 prefixEnd_1005745 := by exact prefixLift 1005745
  have htrace : WordTrace (prefixWord ++ tailWord_1005745) baseStart_1005745 baseEnd_1005745 := by
    simpa [prefixWord, tailWord_1005745, baseEnd_1005745] using wordTrace_append hprefix tailTrace_1005745
  have hstable : (prefixWord ++ tailWord_1005745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005745).length < 2 ^ (prefixWord ++ tailWord_1005745).sum := by decide
  have hdescent : baseEnd_1005745 < baseStart_1005745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005765 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 2, 3, 2]
def baseStart_1005765 : Nat := 118140960795 + 1005765 * 2 ^ 59
def prefixEnd_1005765 : Nat := 4983230072969 + 3 ^ 40 * 1005765 * 2
def baseEnd_1005765 : Nat := 516440870469362673512077

theorem tailTrace_1005765 : CollatzResearch.WordTrace tailWord_1005765 prefixEnd_1005765 516440870469362673512077 := by
  unfold tailWord_1005765
  simp only [CollatzResearch.WordTrace]
  refine ⟨36683263201292650831722749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24455508800861767221148499 36683263201292650831722749)
  ·
    refine ⟨13756223700484744061896031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36683263201292650831722749 13756223700484744061896031)
    ·
      refine ⟨20634335550727116092844047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13756223700484744061896031 20634335550727116092844047)
      ·
        refine ⟨30951503326090674139266071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20634335550727116092844047 30951503326090674139266071)
        ·
          refine ⟨46427254989136011208899107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30951503326090674139266071 46427254989136011208899107)
          ·
            refine ⟨69640882483704016813348661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46427254989136011208899107 69640882483704016813348661)
            ·
              refine ⟨6528832732847251576251437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69640882483704016813348661 6528832732847251576251437)
              ·
                refine ⟨2448312274817719341094289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6528832732847251576251437 2448312274817719341094289)
                ·
                  refine ⟨1836234206113289505820717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2448312274817719341094289 1836234206113289505820717)
                  ·
                    refine ⟨688587827292483564682769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1836234206113289505820717 688587827292483564682769)
                    ·
                      refine ⟨516440870469362673512077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688587827292483564682769 516440870469362673512077)
                      ·
                        rfl

theorem cell23_1005765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_1005765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005765 prefixEnd_1005765 := by exact prefixLift 1005765
  have htrace : WordTrace (prefixWord ++ tailWord_1005765) baseStart_1005765 baseEnd_1005765 := by
    simpa [prefixWord, tailWord_1005765, baseEnd_1005765] using wordTrace_append hprefix tailTrace_1005765
  have hstable : (prefixWord ++ tailWord_1005765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005765).length < 2 ^ (prefixWord ++ tailWord_1005765).sum := by decide
  have hdescent : baseEnd_1005765 < baseStart_1005765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005775 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 1, 5]
def baseStart_1005775 : Nat := 118140960795 + 1005775 * 2 ^ 59
def prefixEnd_1005775 : Nat := 4983230072969 + 3 ^ 40 * 1005775 * 2
def baseEnd_1005775 : Nat := 172148668425302544795677

theorem tailTrace_1005775 : CollatzResearch.WordTrace tailWord_1005775 prefixEnd_1005775 172148668425302544795677 := by
  unfold tailWord_1005775
  simp only [CollatzResearch.WordTrace]
  refine ⟨36683627931256422539586779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24455751954170948359724519 36683627931256422539586779)
  ·
    refine ⟨55025441896884633809380169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36683627931256422539586779 55025441896884633809380169)
    ·
      refine ⟨41269081422663475357035127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55025441896884633809380169 41269081422663475357035127)
      ·
        refine ⟨61903622133995213035552691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41269081422663475357035127 61903622133995213035552691)
        ·
          refine ⟨92855433200992819553329037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61903622133995213035552691 92855433200992819553329037)
          ·
            refine ⟨34820787450372307332498389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92855433200992819553329037 34820787450372307332498389)
            ·
              refine ⟨816112205868100953105431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34820787450372307332498389 816112205868100953105431)
              ·
                refine ⟨1224168308802151429658147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816112205868100953105431 1224168308802151429658147)
                ·
                  refine ⟨1836252463203227144487221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224168308802151429658147 1836252463203227144487221)
                  ·
                    refine ⟨172148668425302544795677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1836252463203227144487221 172148668425302544795677)
                    ·
                      rfl

theorem cell23_1005775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 5].length) (baseStart_1005775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005775 prefixEnd_1005775 := by exact prefixLift 1005775
  have htrace : WordTrace (prefixWord ++ tailWord_1005775) baseStart_1005775 baseEnd_1005775 := by
    simpa [prefixWord, tailWord_1005775, baseEnd_1005775] using wordTrace_append hprefix tailTrace_1005775
  have hstable : (prefixWord ++ tailWord_1005775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005775).length < 2 ^ (prefixWord ++ tailWord_1005775).sum := by decide
  have hdescent : baseEnd_1005775 < baseStart_1005775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005832 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_1005832 : Nat := 118140960795 + 1005832 * 2 ^ 59
def prefixEnd_1005832 : Nat := 4983230072969 + 3 ^ 40 * 1005832 * 2
def baseEnd_1005832 : Nat := 516475273673213911374269

theorem tailTrace_1005832 : CollatzResearch.WordTrace tailWord_1005832 prefixEnd_1005832 516475273673213911374269 := by
  unfold tailWord_1005832
  simp only [CollatzResearch.WordTrace]
  refine ⟨18342853446024960637205875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24457137928033280849607833 18342853446024960637205875)
  ·
    refine ⟨27514280169037440955808813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18342853446024960637205875 27514280169037440955808813)
    ·
      refine ⟨10317855063389040358428305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27514280169037440955808813 10317855063389040358428305)
      ·
        refine ⟨7738391297541780268821229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10317855063389040358428305 7738391297541780268821229)
        ·
          refine ⟨2901896736578167600807961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7738391297541780268821229 2901896736578167600807961)
          ·
            refine ⟨2176422552433625700605971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901896736578167600807961 2176422552433625700605971)
            ·
              refine ⟨3264633828650438550908957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176422552433625700605971 3264633828650438550908957)
              ·
                refine ⟨1224237685743914456590859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3264633828650438550908957 1224237685743914456590859)
                ·
                  refine ⟨1836356528615871684886289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224237685743914456590859 1836356528615871684886289)
                  ·
                    refine ⟨1377267396461903763664717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1836356528615871684886289 1377267396461903763664717)
                    ·
                      refine ⟨516475273673213911374269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1377267396461903763664717 516475273673213911374269)
                      ·
                        rfl

theorem cell23_1005832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_1005832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005832 prefixEnd_1005832 := by exact prefixLift 1005832
  have htrace : WordTrace (prefixWord ++ tailWord_1005832) baseStart_1005832 baseEnd_1005832 := by
    simpa [prefixWord, tailWord_1005832, baseEnd_1005832] using wordTrace_append hprefix tailTrace_1005832
  have hstable : (prefixWord ++ tailWord_1005832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005832).length < 2 ^ (prefixWord ++ tailWord_1005832).sum := by decide
  have hdescent : baseEnd_1005832 < baseStart_1005832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005868 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_1005868 : Nat := 118140960795 + 1005868 * 2 ^ 59
def prefixEnd_1005868 : Nat := 4983230072969 + 3 ^ 40 * 1005868 * 2
def baseEnd_1005868 : Nat := 516493758976775770524103

theorem tailTrace_1005868 : CollatzResearch.WordTrace tailWord_1005868 prefixEnd_1005868 516493758976775770524103 := by
  unfold tailWord_1005868
  simp only [CollatzResearch.WordTrace]
  refine ⟨18343509959959749711361129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24458013279946332948481505 18343509959959749711361129)
  ·
    refine ⟨13757632469969812283520847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18343509959959749711361129 13757632469969812283520847)
    ·
      refine ⟨20636448704954718425281271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13757632469969812283520847 20636448704954718425281271)
      ·
        refine ⟨30954673057432077637921907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20636448704954718425281271 30954673057432077637921907)
        ·
          refine ⟨46432009586148116456882861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30954673057432077637921907 46432009586148116456882861)
          ·
            refine ⟨17412003594805543671331073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46432009586148116456882861 17412003594805543671331073)
            ·
              refine ⟨13059002696104157753498305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17412003594805543671331073 13059002696104157753498305)
              ·
                refine ⟨9794252022078118315123729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13059002696104157753498305 9794252022078118315123729)
                ·
                  refine ⟨7345689016558588736342797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794252022078118315123729 7345689016558588736342797)
                  ·
                    refine ⟨2754633381209470776128549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7345689016558588736342797 2754633381209470776128549)
                    ·
                      refine ⟨516493758976775770524103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2754633381209470776128549 516493758976775770524103)
                      ·
                        rfl

theorem cell23_1005868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_1005868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005868 prefixEnd_1005868 := by exact prefixLift 1005868
  have htrace : WordTrace (prefixWord ++ tailWord_1005868) baseStart_1005868 baseEnd_1005868 := by
    simpa [prefixWord, tailWord_1005868, baseEnd_1005868] using wordTrace_append hprefix tailTrace_1005868
  have hstable : (prefixWord ++ tailWord_1005868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005868).length < 2 ^ (prefixWord ++ tailWord_1005868).sum := by decide
  have hdescent : baseEnd_1005868 < baseStart_1005868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005869 : List Nat := [1, 5, 3, 1, 2, 2, 2, 7]
def baseStart_1005869 : Nat := 118140960795 + 1005869 * 2 ^ 59
def prefixEnd_1005869 : Nat := 4983230072969 + 3 ^ 40 * 1005869 * 2
def baseEnd_1005869 : Nat := 19129417498423343207837

theorem tailTrace_1005869 : CollatzResearch.WordTrace tailWord_1005869 prefixEnd_1005869 19129417498423343207837 := by
  unfold tailWord_1005869
  simp only [CollatzResearch.WordTrace]
  refine ⟨36687056392915876593508661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24458037595277251062339107 36687056392915876593508661)
  ·
    refine ⟨3439411536835863430641437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36687056392915876593508661 3439411536835863430641437)
    ·
      refine ⟨1289779326313448786490539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3439411536835863430641437 1289779326313448786490539)
      ·
        refine ⟨1934668989470173179735809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289779326313448786490539 1934668989470173179735809)
        ·
          refine ⟨1451001742102629884801857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934668989470173179735809 1451001742102629884801857)
          ·
            refine ⟨1088251306576972413601393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451001742102629884801857 1088251306576972413601393)
            ·
              refine ⟨816188479932729310201045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088251306576972413601393 816188479932729310201045)
              ·
                refine ⟨19129417498423343207837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 816188479932729310201045 19129417498423343207837)
                ·
                  rfl

theorem cell23_1005869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 7].length) (baseStart_1005869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005869 prefixEnd_1005869 := by exact prefixLift 1005869
  have htrace : WordTrace (prefixWord ++ tailWord_1005869) baseStart_1005869 baseEnd_1005869 := by
    simpa [prefixWord, tailWord_1005869, baseEnd_1005869] using wordTrace_append hprefix tailTrace_1005869
  have hstable : (prefixWord ++ tailWord_1005869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005869).length < 2 ^ (prefixWord ++ tailWord_1005869).sum := by decide
  have hdescent : baseEnd_1005869 < baseStart_1005869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005975 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1005975 : Nat := 118140960795 + 1005975 * 2 ^ 59
def prefixEnd_1005975 : Nat := 4983230072969 + 3 ^ 40 * 1005975 * 2
def baseEnd_1005975 : Nat := 516548701406806851886111

theorem tailTrace_1005975 : CollatzResearch.WordTrace tailWord_1005975 prefixEnd_1005975 516548701406806851886111 := by
  unfold tailWord_1005975
  simp only [CollatzResearch.WordTrace]
  refine ⟨36690922530531856696867379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24460615020354571131244919 36690922530531856696867379)
  ·
    refine ⟨55036383795797785045301069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36690922530531856696867379 55036383795797785045301069)
    ·
      refine ⟨20638643923424169391987901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55036383795797785045301069 20638643923424169391987901)
      ·
        refine ⟨7739491471284063521995463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20638643923424169391987901 7739491471284063521995463)
        ·
          refine ⟨11609237206926095282993195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7739491471284063521995463 11609237206926095282993195)
          ·
            refine ⟨17413855810389142924489793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11609237206926095282993195 17413855810389142924489793)
            ·
              refine ⟨13060391857791857193367345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17413855810389142924489793 13060391857791857193367345)
              ·
                refine ⟨9795293893343892895025509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13060391857791857193367345 9795293893343892895025509)
                ·
                  refine ⟨1836617605001979917817283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9795293893343892895025509 1836617605001979917817283)
                  ·
                    refine ⟨2754926407502969876725925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1836617605001979917817283 2754926407502969876725925)
                    ·
                      refine ⟨516548701406806851886111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2754926407502969876725925 516548701406806851886111)
                      ·
                        rfl

theorem cell23_1005975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1005975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005975 prefixEnd_1005975 := by exact prefixLift 1005975
  have htrace : WordTrace (prefixWord ++ tailWord_1005975) baseStart_1005975 baseEnd_1005975 := by
    simpa [prefixWord, tailWord_1005975, baseEnd_1005975] using wordTrace_append hprefix tailTrace_1005975
  have hstable : (prefixWord ++ tailWord_1005975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005975).length < 2 ^ (prefixWord ++ tailWord_1005975).sum := by decide
  have hdescent : baseEnd_1005975 < baseStart_1005975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006053 : List Nat := [1, 3, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_1006053 : Nat := 118140960795 + 1006053 * 2 ^ 59
def prefixEnd_1006053 : Nat := 4983230072969 + 3 ^ 40 * 1006053 * 2
def baseEnd_1006053 : Nat := 172196250965952515570251

theorem tailTrace_1006053 : CollatzResearch.WordTrace tailWord_1006053 prefixEnd_1006053 172196250965952515570251 := by
  unfold tailWord_1006053
  simp only [CollatzResearch.WordTrace]
  refine ⟨36693767424249276018206813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24462511616166184012137875 36693767424249276018206813)
  ·
    refine ⟨13760162784093478506827555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36693767424249276018206813 13760162784093478506827555)
    ·
      refine ⟨20640244176140217760241333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13760162784093478506827555 20640244176140217760241333)
      ·
        refine ⟨1935022891513145415022625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20640244176140217760241333 1935022891513145415022625)
        ·
          refine ⟨1451267168634859061266969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1935022891513145415022625 1451267168634859061266969)
          ·
            refine ⟨1088450376476144295950227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451267168634859061266969 1088450376476144295950227)
            ·
              refine ⟨1632675564714216443925341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088450376476144295950227 1632675564714216443925341)
              ·
                refine ⟨612253336767831166472003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1632675564714216443925341 612253336767831166472003)
                ·
                  refine ⟨918380005151746749708005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612253336767831166472003 918380005151746749708005)
                  ·
                    refine ⟨172196250965952515570251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 918380005151746749708005 172196250965952515570251)
                    ·
                      rfl

theorem cell23_1006053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_1006053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006053 prefixEnd_1006053 := by exact prefixLift 1006053
  have htrace : WordTrace (prefixWord ++ tailWord_1006053) baseStart_1006053 baseEnd_1006053 := by
    simpa [prefixWord, tailWord_1006053, baseEnd_1006053] using wordTrace_append hprefix tailTrace_1006053
  have hstable : (prefixWord ++ tailWord_1006053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006053).length < 2 ^ (prefixWord ++ tailWord_1006053).sum := by decide
  have hdescent : baseEnd_1006053 < baseStart_1006053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006099 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 5, 2, 2]
def baseStart_1006099 : Nat := 118140960795 + 1006099 * 2 ^ 59
def prefixEnd_1006099 : Nat := 4983230072969 + 3 ^ 40 * 1006099 * 2
def baseEnd_1006099 : Nat := 516612373007964366735541

theorem tailTrace_1006099 : CollatzResearch.WordTrace tailWord_1006099 prefixEnd_1006099 516612373007964366735541 := by
  unfold tailWord_1006099
  simp only [CollatzResearch.WordTrace]
  refine ⟨36695445182082625874381351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24463630121388417249587567 36695445182082625874381351)
  ·
    refine ⟨55043167773123938811572027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36695445182082625874381351 55043167773123938811572027)
    ·
      refine ⟨82564751659685908217358041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55043167773123938811572027 82564751659685908217358041)
      ·
        refine ⟨61923563744764431163018531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82564751659685908217358041 61923563744764431163018531)
        ·
          refine ⟨92885345617146646744527797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61923563744764431163018531 92885345617146646744527797)
          ·
            refine ⟨8708001151607498132299481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92885345617146646744527797 8708001151607498132299481)
            ·
              refine ⟨6531000863705623599224611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8708001151607498132299481 6531000863705623599224611)
              ·
                refine ⟨9796501295558435398836917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6531000863705623599224611 9796501295558435398836917)
                ·
                  refine ⟨918421996458603318640961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9796501295558435398836917 918421996458603318640961)
                  ·
                    refine ⟨688816497343952488980721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 918421996458603318640961 688816497343952488980721)
                    ·
                      refine ⟨516612373007964366735541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688816497343952488980721 516612373007964366735541)
                      ·
                        rfl

theorem cell23_1006099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 2, 2].length) (baseStart_1006099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006099 prefixEnd_1006099 := by exact prefixLift 1006099
  have htrace : WordTrace (prefixWord ++ tailWord_1006099) baseStart_1006099 baseEnd_1006099 := by
    simpa [prefixWord, tailWord_1006099, baseEnd_1006099] using wordTrace_append hprefix tailTrace_1006099
  have hstable : (prefixWord ++ tailWord_1006099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006099).length < 2 ^ (prefixWord ++ tailWord_1006099).sum := by decide
  have hdescent : baseEnd_1006099 < baseStart_1006099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006103 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1006103 : Nat := 118140960795 + 1006103 * 2 ^ 59
def prefixEnd_1006103 : Nat := 4983230072969 + 3 ^ 40 * 1006103 * 2
def baseEnd_1006103 : Nat := 516614426930582351085523

theorem tailTrace_1006103 : CollatzResearch.WordTrace tailWord_1006103 prefixEnd_1006103 516614426930582351085523 := by
  unfold tailWord_1006103
  simp only [CollatzResearch.WordTrace]
  refine ⟨36695591074068134557526963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24463727382712089705017975 36695591074068134557526963)
  ·
    refine ⟨55043386611102201836290445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36695591074068134557526963 55043386611102201836290445)
    ·
      refine ⟨20641269979163325688608917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55043386611102201836290445 20641269979163325688608917)
      ·
        refine ⟨967559530273280891653543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20641269979163325688608917 967559530273280891653543)
        ·
          refine ⟨1451339295409921337480315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967559530273280891653543 1451339295409921337480315)
          ·
            refine ⟨2177008943114882006220473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451339295409921337480315 2177008943114882006220473)
            ·
              refine ⟨1632756707336161504665355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2177008943114882006220473 1632756707336161504665355)
              ·
                refine ⟨2449135061004242256998033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632756707336161504665355 2449135061004242256998033)
                ·
                  refine ⟨1836851295753181692748525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2449135061004242256998033 1836851295753181692748525)
                  ·
                    refine ⟨688819235907443134780697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1836851295753181692748525 688819235907443134780697)
                    ·
                      refine ⟨516614426930582351085523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688819235907443134780697 516614426930582351085523)
                      ·
                        rfl

theorem cell23_1006103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1006103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006103 prefixEnd_1006103 := by exact prefixLift 1006103
  have htrace : WordTrace (prefixWord ++ tailWord_1006103) baseStart_1006103 baseEnd_1006103 := by
    simpa [prefixWord, tailWord_1006103, baseEnd_1006103] using wordTrace_append hprefix tailTrace_1006103
  have hstable : (prefixWord ++ tailWord_1006103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006103).length < 2 ^ (prefixWord ++ tailWord_1006103).sum := by decide
  have hdescent : baseEnd_1006103 < baseStart_1006103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006133 : List Nat := [1, 3, 3, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_1006133 : Nat := 118140960795 + 1006133 * 2 ^ 59
def prefixEnd_1006133 : Nat := 4983230072969 + 3 ^ 40 * 1006133 * 2
def baseEnd_1006133 : Nat := 516629831350217233710385

theorem tailTrace_1006133 : CollatzResearch.WordTrace tailWord_1006133 prefixEnd_1006133 516629831350217233710385 := by
  unfold tailWord_1006133
  simp only [CollatzResearch.WordTrace]
  refine ⟨36696685263959449681119053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24464456842639633120746035 36696685263959449681119053)
  ·
    refine ⟨13761256973984793630419645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36696685263959449681119053 13761256973984793630419645)
    ·
      refine ⟨5160471365244297611407367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13761256973984793630419645 5160471365244297611407367)
      ·
        refine ⟨7740707047866446417111051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5160471365244297611407367 7740707047866446417111051)
        ·
          refine ⟨11611060571799669625666577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7740707047866446417111051 11611060571799669625666577)
          ·
            refine ⟨8708295428849752219249933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11611060571799669625666577 8708295428849752219249933)
            ·
              refine ⟨3265610785818657082218725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8708295428849752219249933 3265610785818657082218725)
              ·
                refine ⟨612302022340998202916011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3265610785818657082218725 612302022340998202916011)
                ·
                  refine ⟨918453033511497304374017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612302022340998202916011 918453033511497304374017)
                  ·
                    refine ⟨688839775133622978280513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 918453033511497304374017 688839775133622978280513)
                    ·
                      refine ⟨516629831350217233710385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688839775133622978280513 516629831350217233710385)
                      ·
                        rfl

theorem cell23_1006133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_1006133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006133 prefixEnd_1006133 := by exact prefixLift 1006133
  have htrace : WordTrace (prefixWord ++ tailWord_1006133) baseStart_1006133 baseEnd_1006133 := by
    simpa [prefixWord, tailWord_1006133, baseEnd_1006133] using wordTrace_append hprefix tailTrace_1006133
  have hstable : (prefixWord ++ tailWord_1006133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006133).length < 2 ^ (prefixWord ++ tailWord_1006133).sum := by decide
  have hdescent : baseEnd_1006133 < baseStart_1006133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006135 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 1, 9]
def baseStart_1006135 : Nat := 118140960795 + 1006135 * 2 ^ 59
def prefixEnd_1006135 : Nat := 4983230072969 + 3 ^ 40 * 1006135 * 2
def baseEnd_1006135 : Nat := 172210286103842075295125

theorem tailTrace_1006135 : CollatzResearch.WordTrace tailWord_1006135 prefixEnd_1006135 172210286103842075295125 := by
  unfold tailWord_1006135
  simp only [CollatzResearch.WordTrace]
  refine ⟨36696758209952204022691859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24464505473301469348461239 36696758209952204022691859)
  ·
    refine ⟨55045137314928306034037789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36696758209952204022691859 55045137314928306034037789)
    ·
      refine ⟨20641926493098114762764171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55045137314928306034037789 20641926493098114762764171)
      ·
        refine ⟨30962889739647172144146257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20641926493098114762764171 30962889739647172144146257)
        ·
          refine ⟨23222167304735379108109693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30962889739647172144146257 23222167304735379108109693)
          ·
            refine ⟨8708312739275767165541135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23222167304735379108109693 8708312739275767165541135)
            ·
              refine ⟨13062469108913650748311703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708312739275767165541135 13062469108913650748311703)
              ·
                refine ⟨19593703663370476122467555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13062469108913650748311703 19593703663370476122467555)
                ·
                  refine ⟨29390555495055714183701333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19593703663370476122467555 29390555495055714183701333)
                  ·
                    refine ⟨172210286103842075295125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 29390555495055714183701333 172210286103842075295125)
                    ·
                      rfl

theorem cell23_1006135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_1006135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006135 prefixEnd_1006135 := by exact prefixLift 1006135
  have htrace : WordTrace (prefixWord ++ tailWord_1006135) baseStart_1006135 baseEnd_1006135 := by
    simpa [prefixWord, tailWord_1006135, baseEnd_1006135] using wordTrace_append hprefix tailTrace_1006135
  have hstable : (prefixWord ++ tailWord_1006135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006135).length < 2 ^ (prefixWord ++ tailWord_1006135).sum := by decide
  have hdescent : baseEnd_1006135 < baseStart_1006135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006149 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_1006149 : Nat := 118140960795 + 1006149 * 2 ^ 59
def prefixEnd_1006149 : Nat := 4983230072969 + 3 ^ 40 * 1006149 * 2
def baseEnd_1006149 : Nat := 516638047040689171110311

theorem tailTrace_1006149 : CollatzResearch.WordTrace tailWord_1006149 prefixEnd_1006149 516638047040689171110311 := by
  unfold tailWord_1006149
  simp only [CollatzResearch.WordTrace]
  refine ⟨36697268831901484413701501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24464845887934322942467667 36697268831901484413701501)
  ·
    refine ⟨13761475811963056655138063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36697268831901484413701501 13761475811963056655138063)
    ·
      refine ⟨20642213717944584982707095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13761475811963056655138063 20642213717944584982707095)
      ·
        refine ⟨30963320576916877474060643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20642213717944584982707095 30963320576916877474060643)
        ·
          refine ⟨46444980865375316211090965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30963320576916877474060643 46444980865375316211090965)
          ·
            refine ⟨2177108478064467947394889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46444980865375316211090965 2177108478064467947394889)
            ·
              refine ⟨1632831358548350960546167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2177108478064467947394889 1632831358548350960546167)
              ·
                refine ⟨2449247037822526440819251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632831358548350960546167 2449247037822526440819251)
                ·
                  refine ⟨3673870556733789661228877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449247037822526440819251 3673870556733789661228877)
                  ·
                    refine ⟨1377701458775171122960829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3673870556733789661228877 1377701458775171122960829)
                    ·
                      refine ⟨516638047040689171110311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1377701458775171122960829 516638047040689171110311)
                      ·
                        rfl

theorem cell23_1006149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_1006149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006149 prefixEnd_1006149 := by exact prefixLift 1006149
  have htrace : WordTrace (prefixWord ++ tailWord_1006149) baseStart_1006149 baseEnd_1006149 := by
    simpa [prefixWord, tailWord_1006149, baseEnd_1006149] using wordTrace_append hprefix tailTrace_1006149
  have hstable : (prefixWord ++ tailWord_1006149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006149).length < 2 ^ (prefixWord ++ tailWord_1006149).sum := by decide
  have hdescent : baseEnd_1006149 < baseStart_1006149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006150 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_1006150 : Nat := 118140960795 + 1006150 * 2 ^ 59
def prefixEnd_1006150 : Nat := 4983230072969 + 3 ^ 40 * 1006150 * 2
def baseEnd_1006150 : Nat := 516638560521343667197807

theorem tailTrace_1006150 : CollatzResearch.WordTrace tailWord_1006150 prefixEnd_1006150 516638560521343667197807 := by
  unfold tailWord_1006150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146790790778058174515247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24464870203265241056325269 1146790790778058174515247)
  ·
    refine ⟨1720186186167087261772871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146790790778058174515247 1720186186167087261772871)
    ·
      refine ⟨2580279279250630892659307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1720186186167087261772871 2580279279250630892659307)
      ·
        refine ⟨3870418918875946338988961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580279279250630892659307 3870418918875946338988961)
        ·
          refine ⟨2902814189156959754241721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3870418918875946338988961 2902814189156959754241721)
          ·
            refine ⟨2177110641867719815681291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2902814189156959754241721 2177110641867719815681291)
            ·
              refine ⟨3265665962801579723521937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177110641867719815681291 3265665962801579723521937)
              ·
                refine ⟨2449249472101184792641453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3265665962801579723521937 2449249472101184792641453)
                ·
                  refine ⟨918468552037944297240545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2449249472101184792641453 918468552037944297240545)
                  ·
                    refine ⟨688851414028458222930409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 918468552037944297240545 688851414028458222930409)
                    ·
                      refine ⟨516638560521343667197807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688851414028458222930409 516638560521343667197807)
                      ·
                        rfl

theorem cell23_1006150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_1006150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006150 prefixEnd_1006150 := by exact prefixLift 1006150
  have htrace : WordTrace (prefixWord ++ tailWord_1006150) baseStart_1006150 baseEnd_1006150 := by
    simpa [prefixWord, tailWord_1006150, baseEnd_1006150] using wordTrace_append hprefix tailTrace_1006150
  have hstable : (prefixWord ++ tailWord_1006150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006150).length < 2 ^ (prefixWord ++ tailWord_1006150).sum := by decide
  have hdescent : baseEnd_1006150 < baseStart_1006150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006159 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 3, 3, 2]
def baseStart_1006159 : Nat := 118140960795 + 1006159 * 2 ^ 59
def prefixEnd_1006159 : Nat := 4983230072969 + 3 ^ 40 * 1006159 * 2
def baseEnd_1006159 : Nat := 516643181847234131985265

theorem tailTrace_1006159 : CollatzResearch.WordTrace tailWord_1006159 prefixEnd_1006159 516643181847234131985265 := by
  unfold tailWord_1006159
  simp only [CollatzResearch.WordTrace]
  refine ⟨36697633561865256121565531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24465089041243504081043687 36697633561865256121565531)
  ·
    refine ⟨55046450342797884182348297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36697633561865256121565531 55046450342797884182348297)
    ·
      refine ⟨41284837757098413136761223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55046450342797884182348297 41284837757098413136761223)
      ·
        refine ⟨61927256635647619705141835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41284837757098413136761223 61927256635647619705141835)
        ·
          refine ⟨92890884953471429557712753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61927256635647619705141835 92890884953471429557712753)
          ·
            refine ⟨69668163715103572168284565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92890884953471429557712753 69668163715103572168284565)
            ·
              refine ⟨3265695174145479945388339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69668163715103572168284565 3265695174145479945388339)
              ·
                refine ⟨4898542761218219918082509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265695174145479945388339 4898542761218219918082509)
                ·
                  refine ⟨1836953535456832469280941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4898542761218219918082509 1836953535456832469280941)
                  ·
                    refine ⟨688857575796312175980353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1836953535456832469280941 688857575796312175980353)
                    ·
                      refine ⟨516643181847234131985265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688857575796312175980353 516643181847234131985265)
                      ·
                        rfl

theorem cell23_1006159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 3, 2].length) (baseStart_1006159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006159 prefixEnd_1006159 := by exact prefixLift 1006159
  have htrace : WordTrace (prefixWord ++ tailWord_1006159) baseStart_1006159 baseEnd_1006159 := by
    simpa [prefixWord, tailWord_1006159, baseEnd_1006159] using wordTrace_append hprefix tailTrace_1006159
  have hstable : (prefixWord ++ tailWord_1006159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006159).length < 2 ^ (prefixWord ++ tailWord_1006159).sum := by decide
  have hdescent : baseEnd_1006159 < baseStart_1006159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006162 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1006162 : Nat := 118140960795 + 1006162 * 2 ^ 59
def prefixEnd_1006162 : Nat := 4983230072969 + 3 ^ 40 * 1006162 * 2
def baseEnd_1006162 : Nat := 516644722289197620247751

theorem tailTrace_1006162 : CollatzResearch.WordTrace tailWord_1006162 prefixEnd_1006162 516644722289197620247751 := by
  unfold tailWord_1006162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174435745213596908481185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24465161987236258422616493 9174435745213596908481185)
  ·
    refine ⟨6880826808910197681360889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9174435745213596908481185 6880826808910197681360889)
    ·
      refine ⟨5160620106682648261020667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6880826808910197681360889 5160620106682648261020667)
      ·
        refine ⟨7740930160023972391531001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5160620106682648261020667 7740930160023972391531001)
        ·
          refine ⟨5805697620017979293648251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7740930160023972391531001 5805697620017979293648251)
          ·
            refine ⟨8708546430026968940472377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805697620017979293648251 8708546430026968940472377)
            ·
              refine ⟨6531409822520226705354283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8708546430026968940472377 6531409822520226705354283)
              ·
                refine ⟨9797114733780340058031425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6531409822520226705354283 9797114733780340058031425)
                ·
                  refine ⟨7347836050335255043523569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9797114733780340058031425 7347836050335255043523569)
                  ·
                    refine ⟨5510877037751441282642677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7347836050335255043523569 5510877037751441282642677)
                    ·
                      refine ⟨516644722289197620247751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5510877037751441282642677 516644722289197620247751)
                      ·
                        rfl

theorem cell23_1006162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1006162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006162 prefixEnd_1006162 := by exact prefixLift 1006162
  have htrace : WordTrace (prefixWord ++ tailWord_1006162) baseStart_1006162 baseEnd_1006162 := by
    simpa [prefixWord, tailWord_1006162, baseEnd_1006162] using wordTrace_append hprefix tailTrace_1006162
  have hstable : (prefixWord ++ tailWord_1006162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006162).length < 2 ^ (prefixWord ++ tailWord_1006162).sum := by decide
  have hdescent : baseEnd_1006162 < baseStart_1006162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006276 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1006276 : Nat := 118140960795 + 1006276 * 2 ^ 59
def prefixEnd_1006276 : Nat := 4983230072969 + 3 ^ 40 * 1006276 * 2
def baseEnd_1006276 : Nat := 172234419694603391407409

theorem tailTrace_1006276 : CollatzResearch.WordTrace tailWord_1006276 prefixEnd_1006276 172234419694603391407409 := by
  unfold tailWord_1006276
  simp only [CollatzResearch.WordTrace]
  refine ⟨18350950451220692551787341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24467933934960923402383121 18350950451220692551787341)
  ·
    refine ⟨6881606419207759706920253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18350950451220692551787341 6881606419207759706920253)
    ·
      refine ⟨2580602407202909890095095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6881606419207759706920253 2580602407202909890095095)
      ·
        refine ⟨3870903610804364835142643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580602407202909890095095 3870903610804364835142643)
        ·
          refine ⟨5806355416206547252713965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870903610804364835142643 5806355416206547252713965)
          ·
            refine ⟨2177383281077455219767737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5806355416206547252713965 2177383281077455219767737)
            ·
              refine ⟨1633037460808091414825803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2177383281077455219767737 1633037460808091414825803)
              ·
                refine ⟨2449556191212137122238705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633037460808091414825803 2449556191212137122238705)
                ·
                  refine ⟨1837167143409102841679029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2449556191212137122238705 1837167143409102841679029)
                  ·
                    refine ⟨172234419694603391407409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1837167143409102841679029 172234419694603391407409)
                    ·
                      rfl

theorem cell23_1006276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1006276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006276 prefixEnd_1006276 := by exact prefixLift 1006276
  have htrace : WordTrace (prefixWord ++ tailWord_1006276) baseStart_1006276 baseEnd_1006276 := by
    simpa [prefixWord, tailWord_1006276, baseEnd_1006276] using wordTrace_append hprefix tailTrace_1006276
  have hstable : (prefixWord ++ tailWord_1006276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006276).length < 2 ^ (prefixWord ++ tailWord_1006276).sum := by decide
  have hdescent : baseEnd_1006276 < baseStart_1006276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006279 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_1006279 : Nat := 118140960795 + 1006279 * 2 ^ 59
def prefixEnd_1006279 : Nat := 4983230072969 + 3 ^ 40 * 1006279 * 2
def baseEnd_1006279 : Nat := 516704799525773662484713

theorem tailTrace_1006279 : CollatzResearch.WordTrace tailWord_1006279 prefixEnd_1006279 516704799525773662484713 := by
  unfold tailWord_1006279
  simp only [CollatzResearch.WordTrace]
  refine ⟨36702010321430516615933891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24468006880953677743955927 36702010321430516615933891)
  ·
    refine ⟨55053015482145774923900837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36702010321430516615933891 55053015482145774923900837)
    ·
      refine ⟨10322440402902332798231407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55053015482145774923900837 10322440402902332798231407)
      ·
        refine ⟨15483660604353499197347111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10322440402902332798231407 15483660604353499197347111)
        ·
          refine ⟨23225490906530248796020667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15483660604353499197347111 23225490906530248796020667)
          ·
            refine ⟨34838236359795373194031001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23225490906530248796020667 34838236359795373194031001)
            ·
              refine ⟨26128677269846529895523251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34838236359795373194031001 26128677269846529895523251)
              ·
                refine ⟨39193015904769794843284877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26128677269846529895523251 39193015904769794843284877)
                ·
                  refine ⟨14697380964288673066231829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39193015904769794843284877 14697380964288673066231829)
                  ·
                    refine ⟨688939732701031549979617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14697380964288673066231829 688939732701031549979617)
                    ·
                      refine ⟨516704799525773662484713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688939732701031549979617 516704799525773662484713)
                      ·
                        rfl

theorem cell23_1006279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_1006279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006279 prefixEnd_1006279 := by exact prefixLift 1006279
  have htrace : WordTrace (prefixWord ++ tailWord_1006279) baseStart_1006279 baseEnd_1006279 := by
    simpa [prefixWord, tailWord_1006279, baseEnd_1006279] using wordTrace_append hprefix tailTrace_1006279
  have hstable : (prefixWord ++ tailWord_1006279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006279).length < 2 ^ (prefixWord ++ tailWord_1006279).sum := by decide
  have hdescent : baseEnd_1006279 < baseStart_1006279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006319 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 6]
def baseStart_1006319 : Nat := 118140960795 + 1006319 * 2 ^ 59
def prefixEnd_1006319 : Nat := 4983230072969 + 3 ^ 40 * 1006319 * 2
def baseEnd_1006319 : Nat := 57413926527994833998281

theorem tailTrace_1006319 : CollatzResearch.WordTrace tailWord_1006319 prefixEnd_1006319 57413926527994833998281 := by
  unfold tailWord_1006319
  simp only [CollatzResearch.WordTrace]
  refine ⟨36703469241285603447390011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24468979494190402298260007 36703469241285603447390011)
  ·
    refine ⟨55055203861928405171085017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36703469241285603447390011 55055203861928405171085017)
    ·
      refine ⟨41291402896446303878313763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55055203861928405171085017 41291402896446303878313763)
      ·
        refine ⟨61937104344669455817470645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41291402896446303878313763 61937104344669455817470645)
        ·
          refine ⟨5806603532312761482887873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61937104344669455817470645 5806603532312761482887873)
          ·
            refine ⟨4354952649234571112165905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5806603532312761482887873 4354952649234571112165905)
            ·
              refine ⟨3266214486925928334124429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4354952649234571112165905 3266214486925928334124429)
              ·
                refine ⟨1224830432597223125296661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3266214486925928334124429 1224830432597223125296661)
                ·
                  refine ⟨57413926527994833998281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1224830432597223125296661 57413926527994833998281)
                  ·
                    rfl

theorem cell23_1006319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 6].length) (baseStart_1006319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006319 prefixEnd_1006319 := by exact prefixLift 1006319
  have htrace : WordTrace (prefixWord ++ tailWord_1006319) baseStart_1006319 baseEnd_1006319 := by
    simpa [prefixWord, tailWord_1006319, baseEnd_1006319] using wordTrace_append hprefix tailTrace_1006319
  have hstable : (prefixWord ++ tailWord_1006319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006319).length < 2 ^ (prefixWord ++ tailWord_1006319).sum := by decide
  have hdescent : baseEnd_1006319 < baseStart_1006319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006346 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1006346 : Nat := 118140960795 + 1006346 * 2 ^ 59
def prefixEnd_1006346 : Nat := 4983230072969 + 3 ^ 40 * 1006346 * 2
def baseEnd_1006346 : Nat := 516739202729624900346905

theorem tailTrace_1006346 : CollatzResearch.WordTrace tailWord_1006346 prefixEnd_1006346 516739202729624900346905 := by
  unfold tailWord_1006346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176113503046946764655723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24469636008125191372415261 9176113503046946764655723)
  ·
    refine ⟨13764170254570420146983585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9176113503046946764655723 13764170254570420146983585)
    ·
      refine ⟨10323127690927815110237689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13764170254570420146983585 10323127690927815110237689)
      ·
        refine ⟨7742345768195861332678267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10323127690927815110237689 7742345768195861332678267)
        ·
          refine ⟨11613518652293791999017401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742345768195861332678267 11613518652293791999017401)
          ·
            refine ⟨8710138989220343999263051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11613518652293791999017401 8710138989220343999263051)
            ·
              refine ⟨13065208483830515998894577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710138989220343999263051 13065208483830515998894577)
              ·
                refine ⟨9798906362872886999170933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13065208483830515998894577 9798906362872886999170933)
                ·
                  refine ⟨918647471519333156172275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9798906362872886999170933 918647471519333156172275)
                  ·
                    refine ⟨1377971207278999734258413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 918647471519333156172275 1377971207278999734258413)
                    ·
                      refine ⟨516739202729624900346905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1377971207278999734258413 516739202729624900346905)
                      ·
                        rfl

theorem cell23_1006346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1006346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006346 prefixEnd_1006346 := by exact prefixLift 1006346
  have htrace : WordTrace (prefixWord ++ tailWord_1006346) baseStart_1006346 baseEnd_1006346 := by
    simpa [prefixWord, tailWord_1006346, baseEnd_1006346] using wordTrace_append hprefix tailTrace_1006346
  have hstable : (prefixWord ++ tailWord_1006346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006346).length < 2 ^ (prefixWord ++ tailWord_1006346).sum := by decide
  have hdescent : baseEnd_1006346 < baseStart_1006346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006379 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 6, 4]
def baseStart_1006379 : Nat := 118140960795 + 1006379 * 2 ^ 59
def prefixEnd_1006379 : Nat := 4983230072969 + 3 ^ 40 * 1006379 * 2
def baseEnd_1006379 : Nat := 172252049197074423744751

theorem tailTrace_1006379 : CollatzResearch.WordTrace tailWord_1006379 prefixEnd_1006379 172252049197074423744751 := by
  unfold tailWord_1006379
  simp only [CollatzResearch.WordTrace]
  refine ⟨36705657621068233694574191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24470438414045489129716127 36705657621068233694574191)
  ·
    refine ⟨55058486431602350541861287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36705657621068233694574191 55058486431602350541861287)
    ·
      refine ⟨82587729647403525812791931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55058486431602350541861287 82587729647403525812791931)
      ·
        refine ⟨123881594471105288719187897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82587729647403525812791931 123881594471105288719187897)
        ·
          refine ⟨92911195853328966539390923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123881594471105288719187897 92911195853328966539390923)
          ·
            refine ⟨139366793779993449809086385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92911195853328966539390923 139366793779993449809086385)
            ·
              refine ⟨104525095334995087356814789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139366793779993449809086385 104525095334995087356814789)
              ·
                refine ⟨19598455375311578879402773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104525095334995087356814789 19598455375311578879402773)
                ·
                  refine ⟨918677595717730259972005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19598455375311578879402773 918677595717730259972005)
                  ·
                    refine ⟨172252049197074423744751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 918677595717730259972005 172252049197074423744751)
                    ·
                      rfl

theorem cell23_1006379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 4].length) (baseStart_1006379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006379 prefixEnd_1006379 := by exact prefixLift 1006379
  have htrace : WordTrace (prefixWord ++ tailWord_1006379) baseStart_1006379 baseEnd_1006379 := by
    simpa [prefixWord, tailWord_1006379, baseEnd_1006379] using wordTrace_append hprefix tailTrace_1006379
  have hstable : (prefixWord ++ tailWord_1006379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006379).length < 2 ^ (prefixWord ++ tailWord_1006379).sum := by decide
  have hdescent : baseEnd_1006379 < baseStart_1006379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006386 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_1006386 : Nat := 118140960795 + 1006386 * 2 ^ 59
def prefixEnd_1006386 : Nat := 4983230072969 + 3 ^ 40 * 1006386 * 2
def baseEnd_1006386 : Nat := 516759741955804743846721

theorem tailTrace_1006386 : CollatzResearch.WordTrace tailWord_1006386 prefixEnd_1006386 516759741955804743846721 := by
  unfold tailWord_1006386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176478233010718472519753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24470608621361915926719341 9176478233010718472519753)
  ·
    refine ⟨6882358674758038854389815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9176478233010718472519753 6882358674758038854389815)
    ·
      refine ⟨10323538012137058281584723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6882358674758038854389815 10323538012137058281584723)
      ·
        refine ⟨15485307018205587422377085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10323538012137058281584723 15485307018205587422377085)
        ·
          refine ⟨5806990131827095283391407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15485307018205587422377085 5806990131827095283391407)
          ·
            refine ⟨8710485197740642925087111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806990131827095283391407 8710485197740642925087111)
            ·
              refine ⟨13065727796610964387630667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710485197740642925087111 13065727796610964387630667)
              ·
                refine ⟨19598591694916446581446001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13065727796610964387630667 19598591694916446581446001)
                ·
                  refine ⟨14698943771187334936084501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19598591694916446581446001 14698943771187334936084501)
                  ·
                    refine ⟨689012989274406325128961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14698943771187334936084501 689012989274406325128961)
                    ·
                      refine ⟨516759741955804743846721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689012989274406325128961 516759741955804743846721)
                      ·
                        rfl

theorem cell23_1006386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_1006386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006386 prefixEnd_1006386 := by exact prefixLift 1006386
  have htrace : WordTrace (prefixWord ++ tailWord_1006386) baseStart_1006386 baseEnd_1006386 := by
    simpa [prefixWord, tailWord_1006386, baseEnd_1006386] using wordTrace_append hprefix tailTrace_1006386
  have hstable : (prefixWord ++ tailWord_1006386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006386).length < 2 ^ (prefixWord ++ tailWord_1006386).sum := by decide
  have hdescent : baseEnd_1006386 < baseStart_1006386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006409 : List Nat := [1, 2, 1, 1, 2, 7, 9]
def baseStart_1006409 : Nat := 118140960795 + 1006409 * 2 ^ 59
def prefixEnd_1006409 : Nat := 4983230072969 + 3 ^ 40 * 1006409 * 2
def baseEnd_1006409 : Nat := 6379895703837754985915

theorem tailTrace_1006409 : CollatzResearch.WordTrace tailWord_1006409 prefixEnd_1006409 6379895703837754985915 := by
  unfold tailWord_1006409
  simp only [CollatzResearch.WordTrace]
  refine ⟨36706751810959548818166281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24471167873973032545444187 36706751810959548818166281)
  ·
    refine ⟨27530063858219661613624711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36706751810959548818166281 27530063858219661613624711)
    ·
      refine ⟨41295095787329492420437067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27530063858219661613624711 41295095787329492420437067)
      ·
        refine ⟨61942643680994238630655601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41295095787329492420437067 61942643680994238630655601)
        ·
          refine ⟨46456982760745678972991701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61942643680994238630655601 46456982760745678972991701)
          ·
            refine ⟨1088835533454976850929493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 46456982760745678972991701 1088835533454976850929493)
            ·
              refine ⟨6379895703837754985915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1088835533454976850929493 6379895703837754985915)
              ·
                rfl

theorem cell23_1006409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 9].length) (baseStart_1006409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006409 prefixEnd_1006409 := by exact prefixLift 1006409
  have htrace : WordTrace (prefixWord ++ tailWord_1006409) baseStart_1006409 baseEnd_1006409 := by
    simpa [prefixWord, tailWord_1006409, baseEnd_1006409] using wordTrace_append hprefix tailTrace_1006409
  have hstable : (prefixWord ++ tailWord_1006409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006409).length < 2 ^ (prefixWord ++ tailWord_1006409).sum := by decide
  have hdescent : baseEnd_1006409 < baseStart_1006409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006440 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1006440 : Nat := 118140960795 + 1006440 * 2 ^ 59
def prefixEnd_1006440 : Nat := 4983230072969 + 3 ^ 40 * 1006440 * 2
def baseEnd_1006440 : Nat := 516787469911147532571473

theorem tailTrace_1006440 : CollatzResearch.WordTrace tailWord_1006440 prefixEnd_1006440 516787469911147532571473 := by
  unfold tailWord_1006440
  simp only [CollatzResearch.WordTrace]
  refine ⟨18353941236923620556272387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24471921649231494075029849 18353941236923620556272387)
  ·
    refine ⟨27530911855385430834408581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18353941236923620556272387 27530911855385430834408581)
    ·
      refine ⟨5162045972884768281451609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27530911855385430834408581 5162045972884768281451609)
      ·
        refine ⟨3871534479663576211088707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5162045972884768281451609 3871534479663576211088707)
        ·
          refine ⟨5807301719495364316633061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871534479663576211088707 5807301719495364316633061)
          ·
            refine ⟨1088869072405380809368699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5807301719495364316633061 1088869072405380809368699)
            ·
              refine ⟨1633303608608071214053049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088869072405380809368699 1633303608608071214053049)
              ·
                refine ⟨1224977706456053410539787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633303608608071214053049 1224977706456053410539787)
                ·
                  refine ⟨1837466559684080115809681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224977706456053410539787 1837466559684080115809681)
                  ·
                    refine ⟨1378099919763060086857261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1837466559684080115809681 1378099919763060086857261)
                    ·
                      refine ⟨516787469911147532571473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1378099919763060086857261 516787469911147532571473)
                      ·
                        rfl

theorem cell23_1006440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1006440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006440 prefixEnd_1006440 := by exact prefixLift 1006440
  have htrace : WordTrace (prefixWord ++ tailWord_1006440) baseStart_1006440 baseEnd_1006440 := by
    simpa [prefixWord, tailWord_1006440, baseEnd_1006440] using wordTrace_append hprefix tailTrace_1006440
  have hstable : (prefixWord ++ tailWord_1006440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006440).length < 2 ^ (prefixWord ++ tailWord_1006440).sum := by decide
  have hdescent : baseEnd_1006440 < baseStart_1006440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006453 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1006453 : Nat := 118140960795 + 1006453 * 2 ^ 59
def prefixEnd_1006453 : Nat := 4983230072969 + 3 ^ 40 * 1006453 * 2
def baseEnd_1006453 : Nat := 516794145159655981708913

theorem tailTrace_1006453 : CollatzResearch.WordTrace tailWord_1006453 prefixEnd_1006453 516794145159655981708913 := by
  unfold tailWord_1006453
  simp only [CollatzResearch.WordTrace]
  refine ⟨36708356622800144332768013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24472237748533429555178675 36708356622800144332768013)
  ·
    refine ⟨13765633733550054124788005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36708356622800144332768013 13765633733550054124788005)
    ·
      refine ⟨2581056325040635148397751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13765633733550054124788005 2581056325040635148397751)
      ·
        refine ⟨3871584487560952722596627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581056325040635148397751 3871584487560952722596627)
        ·
          refine ⟨5807376731341429083894941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3871584487560952722596627 5807376731341429083894941)
          ·
            refine ⟨2177766274253035906460603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5807376731341429083894941 2177766274253035906460603)
            ·
              refine ⟨3266649411379553859690905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177766274253035906460603 3266649411379553859690905)
              ·
                refine ⟨2449987058534665394768179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3266649411379553859690905 2449987058534665394768179)
                ·
                  refine ⟨3674980587801998092152269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2449987058534665394768179 3674980587801998092152269)
                  ·
                    refine ⟨1378117720425749284557101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3674980587801998092152269 1378117720425749284557101)
                    ·
                      refine ⟨516794145159655981708913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1378117720425749284557101 516794145159655981708913)
                      ·
                        rfl

theorem cell23_1006453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1006453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006453 prefixEnd_1006453 := by exact prefixLift 1006453
  have htrace : WordTrace (prefixWord ++ tailWord_1006453) baseStart_1006453 baseEnd_1006453 := by
    simpa [prefixWord, tailWord_1006453, baseEnd_1006453] using wordTrace_append hprefix tailTrace_1006453
  have hstable : (prefixWord ++ tailWord_1006453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006453).length < 2 ^ (prefixWord ++ tailWord_1006453).sum := by decide
  have hdescent : baseEnd_1006453 < baseStart_1006453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006463 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 1, 3, 2]
def baseStart_1006463 : Nat := 118140960795 + 1006463 * 2 ^ 59
def prefixEnd_1006463 : Nat := 4983230072969 + 3 ^ 40 * 1006463 * 2
def baseEnd_1006463 : Nat := 516799279966200942583867

theorem tailTrace_1006463 : CollatzResearch.WordTrace tailWord_1006463 prefixEnd_1006463 516799279966200942583867 := by
  unfold tailWord_1006463
  simp only [CollatzResearch.WordTrace]
  refine ⟨36708721352763916040632043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24472480901842610693754695 36708721352763916040632043)
  ·
    refine ⟨55063082029145874060948065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36708721352763916040632043 55063082029145874060948065)
    ·
      refine ⟨41297311521859405545711049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55063082029145874060948065 41297311521859405545711049)
      ·
        refine ⟨30972983641394554159283287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41297311521859405545711049 30972983641394554159283287)
        ·
          refine ⟨46459475462091831238924931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30972983641394554159283287 46459475462091831238924931)
          ·
            refine ⟨69689213193137746858387397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46459475462091831238924931 69689213193137746858387397)
            ·
              refine ⟨13066727473713327535947637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69689213193137746858387397 13066727473713327535947637)
              ·
                refine ⟨1225005700660624456495091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13066727473713327535947637 1225005700660624456495091)
                ·
                  refine ⟨1837508550990936684742637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225005700660624456495091 1837508550990936684742637)
                  ·
                    refine ⟨689065706621601256778489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1837508550990936684742637 689065706621601256778489)
                    ·
                      refine ⟨516799279966200942583867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689065706621601256778489 516799279966200942583867)
                      ·
                        rfl

theorem cell23_1006463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_1006463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006463 prefixEnd_1006463 := by exact prefixLift 1006463
  have htrace : WordTrace (prefixWord ++ tailWord_1006463) baseStart_1006463 baseEnd_1006463 := by
    simpa [prefixWord, tailWord_1006463, baseEnd_1006463] using wordTrace_append hprefix tailTrace_1006463
  have hstable : (prefixWord ++ tailWord_1006463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006463).length < 2 ^ (prefixWord ++ tailWord_1006463).sum := by decide
  have hdescent : baseEnd_1006463 < baseStart_1006463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006499 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 9]
def baseStart_1006499 : Nat := 118140960795 + 1006499 * 2 ^ 59
def prefixEnd_1006499 : Nat := 4983230072969 + 3 ^ 40 * 1006499 * 2
def baseEnd_1006499 : Nat := 57424196141084755748189

theorem tailTrace_1006499 : CollatzResearch.WordTrace tailWord_1006499 prefixEnd_1006499 57424196141084755748189 := by
  unfold tailWord_1006499
  simp only [CollatzResearch.WordTrace]
  refine ⟨36710034380633494188942551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24473356253755662792628367 36710034380633494188942551)
  ·
    refine ⟨55065051570950241283413827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36710034380633494188942551 55065051570950241283413827)
    ·
      refine ⟨82597577356425361925120741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55065051570950241283413827 82597577356425361925120741)
      ·
        refine ⟨15487045754329755360960139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82597577356425361925120741 15487045754329755360960139)
        ·
          refine ⟨23230568631494633041440209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15487045754329755360960139 23230568631494633041440209)
          ·
            refine ⟨17422926473620974781080157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23230568631494633041440209 17422926473620974781080157)
            ·
              refine ⟨6533597427607865542905059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17422926473620974781080157 6533597427607865542905059)
              ·
                refine ⟨9800396141411798314357589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533597427607865542905059 9800396141411798314357589)
                ·
                  refine ⟨57424196141084755748189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9800396141411798314357589 57424196141084755748189)
                  ·
                    rfl

theorem cell23_1006499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 9].length) (baseStart_1006499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006499 prefixEnd_1006499 := by exact prefixLift 1006499
  have htrace : WordTrace (prefixWord ++ tailWord_1006499) baseStart_1006499 baseEnd_1006499 := by
    simpa [prefixWord, tailWord_1006499, baseEnd_1006499] using wordTrace_append hprefix tailTrace_1006499
  have hstable : (prefixWord ++ tailWord_1006499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006499).length < 2 ^ (prefixWord ++ tailWord_1006499).sum := by decide
  have hdescent : baseEnd_1006499 < baseStart_1006499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006590 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1006590 : Nat := 118140960795 + 1006590 * 2 ^ 59
def prefixEnd_1006590 : Nat := 4983230072969 + 3 ^ 40 * 1006590 * 2
def baseEnd_1006590 : Nat := 516864492009321945695783

theorem tailTrace_1006590 : CollatzResearch.WordTrace tailWord_1006590 prefixEnd_1006590 516864492009321945695783 := by
  unfold tailWord_1006590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589169177912977091313153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24475568948869211153670149 4589169177912977091313153)
  ·
    refine ⟨3441876883434732818484865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4589169177912977091313153 3441876883434732818484865)
    ·
      refine ⟨2581407662576049613863649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3441876883434732818484865 2581407662576049613863649)
      ·
        refine ⟨1936055746932037210397737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2581407662576049613863649 1936055746932037210397737)
        ·
          refine ⟨1452041810199027907798303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936055746932037210397737 1452041810199027907798303)
          ·
            refine ⟨2178062715298541861697455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452041810199027907798303 2178062715298541861697455)
            ·
              refine ⟨3267094072947812792546183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178062715298541861697455 3267094072947812792546183)
              ·
                refine ⟨4900641109421719188819275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267094072947812792546183 4900641109421719188819275)
                ·
                  refine ⟨7350961664132578783228913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4900641109421719188819275 7350961664132578783228913)
                  ·
                    refine ⟨5513221248099434087421685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7350961664132578783228913 5513221248099434087421685)
                    ·
                      refine ⟨516864492009321945695783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5513221248099434087421685 516864492009321945695783)
                      ·
                        rfl

theorem cell23_1006590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1006590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006590 prefixEnd_1006590 := by exact prefixLift 1006590
  have htrace : WordTrace (prefixWord ++ tailWord_1006590) baseStart_1006590 baseEnd_1006590 := by
    simpa [prefixWord, tailWord_1006590, baseEnd_1006590] using wordTrace_append hprefix tailTrace_1006590
  have hstable : (prefixWord ++ tailWord_1006590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006590).length < 2 ^ (prefixWord ++ tailWord_1006590).sum := by decide
  have hdescent : baseEnd_1006590 < baseStart_1006590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006643 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 3, 5, 2]
def baseStart_1006643 : Nat := 118140960795 + 1006643 * 2 ^ 59
def prefixEnd_1006643 : Nat := 4983230072969 + 3 ^ 40 * 1006643 * 2
def baseEnd_1006643 : Nat := 516891706484010238333039

theorem tailTrace_1006643 : CollatzResearch.WordTrace tailWord_1006643 prefixEnd_1006643 516891706484010238333039 := by
  unfold tailWord_1006643
  simp only [CollatzResearch.WordTrace]
  refine ⟨36715286492111806782184583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24476857661407871188123055 36715286492111806782184583)
  ·
    refine ⟨55072929738167710173276875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36715286492111806782184583 55072929738167710173276875)
    ·
      refine ⟨82609394607251565259915313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55072929738167710173276875 82609394607251565259915313)
      ·
        refine ⟨61957045955438673944936485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82609394607251565259915313 61957045955438673944936485)
        ·
          refine ⟨11616946116644751364675591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61957045955438673944936485 11616946116644751364675591)
          ·
            refine ⟨17425419174967127047013387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11616946116644751364675591 17425419174967127047013387)
            ·
              refine ⟨26138128762450690570520081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17425419174967127047013387 26138128762450690570520081)
              ·
                refine ⟨19603596571838017927890061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26138128762450690570520081 19603596571838017927890061)
                ·
                  refine ⟨7351348714439256722958773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19603596571838017927890061 7351348714439256722958773)
                  ·
                    refine ⟨689188941978680317777385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7351348714439256722958773 689188941978680317777385)
                    ·
                      refine ⟨516891706484010238333039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689188941978680317777385 516891706484010238333039)
                      ·
                        rfl

theorem cell23_1006643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 5, 2].length) (baseStart_1006643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006643 prefixEnd_1006643 := by exact prefixLift 1006643
  have htrace : WordTrace (prefixWord ++ tailWord_1006643) baseStart_1006643 baseEnd_1006643 := by
    simpa [prefixWord, tailWord_1006643, baseEnd_1006643] using wordTrace_append hprefix tailTrace_1006643
  have hstable : (prefixWord ++ tailWord_1006643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006643).length < 2 ^ (prefixWord ++ tailWord_1006643).sum := by decide
  have hdescent : baseEnd_1006643 < baseStart_1006643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006644 : List Nat := [2, 5, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1006644 : Nat := 118140960795 + 1006644 * 2 ^ 59
def prefixEnd_1006644 : Nat := 4983230072969 + 3 ^ 40 * 1006644 * 2
def baseEnd_1006644 : Nat := 172297406654888244806845

theorem tailTrace_1006644 : CollatzResearch.WordTrace tailWord_1006644 prefixEnd_1006644 172297406654888244806845 := by
  unfold tailWord_1006644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18357661482554091976485493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24476881976738789301980657 18357661482554091976485493)
  ·
    refine ⟨1721030763989446122795515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18357661482554091976485493 1721030763989446122795515)
    ·
      refine ⟨2581546145984169184193273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721030763989446122795515 2581546145984169184193273)
      ·
        refine ⟨1936159609488126888144955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2581546145984169184193273 1936159609488126888144955)
        ·
          refine ⟨2904239414232190332217433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936159609488126888144955 2904239414232190332217433)
          ·
            refine ⟨2178179560674142749163075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2904239414232190332217433 2178179560674142749163075)
            ·
              refine ⟨3267269341011214123744613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178179560674142749163075 3267269341011214123744613)
              ·
                refine ⟨612613001439602648202115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3267269341011214123744613 612613001439602648202115)
                ·
                  refine ⟨918919502159403972303173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612613001439602648202115 918919502159403972303173)
                  ·
                    refine ⟨172297406654888244806845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 918919502159403972303173 172297406654888244806845)
                    ·
                      rfl

theorem cell23_1006644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1006644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006644 prefixEnd_1006644 := by exact prefixLift 1006644
  have htrace : WordTrace (prefixWord ++ tailWord_1006644) baseStart_1006644 baseEnd_1006644 := by
    simpa [prefixWord, tailWord_1006644, baseEnd_1006644] using wordTrace_append hprefix tailTrace_1006644
  have hstable : (prefixWord ++ tailWord_1006644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006644).length < 2 ^ (prefixWord ++ tailWord_1006644).sum := by decide
  have hdescent : baseEnd_1006644 < baseStart_1006644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006653 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_1006653 : Nat := 118140960795 + 1006653 * 2 ^ 59
def prefixEnd_1006653 : Nat := 4983230072969 + 3 ^ 40 * 1006653 * 2
def baseEnd_1006653 : Nat := 172298947096851733069331

theorem tailTrace_1006653 : CollatzResearch.WordTrace tailWord_1006653 prefixEnd_1006653 172298947096851733069331 := by
  unfold tailWord_1006653
  simp only [CollatzResearch.WordTrace]
  refine ⟨36715651222075578490048613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24477100814717052326699075 36715651222075578490048613)
  ·
    refine ⟨6884184604139170966884115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36715651222075578490048613 6884184604139170966884115)
    ·
      refine ⟨10326276906208756450326173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884184604139170966884115 10326276906208756450326173)
      ·
        refine ⟨3872353839828283668872315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10326276906208756450326173 3872353839828283668872315)
        ·
          refine ⟨5808530759742425503308473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872353839828283668872315 5808530759742425503308473)
          ·
            refine ⟨4356398069806819127481355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5808530759742425503308473 4356398069806819127481355)
            ·
              refine ⟨6534597104710228691222033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356398069806819127481355 6534597104710228691222033)
              ·
                refine ⟨4900947828532671518416525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6534597104710228691222033 4900947828532671518416525)
                ·
                  refine ⟨1837855435699751819406197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4900947828532671518416525 1837855435699751819406197)
                  ·
                    refine ⟨172298947096851733069331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1837855435699751819406197 172298947096851733069331)
                    ·
                      rfl

theorem cell23_1006653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_1006653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006653 prefixEnd_1006653 := by exact prefixLift 1006653
  have htrace : WordTrace (prefixWord ++ tailWord_1006653) baseStart_1006653 baseEnd_1006653 := by
    simpa [prefixWord, tailWord_1006653, baseEnd_1006653] using wordTrace_append hprefix tailTrace_1006653
  have hstable : (prefixWord ++ tailWord_1006653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006653).length < 2 ^ (prefixWord ++ tailWord_1006653).sum := by decide
  have hdescent : baseEnd_1006653 < baseStart_1006653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006673 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_1006673 : Nat := 118140960795 + 1006673 * 2 ^ 59
def prefixEnd_1006673 : Nat := 4983230072969 + 3 ^ 40 * 1006673 * 2
def baseEnd_1006673 : Nat := 516907110903645120957901

theorem tailTrace_1006673 : CollatzResearch.WordTrace tailWord_1006673 prefixEnd_1006673 516907110903645120957901 := by
  unfold tailWord_1006673
  simp only [CollatzResearch.WordTrace]
  refine ⟨36716380682003121905776673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24477587121335414603851115 36716380682003121905776673)
  ·
    refine ⟨27537285511502341429332505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36716380682003121905776673 27537285511502341429332505)
    ·
      refine ⟨20652964133626756071999379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27537285511502341429332505 20652964133626756071999379)
      ·
        refine ⟨30979446200440134107999069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20652964133626756071999379 30979446200440134107999069)
        ·
          refine ⟨11617292325165050290499651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30979446200440134107999069 11617292325165050290499651)
          ·
            refine ⟨17425938487747575435749477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11617292325165050290499651 17425938487747575435749477)
            ·
              refine ⟨3267363466452670394203027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17425938487747575435749477 3267363466452670394203027)
              ·
                refine ⟨4901045199679005591304541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267363466452670394203027 4901045199679005591304541)
                ·
                  refine ⟨1837891949879627096739203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4901045199679005591304541 1837891949879627096739203)
                  ·
                    refine ⟨2756837924819440645108805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1837891949879627096739203 2756837924819440645108805)
                    ·
                      refine ⟨516907110903645120957901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2756837924819440645108805 516907110903645120957901)
                      ·
                        rfl

theorem cell23_1006673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_1006673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006673 prefixEnd_1006673 := by exact prefixLift 1006673
  have htrace : WordTrace (prefixWord ++ tailWord_1006673) baseStart_1006673 baseEnd_1006673 := by
    simpa [prefixWord, tailWord_1006673, baseEnd_1006673] using wordTrace_append hprefix tailTrace_1006673
  have hstable : (prefixWord ++ tailWord_1006673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006673).length < 2 ^ (prefixWord ++ tailWord_1006673).sum := by decide
  have hdescent : baseEnd_1006673 < baseStart_1006673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006684 : List Nat := [2, 2, 4, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_1006684 : Nat := 118140960795 + 1006684 * 2 ^ 59
def prefixEnd_1006684 : Nat := 4983230072969 + 3 ^ 40 * 1006684 * 2
def baseEnd_1006684 : Nat := 516912759190844577920351

theorem tailTrace_1006684 : CollatzResearch.WordTrace tailWord_1006684 prefixEnd_1006684 516912759190844577920351 := by
  unfold tailWord_1006684
  simp only [CollatzResearch.WordTrace]
  refine ⟨18358390942481635392213553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24477854589975513856284737 18358390942481635392213553)
  ·
    refine ⟨13768793206861226544160165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18358390942481635392213553 13768793206861226544160165)
    ·
      refine ⟨2581648726286479977030031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13768793206861226544160165 2581648726286479977030031)
      ·
        refine ⟨3872473089429719965545047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581648726286479977030031 3872473089429719965545047)
        ·
          refine ⟨5808709634144579948317571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872473089429719965545047 5808709634144579948317571)
          ·
            refine ⟨8713064451216869922476357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808709634144579948317571 8713064451216869922476357)
            ·
              refine ⟨1633699584603163110464317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8713064451216869922476357 1633699584603163110464317)
              ·
                refine ⟨612637344226186166424119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1633699584603163110464317 612637344226186166424119)
                ·
                  refine ⟨918956016339279249636179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612637344226186166424119 918956016339279249636179)
                  ·
                    refine ⟨1378434024508918874454269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 918956016339279249636179 1378434024508918874454269)
                    ·
                      refine ⟨516912759190844577920351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1378434024508918874454269 516912759190844577920351)
                      ·
                        rfl

theorem cell23_1006684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_1006684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006684 prefixEnd_1006684 := by exact prefixLift 1006684
  have htrace : WordTrace (prefixWord ++ tailWord_1006684) baseStart_1006684 baseEnd_1006684 := by
    simpa [prefixWord, tailWord_1006684, baseEnd_1006684] using wordTrace_append hprefix tailTrace_1006684
  have hstable : (prefixWord ++ tailWord_1006684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006684).length < 2 ^ (prefixWord ++ tailWord_1006684).sum := by decide
  have hdescent : baseEnd_1006684 < baseStart_1006684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006693 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1006693 : Nat := 118140960795 + 1006693 * 2 ^ 59
def prefixEnd_1006693 : Nat := 4983230072969 + 3 ^ 40 * 1006693 * 2
def baseEnd_1006693 : Nat := 516917380516735042707809

theorem tailTrace_1006693 : CollatzResearch.WordTrace tailWord_1006693 prefixEnd_1006693 516917380516735042707809 := by
  unfold tailWord_1006693
  simp only [CollatzResearch.WordTrace]
  refine ⟨36717110141930665321504733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24478073427953776881003155 36717110141930665321504733)
  ·
    refine ⟨13768916303223999495564275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36717110141930665321504733 13768916303223999495564275)
    ·
      refine ⟨20653374454835999243346413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13768916303223999495564275 20653374454835999243346413)
      ·
        refine ⟨7745015420563499716254905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20653374454835999243346413 7745015420563499716254905)
        ·
          refine ⟨5808761565422624787191179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7745015420563499716254905 5808761565422624787191179)
          ·
            refine ⟨8713142348133937180786769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808761565422624787191179 8713142348133937180786769)
            ·
              refine ⟨6534856761100452885590077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8713142348133937180786769 6534856761100452885590077)
              ·
                refine ⟨2450571285412669832096279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6534856761100452885590077 2450571285412669832096279)
                ·
                  refine ⟨3675856928119004748144419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450571285412669832096279 3675856928119004748144419)
                  ·
                    refine ⟨5513785392178507122216629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675856928119004748144419 5513785392178507122216629)
                    ·
                      refine ⟨516917380516735042707809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5513785392178507122216629 516917380516735042707809)
                      ·
                        rfl

theorem cell23_1006693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1006693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006693 prefixEnd_1006693 := by exact prefixLift 1006693
  have htrace : WordTrace (prefixWord ++ tailWord_1006693) baseStart_1006693 baseEnd_1006693 := by
    simpa [prefixWord, tailWord_1006693, baseEnd_1006693] using wordTrace_append hprefix tailTrace_1006693
  have hstable : (prefixWord ++ tailWord_1006693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006693).length < 2 ^ (prefixWord ++ tailWord_1006693).sum := by decide
  have hdescent : baseEnd_1006693 < baseStart_1006693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006710 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1006710 : Nat := 118140960795 + 1006710 * 2 ^ 59
def prefixEnd_1006710 : Nat := 4983230072969 + 3 ^ 40 * 1006710 * 2
def baseEnd_1006710 : Nat := 516926109687861476195231

theorem tailTrace_1006710 : CollatzResearch.WordTrace tailWord_1006710 prefixEnd_1006710 516926109687861476195231 := by
  unfold tailWord_1006710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2294858136429317326554599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24478486788579384816582389 2294858136429317326554599)
  ·
    refine ⟨3442287204643975989831899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2294858136429317326554599 3442287204643975989831899)
    ·
      refine ⟨5163430806965963984747849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442287204643975989831899 5163430806965963984747849)
      ·
        refine ⟨3872573105224472988560887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5163430806965963984747849 3872573105224472988560887)
        ·
          refine ⟨5808859657836709482841331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872573105224472988560887 5808859657836709482841331)
          ·
            refine ⟨8713289486755064224261997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808859657836709482841331 8713289486755064224261997)
            ·
              refine ⟨3267483557533149084098249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8713289486755064224261997 3267483557533149084098249)
              ·
                refine ⟨2450612668149861813073687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267483557533149084098249 2450612668149861813073687)
                ·
                  refine ⟨3675919002224792719610531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450612668149861813073687 3675919002224792719610531)
                  ·
                    refine ⟨5513878503337189079415797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3675919002224792719610531 5513878503337189079415797)
                    ·
                      refine ⟨516926109687861476195231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5513878503337189079415797 516926109687861476195231)
                      ·
                        rfl

theorem cell23_1006710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1006710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006710 prefixEnd_1006710 := by exact prefixLift 1006710
  have htrace : WordTrace (prefixWord ++ tailWord_1006710) baseStart_1006710 baseEnd_1006710 := by
    simpa [prefixWord, tailWord_1006710, baseEnd_1006710] using wordTrace_append hprefix tailTrace_1006710
  have hstable : (prefixWord ++ tailWord_1006710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006710).length < 2 ^ (prefixWord ++ tailWord_1006710).sum := by decide
  have hdescent : baseEnd_1006710 < baseStart_1006710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006717 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_1006717 : Nat := 118140960795 + 1006717 * 2 ^ 59
def prefixEnd_1006717 : Nat := 4983230072969 + 3 ^ 40 * 1006717 * 2
def baseEnd_1006717 : Nat := 172309901350814316269233

theorem tailTrace_1006717 : CollatzResearch.WordTrace tailWord_1006717 prefixEnd_1006717 172309901350814316269233 := by
  unfold tailWord_1006717
  simp only [CollatzResearch.WordTrace]
  refine ⟨36717985493843717420378405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24478656995895811613585603 36717985493843717420378405)
  ·
    refine ⟨6884622280095697016320951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36717985493843717420378405 6884622280095697016320951)
    ·
      refine ⟨10326933420143545524481427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884622280095697016320951 10326933420143545524481427)
      ·
        refine ⟨15490400130215318286722141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10326933420143545524481427 15490400130215318286722141)
        ·
          refine ⟨5808900048830744357520803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15490400130215318286722141 5808900048830744357520803)
          ·
            refine ⟨8713350073246116536281205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5808900048830744357520803 8713350073246116536281205)
            ·
              refine ⟨816876569366823425276363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8713350073246116536281205 816876569366823425276363)
              ·
                refine ⟨1225314854050235137914545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816876569366823425276363 1225314854050235137914545)
                ·
                  refine ⟨918986140537676353435909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1225314854050235137914545 918986140537676353435909)
                  ·
                    refine ⟨172309901350814316269233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 918986140537676353435909 172309901350814316269233)
                    ·
                      rfl

theorem cell23_1006717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_1006717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006717 prefixEnd_1006717 := by exact prefixLift 1006717
  have htrace : WordTrace (prefixWord ++ tailWord_1006717) baseStart_1006717 baseEnd_1006717 := by
    simpa [prefixWord, tailWord_1006717, baseEnd_1006717] using wordTrace_append hprefix tailTrace_1006717
  have hstable : (prefixWord ++ tailWord_1006717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006717).length < 2 ^ (prefixWord ++ tailWord_1006717).sum := by decide
  have hdescent : baseEnd_1006717 < baseStart_1006717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006753 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1006753 : Nat := 118140960795 + 1006753 * 2 ^ 59
def prefixEnd_1006753 : Nat := 4983230072969 + 3 ^ 40 * 1006753 * 2
def baseEnd_1006753 : Nat := 516948189356004807957533

theorem tailTrace_1006753 : CollatzResearch.WordTrace tailWord_1006753 prefixEnd_1006753 516948189356004807957533 := by
  unfold tailWord_1006753
  simp only [CollatzResearch.WordTrace]
  refine ⟨36719298521713295568688913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24479532347808863712459275 36719298521713295568688913)
  ·
    refine ⟨27539473891284971676516685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36719298521713295568688913 27539473891284971676516685)
    ·
      refine ⟨10327302709231864378693757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27539473891284971676516685 10327302709231864378693757)
      ·
        refine ⟨3872738515961949142010159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10327302709231864378693757 3872738515961949142010159)
        ·
          refine ⟨5809107773942923713015239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3872738515961949142010159 5809107773942923713015239)
          ·
            refine ⟨8713661660914385569522859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809107773942923713015239 8713661660914385569522859)
            ·
              refine ⟨13070492491371578354284289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8713661660914385569522859 13070492491371578354284289)
              ·
                refine ⟨9802869368528683765713217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13070492491371578354284289 9802869368528683765713217)
                ·
                  refine ⟨7352152026396512824284913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9802869368528683765713217 7352152026396512824284913)
                  ·
                    refine ⟨5514114019797384618213685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7352152026396512824284913 5514114019797384618213685)
                    ·
                      refine ⟨516948189356004807957533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5514114019797384618213685 516948189356004807957533)
                      ·
                        rfl

theorem cell23_1006753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1006753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006753 prefixEnd_1006753 := by exact prefixLift 1006753
  have htrace : WordTrace (prefixWord ++ tailWord_1006753) baseStart_1006753 baseEnd_1006753 := by
    simpa [prefixWord, tailWord_1006753, baseEnd_1006753] using wordTrace_append hprefix tailTrace_1006753
  have hstable : (prefixWord ++ tailWord_1006753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006753).length < 2 ^ (prefixWord ++ tailWord_1006753).sum := by decide
  have hdescent : baseEnd_1006753 < baseStart_1006753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006783 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_1006783 : Nat := 118140960795 + 1006783 * 2 ^ 59
def prefixEnd_1006783 : Nat := 4983230072969 + 3 ^ 40 * 1006783 * 2
def baseEnd_1006783 : Nat := 516963593775639690582395

theorem tailTrace_1006783 : CollatzResearch.WordTrace tailWord_1006783 prefixEnd_1006783 516963593775639690582395 := by
  unfold tailWord_1006783
  simp only [CollatzResearch.WordTrace]
  refine ⟨36720392711604610692281003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24480261807736407128187335 36720392711604610692281003)
  ·
    refine ⟨55080589067406916038421505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36720392711604610692281003 55080589067406916038421505)
    ·
      refine ⟨41310441800555187028816129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55080589067406916038421505 41310441800555187028816129)
      ·
        refine ⟨30982831350416390271612097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41310441800555187028816129 30982831350416390271612097)
        ·
          refine ⟨23237123512812292703709073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30982831350416390271612097 23237123512812292703709073)
          ·
            refine ⟨17427842634609219527781805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23237123512812292703709073 17427842634609219527781805)
            ·
              refine ⟨6535440987978457322918177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17427842634609219527781805 6535440987978457322918177)
              ·
                refine ⟨4901580740983842992188633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6535440987978457322918177 4901580740983842992188633)
                ·
                  refine ⟨3676185555737882244141475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4901580740983842992188633 3676185555737882244141475)
                  ·
                    refine ⟨5514278333606823366212213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3676185555737882244141475 5514278333606823366212213)
                    ·
                      refine ⟨516963593775639690582395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5514278333606823366212213 516963593775639690582395)
                      ·
                        rfl

theorem cell23_1006783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_1006783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006783 prefixEnd_1006783 := by exact prefixLift 1006783
  have htrace : WordTrace (prefixWord ++ tailWord_1006783) baseStart_1006783 baseEnd_1006783 := by
    simpa [prefixWord, tailWord_1006783, baseEnd_1006783] using wordTrace_append hprefix tailTrace_1006783
  have hstable : (prefixWord ++ tailWord_1006783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006783).length < 2 ^ (prefixWord ++ tailWord_1006783).sum := by decide
  have hdescent : baseEnd_1006783 < baseStart_1006783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006830 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1006830 : Nat := 118140960795 + 1006830 * 2 ^ 59
def prefixEnd_1006830 : Nat := 4983230072969 + 3 ^ 40 * 1006830 * 2
def baseEnd_1006830 : Nat := 516987727366401006694679

theorem tailTrace_1006830 : CollatzResearch.WordTrace tailWord_1006830 prefixEnd_1006830 516987727366401006694679 := by
  unfold tailWord_1006830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590263367804292214905243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24481404628289558479494629 4590263367804292214905243)
  ·
    refine ⟨6885395051706438322357865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4590263367804292214905243 6885395051706438322357865)
    ·
      refine ⟨5164046288779828741768399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6885395051706438322357865 5164046288779828741768399)
      ·
        refine ⟨7746069433169743112652599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5164046288779828741768399 7746069433169743112652599)
        ·
          refine ⟨11619104149754614668978899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7746069433169743112652599 11619104149754614668978899)
          ·
            refine ⟨17428656224631922003468349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619104149754614668978899 17428656224631922003468349)
            ·
              refine ⟨6535746084236970751300631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17428656224631922003468349 6535746084236970751300631)
              ·
                refine ⟨9803619126355456126950947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535746084236970751300631 9803619126355456126950947)
                ·
                  refine ⟨14705428689533184190426421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803619126355456126950947 14705428689533184190426421)
                  ·
                    refine ⟨1378633939643736017852477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14705428689533184190426421 1378633939643736017852477)
                    ·
                      refine ⟨516987727366401006694679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1378633939643736017852477 516987727366401006694679)
                      ·
                        rfl

theorem cell23_1006830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1006830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006830 prefixEnd_1006830 := by exact prefixLift 1006830
  have htrace : WordTrace (prefixWord ++ tailWord_1006830) baseStart_1006830 baseEnd_1006830 := by
    simpa [prefixWord, tailWord_1006830, baseEnd_1006830] using wordTrace_append hprefix tailTrace_1006830
  have hstable : (prefixWord ++ tailWord_1006830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006830).length < 2 ^ (prefixWord ++ tailWord_1006830).sum := by decide
  have hdescent : baseEnd_1006830 < baseStart_1006830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006833 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 1, 7]
def baseStart_1006833 : Nat := 118140960795 + 1006833 * 2 ^ 59
def prefixEnd_1006833 : Nat := 4983230072969 + 3 ^ 40 * 1006833 * 2
def baseEnd_1006833 : Nat := 172329755936121498319055

theorem tailTrace_1006833 : CollatzResearch.WordTrace tailWord_1006833 prefixEnd_1006833 172329755936121498319055 := by
  unfold tailWord_1006833
  simp only [CollatzResearch.WordTrace]
  refine ⟨36722216361423469231601153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24481477574282312821067435 36722216361423469231601153)
  ·
    refine ⟨27541662271067601923700865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36722216361423469231601153 27541662271067601923700865)
    ·
      refine ⟨20656246703300701442775649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27541662271067601923700865 20656246703300701442775649)
      ·
        refine ⟨15492185027475526082081737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20656246703300701442775649 15492185027475526082081737)
        ·
          refine ⟨11619138770606644561561303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15492185027475526082081737 11619138770606644561561303)
          ·
            refine ⟨17428708155909966842341955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619138770606644561561303 17428708155909966842341955)
            ·
              refine ⟨26143062233864950263512933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17428708155909966842341955 26143062233864950263512933)
              ·
                refine ⟨4901824168849678174408675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26143062233864950263512933 4901824168849678174408675)
                ·
                  refine ⟨7352736253274517261613013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901824168849678174408675 7352736253274517261613013)
                  ·
                    refine ⟨172329755936121498319055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7352736253274517261613013 172329755936121498319055)
                    ·
                      rfl

theorem cell23_1006833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_1006833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006833 prefixEnd_1006833 := by exact prefixLift 1006833
  have htrace : WordTrace (prefixWord ++ tailWord_1006833) baseStart_1006833 baseEnd_1006833 := by
    simpa [prefixWord, tailWord_1006833, baseEnd_1006833] using wordTrace_append hprefix tailTrace_1006833
  have hstable : (prefixWord ++ tailWord_1006833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006833).length < 2 ^ (prefixWord ++ tailWord_1006833).sum := by decide
  have hdescent : baseEnd_1006833 < baseStart_1006833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006897 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 3, 4]
def baseStart_1006897 : Nat := 118140960795 + 1006897 * 2 ^ 59
def prefixEnd_1006897 : Nat := 4983230072969 + 3 ^ 40 * 1006897 * 2
def baseEnd_1006897 : Nat := 172340710190084081518957

theorem tailTrace_1006897 : CollatzResearch.WordTrace tailWord_1006897 prefixEnd_1006897 172340710190084081518957 := by
  unfold tailWord_1006897
  simp only [CollatzResearch.WordTrace]
  refine ⟨36724550633191608161930945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24483033755461072107953963 36724550633191608161930945)
  ·
    refine ⟨27543412974893706121448209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36724550633191608161930945 27543412974893706121448209)
    ·
      refine ⟨20657559731170279591086157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27543412974893706121448209 20657559731170279591086157)
      ·
        refine ⟨7746584899188854846657309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20657559731170279591086157 7746584899188854846657309)
        ·
          refine ⟨2904969337195820567496491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7746584899188854846657309 2904969337195820567496491)
          ·
            refine ⟨4357454005793730851244737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904969337195820567496491 4357454005793730851244737)
            ·
              refine ⟨3268090504345298138433553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4357454005793730851244737 3268090504345298138433553)
              ·
                refine ⟨2451067878258973603825165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268090504345298138433553 2451067878258973603825165)
                ·
                  refine ⟨919150454347115101434437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2451067878258973603825165 919150454347115101434437)
                  ·
                    refine ⟨172340710190084081518957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 919150454347115101434437 172340710190084081518957)
                    ·
                      rfl

theorem cell23_1006897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_1006897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006897 prefixEnd_1006897 := by exact prefixLift 1006897
  have htrace : WordTrace (prefixWord ++ tailWord_1006897) baseStart_1006897 baseEnd_1006897 := by
    simpa [prefixWord, tailWord_1006897, baseEnd_1006897] using wordTrace_append hprefix tailTrace_1006897
  have hstable : (prefixWord ++ tailWord_1006897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006897).length < 2 ^ (prefixWord ++ tailWord_1006897).sum := by decide
  have hdescent : baseEnd_1006897 < baseStart_1006897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006903 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1006903 : Nat := 118140960795 + 1006903 * 2 ^ 59
def prefixEnd_1006903 : Nat := 4983230072969 + 3 ^ 40 * 1006903 * 2
def baseEnd_1006903 : Nat := 517025211454179221081843

theorem tailTrace_1006903 : CollatzResearch.WordTrace tailWord_1006903 prefixEnd_1006903 517025211454179221081843 := by
  unfold tailWord_1006903
  simp only [CollatzResearch.WordTrace]
  refine ⟨36724769471169871186649363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24483179647446580791099575 36724769471169871186649363)
  ·
    refine ⟨55087154206754806779974045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36724769471169871186649363 55087154206754806779974045)
    ·
      refine ⟨20657682827533052542490267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55087154206754806779974045 20657682827533052542490267)
      ·
        refine ⟨30986524241299578813735401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20657682827533052542490267 30986524241299578813735401)
        ·
          refine ⟨23239893180974684110301551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30986524241299578813735401 23239893180974684110301551)
          ·
            refine ⟨34859839771462026165452327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23239893180974684110301551 34859839771462026165452327)
            ·
              refine ⟨52289759657193039248178491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34859839771462026165452327 52289759657193039248178491)
              ·
                refine ⟨78434639485789558872267737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52289759657193039248178491 78434639485789558872267737)
                ·
                  refine ⟨58825979614342169154200803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78434639485789558872267737 58825979614342169154200803)
                  ·
                    refine ⟨88238969421513253731301205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58825979614342169154200803 88238969421513253731301205)
                    ·
                      refine ⟨517025211454179221081843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 88238969421513253731301205 517025211454179221081843)
                      ·
                        rfl

theorem cell23_1006903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1006903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006903 prefixEnd_1006903 := by exact prefixLift 1006903
  have htrace : WordTrace (prefixWord ++ tailWord_1006903) baseStart_1006903 baseEnd_1006903 := by
    simpa [prefixWord, tailWord_1006903, baseEnd_1006903] using wordTrace_append hprefix tailTrace_1006903
  have hstable : (prefixWord ++ tailWord_1006903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006903).length < 2 ^ (prefixWord ++ tailWord_1006903).sum := by decide
  have hdescent : baseEnd_1006903 < baseStart_1006903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006910 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_1006910 : Nat := 118140960795 + 1006910 * 2 ^ 59
def prefixEnd_1006910 : Nat := 4983230072969 + 3 ^ 40 * 1006910 * 2
def baseEnd_1006910 : Nat := 57447645090973410410479

theorem tailTrace_1006910 : CollatzResearch.WordTrace tailWord_1006910 prefixEnd_1006910 57447645090973410410479 := by
  unfold tailWord_1006910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590628097768063922769273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24483349854763007588102789 4590628097768063922769273)
  ·
    refine ⟨3442971073326047942076955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4590628097768063922769273 3442971073326047942076955)
    ·
      refine ⟨5164456609989071913115433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442971073326047942076955 5164456609989071913115433)
      ·
        refine ⟨3873342457491803934836575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5164456609989071913115433 3873342457491803934836575)
        ·
          refine ⟨5810013686237705902254863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873342457491803934836575 5810013686237705902254863)
          ·
            refine ⟨8715020529356558853382295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810013686237705902254863 8715020529356558853382295)
            ·
              refine ⟨13072530794034838280073443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715020529356558853382295 13072530794034838280073443)
              ·
                refine ⟨19608796191052257420110165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13072530794034838280073443 19608796191052257420110165)
                ·
                  refine ⟨57447645090973410410479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 19608796191052257420110165 57447645090973410410479)
                  ·
                    rfl

theorem cell23_1006910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_1006910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006910 prefixEnd_1006910 := by exact prefixLift 1006910
  have htrace : WordTrace (prefixWord ++ tailWord_1006910) baseStart_1006910 baseEnd_1006910 := by
    simpa [prefixWord, tailWord_1006910, baseEnd_1006910] using wordTrace_append hprefix tailTrace_1006910
  have hstable : (prefixWord ++ tailWord_1006910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006910).length < 2 ^ (prefixWord ++ tailWord_1006910).sum := by decide
  have hdescent : baseEnd_1006910 < baseStart_1006910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006923 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 11]
def baseStart_1006923 : Nat := 118140960795 + 1006923 * 2 ^ 59
def prefixEnd_1006923 : Nat := 4983230072969 + 3 ^ 40 * 1006923 * 2
def baseEnd_1006923 : Nat := 172345160355756380943917

theorem tailTrace_1006923 : CollatzResearch.WordTrace tailWord_1006923 prefixEnd_1006923 172345160355756380943917 := by
  unfold tailWord_1006923
  simp only [CollatzResearch.WordTrace]
  refine ⟨36725498931097414602377423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24483665954064943068251615 36725498931097414602377423)
  ·
    refine ⟨55088248396646121903566135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36725498931097414602377423 55088248396646121903566135)
    ·
      refine ⟨82632372594969182855349203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55088248396646121903566135 82632372594969182855349203)
      ·
        refine ⟨123948558892453774283023805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82632372594969182855349203 123948558892453774283023805)
        ·
          refine ⟨46480709584670165356133927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123948558892453774283023805 46480709584670165356133927)
          ·
            refine ⟨69721064377005248034200891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46480709584670165356133927 69721064377005248034200891)
            ·
              refine ⟨104581596565507872051301337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69721064377005248034200891 104581596565507872051301337)
              ·
                refine ⟨78436197424130904038476003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104581596565507872051301337 78436197424130904038476003)
                ·
                  refine ⟨117654296136196356057714005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78436197424130904038476003 117654296136196356057714005)
                  ·
                    refine ⟨172345160355756380943917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 117654296136196356057714005 172345160355756380943917)
                    ·
                      rfl

theorem cell23_1006923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 11].length) (baseStart_1006923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006923 prefixEnd_1006923 := by exact prefixLift 1006923
  have htrace : WordTrace (prefixWord ++ tailWord_1006923) baseStart_1006923 baseEnd_1006923 := by
    simpa [prefixWord, tailWord_1006923, baseEnd_1006923] using wordTrace_append hprefix tailTrace_1006923
  have hstable : (prefixWord ++ tailWord_1006923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006923).length < 2 ^ (prefixWord ++ tailWord_1006923).sum := by decide
  have hdescent : baseEnd_1006923 < baseStart_1006923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006944 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 6]
def baseStart_1006944 : Nat := 118140960795 + 1006944 * 2 ^ 59
def prefixEnd_1006944 : Nat := 4983230072969 + 3 ^ 40 * 1006944 * 2
def baseEnd_1006944 : Nat := 57449584906779284518795

theorem tailTrace_1006944 : CollatzResearch.WordTrace tailWord_1006944 prefixEnd_1006944 57449584906779284518795 := by
  unfold tailWord_1006944
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363132432010667594445943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24484176576014223459261257 18363132432010667594445943)
  ·
    refine ⟨27544698648016001391668915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363132432010667594445943 27544698648016001391668915)
    ·
      refine ⟨41317047972024002087503373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27544698648016001391668915 41317047972024002087503373)
      ·
        refine ⟨15493892989509000782813765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41317047972024002087503373 15493892989509000782813765)
        ·
          refine ⟨2905104935532937646777581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15493892989509000782813765 2905104935532937646777581)
          ·
            refine ⟨1089414350824851617541593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2905104935532937646777581 1089414350824851617541593)
            ·
              refine ⟨817060763118638713156195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089414350824851617541593 817060763118638713156195)
              ·
                refine ⟨1225591144677958069734293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817060763118638713156195 1225591144677958069734293)
                ·
                  refine ⟨57449584906779284518795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1225591144677958069734293 57449584906779284518795)
                  ·
                    rfl

theorem cell23_1006944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 6].length) (baseStart_1006944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006944 prefixEnd_1006944 := by exact prefixLift 1006944
  have htrace : WordTrace (prefixWord ++ tailWord_1006944) baseStart_1006944 baseEnd_1006944 := by
    simpa [prefixWord, tailWord_1006944, baseEnd_1006944] using wordTrace_append hprefix tailTrace_1006944
  have hstable : (prefixWord ++ tailWord_1006944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006944).length < 2 ^ (prefixWord ++ tailWord_1006944).sum := by decide
  have hdescent : baseEnd_1006944 < baseStart_1006944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006957 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1006957 : Nat := 118140960795 + 1006957 * 2 ^ 59
def prefixEnd_1006957 : Nat := 4983230072969 + 3 ^ 40 * 1006957 * 2
def baseEnd_1006957 : Nat := 172350979803174003268865

theorem tailTrace_1006957 : CollatzResearch.WordTrace tailWord_1006957 prefixEnd_1006957 172350979803174003268865 := by
  unfold tailWord_1006957
  simp only [CollatzResearch.WordTrace]
  refine ⟨36726739012974238409115125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24484492675316158939410083 36726739012974238409115125)
  ·
    refine ⟨3443131782466334850854543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36726739012974238409115125 3443131782466334850854543)
    ·
      refine ⟨5164697673699502276281815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3443131782466334850854543 5164697673699502276281815)
      ·
        refine ⟨7747046510549253414422723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5164697673699502276281815 7747046510549253414422723)
        ·
          refine ⟨11620569765823880121634085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7747046510549253414422723 11620569765823880121634085)
          ·
            refine ⟨2178856831091977522806391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11620569765823880121634085 2178856831091977522806391)
            ·
              refine ⟨3268285246637966284209587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178856831091977522806391 3268285246637966284209587)
              ·
                refine ⟨4902427869956949426314381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3268285246637966284209587 4902427869956949426314381)
                ·
                  refine ⟨1838410451233856034867893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4902427869956949426314381 1838410451233856034867893)
                  ·
                    refine ⟨172350979803174003268865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1838410451233856034867893 172350979803174003268865)
                    ·
                      rfl

theorem cell23_1006957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1006957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006957 prefixEnd_1006957 := by exact prefixLift 1006957
  have htrace : WordTrace (prefixWord ++ tailWord_1006957) baseStart_1006957 baseEnd_1006957 := by
    simpa [prefixWord, tailWord_1006957, baseEnd_1006957] using wordTrace_append hprefix tailTrace_1006957
  have hstable : (prefixWord ++ tailWord_1006957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006957).length < 2 ^ (prefixWord ++ tailWord_1006957).sum := by decide
  have hdescent : baseEnd_1006957 < baseStart_1006957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006970 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_1006970 : Nat := 118140960795 + 1006970 * 2 ^ 59
def prefixEnd_1006970 : Nat := 4983230072969 + 3 ^ 40 * 1006970 * 2
def baseEnd_1006970 : Nat := 172353204886010152981345

theorem tailTrace_1006970 : CollatzResearch.WordTrace tailWord_1006970 prefixEnd_1006970 172353204886010152981345 := by
  unfold tailWord_1006970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181803290481785407334591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24484808774618094419558909 9181803290481785407334591)
  ·
    refine ⟨13772704935722678111001887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9181803290481785407334591 13772704935722678111001887)
    ·
      refine ⟨20659057403584017166502831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13772704935722678111001887 20659057403584017166502831)
      ·
        refine ⟨30988586105376025749754247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20659057403584017166502831 30988586105376025749754247)
        ·
          refine ⟨46482879158064038624631371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30988586105376025749754247 46482879158064038624631371)
          ·
            refine ⟨69724318737096057936947057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46482879158064038624631371 69724318737096057936947057)
            ·
              refine ⟨52293239052822043452710293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69724318737096057936947057 52293239052822043452710293)
              ·
                refine ⟨2451245580601033286845795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52293239052822043452710293 2451245580601033286845795)
                ·
                  refine ⟨3676868370901549930268693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451245580601033286845795 3676868370901549930268693)
                  ·
                    refine ⟨172353204886010152981345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3676868370901549930268693 172353204886010152981345)
                    ·
                      rfl

theorem cell23_1006970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_1006970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006970 prefixEnd_1006970 := by exact prefixLift 1006970
  have htrace : WordTrace (prefixWord ++ tailWord_1006970) baseStart_1006970 baseEnd_1006970 := by
    simpa [prefixWord, tailWord_1006970, baseEnd_1006970] using wordTrace_append hprefix tailTrace_1006970
  have hstable : (prefixWord ++ tailWord_1006970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006970).length < 2 ^ (prefixWord ++ tailWord_1006970).sum := by decide
  have hdescent : baseEnd_1006970 < baseStart_1006970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006997 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1006997 : Nat := 118140960795 + 1006997 * 2 ^ 59
def prefixEnd_1006997 : Nat := 4983230072969 + 3 ^ 40 * 1006997 * 2
def baseEnd_1006997 : Nat := 517073478635701853306411

theorem tailTrace_1006997 : CollatzResearch.WordTrace tailWord_1006997 prefixEnd_1006997 517073478635701853306411 := by
  unfold tailWord_1006997
  simp only [CollatzResearch.WordTrace]
  refine ⟨36728197932829325240571245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24485465288552883493714163 36728197932829325240571245)
  ·
    refine ⟨13773074224810996965214217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36728197932829325240571245 13773074224810996965214217)
    ·
      refine ⟨10329805668608247723910663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13773074224810996965214217 10329805668608247723910663)
      ·
        refine ⟨15494708502912371585865995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10329805668608247723910663 15494708502912371585865995)
        ·
          refine ⟨23242062754368557378798993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15494708502912371585865995 23242062754368557378798993)
          ·
            refine ⟨17431547065776418034099245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23242062754368557378798993 17431547065776418034099245)
            ·
              refine ⟨6536830149666156762787217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17431547065776418034099245 6536830149666156762787217)
              ·
                refine ⟨4902622612249617572090413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6536830149666156762787217 4902622612249617572090413)
                ·
                  refine ⟨1838483479593606589533905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4902622612249617572090413 1838483479593606589533905)
                  ·
                    refine ⟨1378862609695204942150429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1838483479593606589533905 1378862609695204942150429)
                    ·
                      refine ⟨517073478635701853306411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1378862609695204942150429 517073478635701853306411)
                      ·
                        rfl

theorem cell23_1006997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1006997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1006997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1006997 prefixEnd_1006997 := by exact prefixLift 1006997
  have htrace : WordTrace (prefixWord ++ tailWord_1006997) baseStart_1006997 baseEnd_1006997 := by
    simpa [prefixWord, tailWord_1006997, baseEnd_1006997] using wordTrace_append hprefix tailTrace_1006997
  have hstable : (prefixWord ++ tailWord_1006997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006997).length < 2 ^ (prefixWord ++ tailWord_1006997).sum := by decide
  have hdescent : baseEnd_1006997 < baseStart_1006997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007007 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1007007 : Nat := 118140960795 + 1007007 * 2 ^ 59
def prefixEnd_1007007 : Nat := 4983230072969 + 3 ^ 40 * 1007007 * 2
def baseEnd_1007007 : Nat := 517078613442246814181365

theorem tailTrace_1007007 : CollatzResearch.WordTrace tailWord_1007007 prefixEnd_1007007 517078613442246814181365 := by
  unfold tailWord_1007007
  simp only [CollatzResearch.WordTrace]
  refine ⟨36728562662793096948435275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24485708441862064632290183 36728562662793096948435275)
  ·
    refine ⟨55092843994189645422652913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36728562662793096948435275 55092843994189645422652913)
    ·
      refine ⟨41319632995642234066989685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55092843994189645422652913 41319632995642234066989685)
      ·
        refine ⟨3873715593341459443780283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41319632995642234066989685 3873715593341459443780283)
        ·
          refine ⟨5810573390012189165670425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873715593341459443780283 5810573390012189165670425)
          ·
            refine ⟨4357930042509141874252819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810573390012189165670425 4357930042509141874252819)
            ·
              refine ⟨6536895063763712811379229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357930042509141874252819 6536895063763712811379229)
              ·
                refine ⟨2451335648911392304267211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6536895063763712811379229 2451335648911392304267211)
                ·
                  refine ⟨3677003473367088456400817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451335648911392304267211 3677003473367088456400817)
                  ·
                    refine ⟨2757752605025316342300613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3677003473367088456400817 2757752605025316342300613)
                    ·
                      refine ⟨517078613442246814181365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2757752605025316342300613 517078613442246814181365)
                      ·
                        rfl

theorem cell23_1007007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1007007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007007 prefixEnd_1007007 := by exact prefixLift 1007007
  have htrace : WordTrace (prefixWord ++ tailWord_1007007) baseStart_1007007 baseEnd_1007007 := by
    simpa [prefixWord, tailWord_1007007, baseEnd_1007007] using wordTrace_append hprefix tailTrace_1007007
  have hstable : (prefixWord ++ tailWord_1007007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007007).length < 2 ^ (prefixWord ++ tailWord_1007007).sum := by decide
  have hdescent : baseEnd_1007007 < baseStart_1007007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007054 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_1007054 : Nat := 118140960795 + 1007054 * 2 ^ 59
def prefixEnd_1007054 : Nat := 4983230072969 + 3 ^ 40 * 1007054 * 2
def baseEnd_1007054 : Nat := 517102747033008130293649

theorem tailTrace_1007054 : CollatzResearch.WordTrace tailWord_1007054 prefixEnd_1007054 517102747033008130293649 := by
  unfold tailWord_1007054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4591284611702852996924527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24486851262415215983597477 4591284611702852996924527)
  ·
    refine ⟨6886926917554279495386791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4591284611702852996924527 6886926917554279495386791)
    ·
      refine ⟨10330390376331419243080187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6886926917554279495386791 10330390376331419243080187)
      ·
        refine ⟨15495585564497128864620281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10330390376331419243080187 15495585564497128864620281)
        ·
          refine ⟨11621689173372846648465211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15495585564497128864620281 11621689173372846648465211)
          ·
            refine ⟨17432533760059269972697817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11621689173372846648465211 17432533760059269972697817)
            ·
              refine ⟨13074400320044452479523363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17432533760059269972697817 13074400320044452479523363)
              ·
                refine ⟨19611600480066678719285045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13074400320044452479523363 19611600480066678719285045)
                ·
                  refine ⟨1838587545006251129932973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19611600480066678719285045 1838587545006251129932973)
                  ·
                    refine ⟨689470329377344173724865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838587545006251129932973 689470329377344173724865)
                    ·
                      refine ⟨517102747033008130293649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689470329377344173724865 517102747033008130293649)
                      ·
                        rfl

theorem cell23_1007054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_1007054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007054 prefixEnd_1007054 := by exact prefixLift 1007054
  have htrace : WordTrace (prefixWord ++ tailWord_1007054) baseStart_1007054 baseEnd_1007054 := by
    simpa [prefixWord, tailWord_1007054, baseEnd_1007054] using wordTrace_append hprefix tailTrace_1007054
  have hstable : (prefixWord ++ tailWord_1007054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007054).length < 2 ^ (prefixWord ++ tailWord_1007054).sum := by decide
  have hdescent : baseEnd_1007054 < baseStart_1007054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007067 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 8, 2]
def baseStart_1007067 : Nat := 118140960795 + 1007067 * 2 ^ 59
def prefixEnd_1007067 : Nat := 4983230072969 + 3 ^ 40 * 1007067 * 2
def baseEnd_1007067 : Nat := 517109422281516579431089

theorem tailTrace_1007067 : CollatzResearch.WordTrace tailWord_1007067 prefixEnd_1007067 517109422281516579431089 := by
  unfold tailWord_1007067
  simp only [CollatzResearch.WordTrace]
  refine ⟨36730751042575727195619455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24487167361717151463746303 36730751042575727195619455)
  ·
    refine ⟨55096126563863590793429183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36730751042575727195619455 55096126563863590793429183)
    ·
      refine ⟨82644189845795386190143775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55096126563863590793429183 82644189845795386190143775)
      ·
        refine ⟨123966284768693079285215663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82644189845795386190143775 123966284768693079285215663)
        ·
          refine ⟨185949427153039618927823495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123966284768693079285215663 185949427153039618927823495)
          ·
            refine ⟨278924140729559428391735243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185949427153039618927823495 278924140729559428391735243)
            ·
              refine ⟨418386211094339142587602865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278924140729559428391735243 418386211094339142587602865)
              ·
                refine ⟨313789658320754356940702149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418386211094339142587602865 313789658320754356940702149)
                ·
                  refine ⟨58835560935141441926381653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313789658320754356940702149 58835560935141441926381653)
                  ·
                    refine ⟨689479229708688772574785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58835560935141441926381653 689479229708688772574785)
                    ·
                      refine ⟨517109422281516579431089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689479229708688772574785 517109422281516579431089)
                      ·
                        rfl

theorem cell23_1007067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8, 2].length) (baseStart_1007067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007067 prefixEnd_1007067 := by exact prefixLift 1007067
  have htrace : WordTrace (prefixWord ++ tailWord_1007067) baseStart_1007067 baseEnd_1007067 := by
    simpa [prefixWord, tailWord_1007067, baseEnd_1007067] using wordTrace_append hprefix tailTrace_1007067
  have hstable : (prefixWord ++ tailWord_1007067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007067).length < 2 ^ (prefixWord ++ tailWord_1007067).sum := by decide
  have hdescent : baseEnd_1007067 < baseStart_1007067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007071 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 1, 3, 2]
def baseStart_1007071 : Nat := 118140960795 + 1007071 * 2 ^ 59
def prefixEnd_1007071 : Nat := 4983230072969 + 3 ^ 40 * 1007071 * 2
def baseEnd_1007071 : Nat := 517111476204134563781071

theorem tailTrace_1007071 : CollatzResearch.WordTrace tailWord_1007071 prefixEnd_1007071 517111476204134563781071 := by
  unfold tailWord_1007071
  simp only [CollatzResearch.WordTrace]
  refine ⟨36730896934561235878765067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24487264623040823919176711 36730896934561235878765067)
  ·
    refine ⟨55096345401841853818147601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36730896934561235878765067 55096345401841853818147601)
    ·
      refine ⟨41322259051381390363610701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55096345401841853818147601 41322259051381390363610701)
      ·
        refine ⟨15495847144268021386354013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41322259051381390363610701 15495847144268021386354013)
        ·
          refine ⟨5810942679100508019882755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15495847144268021386354013 5810942679100508019882755)
          ·
            refine ⟨8716414018650762029824133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810942679100508019882755 8716414018650762029824133)
            ·
              refine ⟨1634327628497017880592025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8716414018650762029824133 1634327628497017880592025)
              ·
                refine ⟨1225745721372763410444019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634327628497017880592025 1225745721372763410444019)
                ·
                  refine ⟨1838618582059145115666029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225745721372763410444019 1838618582059145115666029)
                  ·
                    refine ⟨689481968272179418374761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838618582059145115666029 689481968272179418374761)
                    ·
                      refine ⟨517111476204134563781071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689481968272179418374761 517111476204134563781071)
                      ·
                        rfl

theorem cell23_1007071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_1007071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007071 prefixEnd_1007071 := by exact prefixLift 1007071
  have htrace : WordTrace (prefixWord ++ tailWord_1007071) baseStart_1007071 baseEnd_1007071 := by
    simpa [prefixWord, tailWord_1007071, baseEnd_1007071] using wordTrace_append hprefix tailTrace_1007071
  have hstable : (prefixWord ++ tailWord_1007071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007071).length < 2 ^ (prefixWord ++ tailWord_1007071).sum := by decide
  have hdescent : baseEnd_1007071 < baseStart_1007071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007101 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_1007101 : Nat := 118140960795 + 1007101 * 2 ^ 59
def prefixEnd_1007101 : Nat := 4983230072969 + 3 ^ 40 * 1007101 * 2
def baseEnd_1007101 : Nat := 517126880623769446405933

theorem tailTrace_1007101 : CollatzResearch.WordTrace tailWord_1007101 prefixEnd_1007101 517126880623769446405933 := by
  unfold tailWord_1007101
  simp only [CollatzResearch.WordTrace]
  refine ⟨36731991124452551002357157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24487994082968367334904771 36731991124452551002357157)
  ·
    refine ⟨6887248335834853312941967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36731991124452551002357157 6887248335834853312941967)
    ·
      refine ⟨10330872503752279969412951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6887248335834853312941967 10330872503752279969412951)
      ·
        refine ⟨15496308755628419954119427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10330872503752279969412951 15496308755628419954119427)
        ·
          refine ⟨23244463133442629931179141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15496308755628419954119427 23244463133442629931179141)
          ·
            refine ⟨4358336837520493112096089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23244463133442629931179141 4358336837520493112096089)
            ·
              refine ⟨3268752628140369834072067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4358336837520493112096089 3268752628140369834072067)
              ·
                refine ⟨4903128942210554751108101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3268752628140369834072067 4903128942210554751108101)
                ·
                  refine ⟨919336676664479015832769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4903128942210554751108101 919336676664479015832769)
                  ·
                    refine ⟨689502507498359261874577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 919336676664479015832769 689502507498359261874577)
                    ·
                      refine ⟨517126880623769446405933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689502507498359261874577 517126880623769446405933)
                      ·
                        rfl

theorem cell23_1007101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_1007101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007101 prefixEnd_1007101 := by exact prefixLift 1007101
  have htrace : WordTrace (prefixWord ++ tailWord_1007101) baseStart_1007101 baseEnd_1007101 := by
    simpa [prefixWord, tailWord_1007101, baseEnd_1007101] using wordTrace_append hprefix tailTrace_1007101
  have hstable : (prefixWord ++ tailWord_1007101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007101).length < 2 ^ (prefixWord ++ tailWord_1007101).sum := by decide
  have hdescent : baseEnd_1007101 < baseStart_1007101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007158 : List Nat := [5, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_1007158 : Nat := 118140960795 + 1007158 * 2 ^ 59
def prefixEnd_1007158 : Nat := 4983230072969 + 3 ^ 40 * 1007158 * 2
def baseEnd_1007158 : Nat := 57461794335675080377019

theorem tailTrace_1007158 : CollatzResearch.WordTrace tailWord_1007158 prefixEnd_1007158 57461794335675080377019 := by
  unfold tailWord_1007158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295879380327878108573883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24489380056830699824788085 2295879380327878108573883)
  ·
    refine ⟨3443819070491817162860825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2295879380327878108573883 3443819070491817162860825)
    ·
      refine ⟨2582864302868862872145619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3443819070491817162860825 2582864302868862872145619)
      ·
        refine ⟨3874296454303294308218429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582864302868862872145619 3874296454303294308218429)
        ·
          refine ⟨1452861170363735365581911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3874296454303294308218429 1452861170363735365581911)
          ·
            refine ⟨2179291755545603048372867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452861170363735365581911 2179291755545603048372867)
            ·
              refine ⟨3268937633318404572559301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179291755545603048372867 3268937633318404572559301)
              ·
                refine ⟨612925806247200857354869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3268937633318404572559301 612925806247200857354869)
                ·
                  refine ⟨57461794335675080377019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 612925806247200857354869 57461794335675080377019)
                  ·
                    rfl

theorem cell23_1007158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_1007158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007158 prefixEnd_1007158 := by exact prefixLift 1007158
  have htrace : WordTrace (prefixWord ++ tailWord_1007158) baseStart_1007158 baseEnd_1007158 := by
    simpa [prefixWord, tailWord_1007158, baseEnd_1007158] using wordTrace_append hprefix tailTrace_1007158
  have hstable : (prefixWord ++ tailWord_1007158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007158).length < 2 ^ (prefixWord ++ tailWord_1007158).sum := by decide
  have hdescent : baseEnd_1007158 < baseStart_1007158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007184 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 3, 4]
def baseStart_1007184 : Nat := 118140960795 + 1007184 * 2 ^ 59
def prefixEnd_1007184 : Nat := 4983230072969 + 3 ^ 40 * 1007184 * 2
def baseEnd_1007184 : Nat := 172389833172697540556017

theorem tailTrace_1007184 : CollatzResearch.WordTrace tailWord_1007184 prefixEnd_1007184 172389833172697540556017 := by
  unfold tailWord_1007184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18367509191575928088814303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24490012255434570785085737 18367509191575928088814303)
  ·
    refine ⟨27551263787363892133221455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18367509191575928088814303 27551263787363892133221455)
    ·
      refine ⟨41326895681045838199832183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27551263787363892133221455 41326895681045838199832183)
      ·
        refine ⟨61990343521568757299748275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41326895681045838199832183 61990343521568757299748275)
        ·
          refine ⟨92985515282353135949622413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61990343521568757299748275 92985515282353135949622413)
          ·
            refine ⟨34869568230882425981108405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92985515282353135949622413 34869568230882425981108405)
            ·
              refine ⟨3269022021645227435728913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34869568230882425981108405 3269022021645227435728913)
              ·
                refine ⟨2451766516233920576796685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3269022021645227435728913 2451766516233920576796685)
                ·
                  refine ⟨919412443587720216298757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2451766516233920576796685 919412443587720216298757)
                  ·
                    refine ⟨172389833172697540556017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 919412443587720216298757 172389833172697540556017)
                    ·
                      rfl

theorem cell23_1007184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 4].length) (baseStart_1007184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007184 prefixEnd_1007184 := by exact prefixLift 1007184
  have htrace : WordTrace (prefixWord ++ tailWord_1007184) baseStart_1007184 baseEnd_1007184 := by
    simpa [prefixWord, tailWord_1007184, baseEnd_1007184] using wordTrace_append hprefix tailTrace_1007184
  have hstable : (prefixWord ++ tailWord_1007184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007184).length < 2 ^ (prefixWord ++ tailWord_1007184).sum := by decide
  have hdescent : baseEnd_1007184 < baseStart_1007184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007191 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_1007191 : Nat := 118140960795 + 1007191 * 2 ^ 59
def prefixEnd_1007191 : Nat := 4983230072969 + 3 ^ 40 * 1007191 * 2
def baseEnd_1007191 : Nat := 517173093882674094280519

theorem tailTrace_1007191 : CollatzResearch.WordTrace tailWord_1007191 prefixEnd_1007191 517173093882674094280519 := by
  unfold tailWord_1007191
  simp only [CollatzResearch.WordTrace]
  refine ⟨36735273694126496373133427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24490182462750997582088951 36735273694126496373133427)
  ·
    refine ⟨55102910541189744559700141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36735273694126496373133427 55102910541189744559700141)
    ·
      refine ⟨20663591452946154209887553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55102910541189744559700141 20663591452946154209887553)
      ·
        refine ⟨15497693589709615657415665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20663591452946154209887553 15497693589709615657415665)
        ·
          refine ⟨11623270192282211743061749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15497693589709615657415665 11623270192282211743061749)
          ·
            refine ⟨1089681580526457350912039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11623270192282211743061749 1089681580526457350912039)
            ·
              refine ⟨1634522370789686026368059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089681580526457350912039 1634522370789686026368059)
              ·
                refine ⟨2451783556184529039552089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634522370789686026368059 2451783556184529039552089)
                ·
                  refine ⟨1838837667138396779664067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2451783556184529039552089 1838837667138396779664067)
                  ·
                    refine ⟨2758256500707595169496101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1838837667138396779664067 2758256500707595169496101)
                    ·
                      refine ⟨517173093882674094280519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2758256500707595169496101 517173093882674094280519)
                      ·
                        rfl

theorem cell23_1007191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_1007191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007191 prefixEnd_1007191 := by exact prefixLift 1007191
  have htrace : WordTrace (prefixWord ++ tailWord_1007191) baseStart_1007191 baseEnd_1007191 := by
    simpa [prefixWord, tailWord_1007191, baseEnd_1007191] using wordTrace_append hprefix tailTrace_1007191
  have hstable : (prefixWord ++ tailWord_1007191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007191).length < 2 ^ (prefixWord ++ tailWord_1007191).sum := by decide
  have hdescent : baseEnd_1007191 < baseStart_1007191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007218 : List Nat := [3, 2, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_1007218 : Nat := 118140960795 + 1007218 * 2 ^ 59
def prefixEnd_1007218 : Nat := 4983230072969 + 3 ^ 40 * 1007218 * 2
def baseEnd_1007218 : Nat := 172395652620115162880965

theorem tailTrace_1007218 : CollatzResearch.WordTrace tailWord_1007218 prefixEnd_1007218 172395652620115162880965 := by
  unfold tailWord_1007218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9184064616257169996091577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24490838976685786656244205 9184064616257169996091577)
  ·
    refine ⟨6888048462192877497068683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9184064616257169996091577 6888048462192877497068683)
    ·
      refine ⟨10332072693289316245603025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6888048462192877497068683 10332072693289316245603025)
      ·
        refine ⟨7749054519966987184202269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10332072693289316245603025 7749054519966987184202269)
        ·
          refine ⟨2905895444987620194075851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7749054519966987184202269 2905895444987620194075851)
          ·
            refine ⟨4358843167481430291113777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2905895444987620194075851 4358843167481430291113777)
            ·
              refine ⟨3269132375611072718335333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4358843167481430291113777 3269132375611072718335333)
              ·
                refine ⟨612962320427076134687875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3269132375611072718335333 612962320427076134687875)
                ·
                  refine ⟨919443480640614202031813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612962320427076134687875 919443480640614202031813)
                  ·
                    refine ⟨172395652620115162880965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 919443480640614202031813 172395652620115162880965)
                    ·
                      rfl

theorem cell23_1007218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_1007218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007218 prefixEnd_1007218 := by exact prefixLift 1007218
  have htrace : WordTrace (prefixWord ++ tailWord_1007218) baseStart_1007218 baseEnd_1007218 := by
    simpa [prefixWord, tailWord_1007218, baseEnd_1007218] using wordTrace_append hprefix tailTrace_1007218
  have hstable : (prefixWord ++ tailWord_1007218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007218).length < 2 ^ (prefixWord ++ tailWord_1007218).sum := by decide
  have hdescent : baseEnd_1007218 < baseStart_1007218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007241 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 3]
def baseStart_1007241 : Nat := 118140960795 + 1007241 * 2 ^ 59
def prefixEnd_1007241 : Nat := 4983230072969 + 3 ^ 40 * 1007241 * 2
def baseEnd_1007241 : Nat := 517198767915398898655289

theorem tailTrace_1007241 : CollatzResearch.WordTrace tailWord_1007241 prefixEnd_1007241 517198767915398898655289 := by
  unfold tailWord_1007241
  simp only [CollatzResearch.WordTrace]
  refine ⟨36737097343945354912453577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24491398229296903274969051 36737097343945354912453577)
  ·
    refine ⟨27552823007959016184340183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36737097343945354912453577 27552823007959016184340183)
    ·
      refine ⟨41329234511938524276510275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27552823007959016184340183 41329234511938524276510275)
      ·
        refine ⟨61993851767907786414765413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41329234511938524276510275 61993851767907786414765413)
        ·
          refine ⟨11623847206482709952768515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61993851767907786414765413 11623847206482709952768515)
          ·
            refine ⟨17435770809724064929152773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623847206482709952768515 17435770809724064929152773)
            ·
              refine ⟨3269207026823262174216145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17435770809724064929152773 3269207026823262174216145)
              ·
                refine ⟨2451905270117446630662109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3269207026823262174216145 2451905270117446630662109)
                ·
                  refine ⟨919464476294042486498291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2451905270117446630662109 919464476294042486498291)
                  ·
                    refine ⟨1379196714441063729747437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 919464476294042486498291 1379196714441063729747437)
                    ·
                      refine ⟨517198767915398898655289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1379196714441063729747437 517198767915398898655289)
                      ·
                        rfl

theorem cell23_1007241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 3].length) (baseStart_1007241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007241 prefixEnd_1007241 := by exact prefixLift 1007241
  have htrace : WordTrace (prefixWord ++ tailWord_1007241) baseStart_1007241 baseEnd_1007241 := by
    simpa [prefixWord, tailWord_1007241, baseEnd_1007241] using wordTrace_append hprefix tailTrace_1007241
  have hstable : (prefixWord ++ tailWord_1007241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007241).length < 2 ^ (prefixWord ++ tailWord_1007241).sum := by decide
  have hdescent : baseEnd_1007241 < baseStart_1007241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007252 : List Nat := [2, 4, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1007252 : Nat := 118140960795 + 1007252 * 2 ^ 59
def prefixEnd_1007252 : Nat := 4983230072969 + 3 ^ 40 * 1007252 * 2
def baseEnd_1007252 : Nat := 172401472067532785205913

theorem tailTrace_1007252 : CollatzResearch.WordTrace tailWord_1007252 prefixEnd_1007252 172401472067532785205913 := by
  unfold tailWord_1007252
  simp only [CollatzResearch.WordTrace]
  refine ⟨18368749273452751895552005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24491665697937002527402673 18368749273452751895552005)
  ·
    refine ⟨3444140488772390980416001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18368749273452751895552005 3444140488772390980416001)
    ·
      refine ⟨2583105366579293235312001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3444140488772390980416001 2583105366579293235312001)
      ·
        refine ⟨1937329024934469926484001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2583105366579293235312001 1937329024934469926484001)
        ·
          refine ⟨1452996768700852444863001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1937329024934469926484001 1452996768700852444863001)
          ·
            refine ⟨1089747576525639333647251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452996768700852444863001 1089747576525639333647251)
            ·
              refine ⟨1634621364788459000470877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089747576525639333647251 1634621364788459000470877)
              ·
                refine ⟨612983011795672125176579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1634621364788459000470877 612983011795672125176579)
                ·
                  refine ⟨919474517693508187764869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612983011795672125176579 919474517693508187764869)
                  ·
                    refine ⟨172401472067532785205913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 919474517693508187764869 172401472067532785205913)
                    ·
                      rfl

theorem cell23_1007252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1007252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007252 prefixEnd_1007252 := by exact prefixLift 1007252
  have htrace : WordTrace (prefixWord ++ tailWord_1007252) baseStart_1007252 baseEnd_1007252 := by
    simpa [prefixWord, tailWord_1007252, baseEnd_1007252] using wordTrace_append hprefix tailTrace_1007252
  have hstable : (prefixWord ++ tailWord_1007252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007252).length < 2 ^ (prefixWord ++ tailWord_1007252).sum := by decide
  have hdescent : baseEnd_1007252 < baseStart_1007252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007268 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_1007268 : Nat := 118140960795 + 1007268 * 2 ^ 59
def prefixEnd_1007268 : Nat := 4983230072969 + 3 ^ 40 * 1007268 * 2
def baseEnd_1007268 : Nat := 517212631893070293017665

theorem tailTrace_1007268 : CollatzResearch.WordTrace tailWord_1007268 prefixEnd_1007268 517212631893070293017665 := by
  unfold tailWord_1007268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18369041057423769261843229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24492054743231692349124305 18369041057423769261843229)
  ·
    refine ⟨6888390396533913473191211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18369041057423769261843229 6888390396533913473191211)
    ·
      refine ⟨10332585594800870209786817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6888390396533913473191211 10332585594800870209786817)
      ·
        refine ⟨7749439196100652657340113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10332585594800870209786817 7749439196100652657340113)
        ·
          refine ⟨5812079397075489493005085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7749439196100652657340113 5812079397075489493005085)
          ·
            refine ⟨2179529773903308559876907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5812079397075489493005085 2179529773903308559876907)
            ·
              refine ⟨3269294660854962839815361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179529773903308559876907 3269294660854962839815361)
              ·
                refine ⟨2451970995641222129861521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3269294660854962839815361 2451970995641222129861521)
                ·
                  refine ⟨1838978246730916597396141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2451970995641222129861521 1838978246730916597396141)
                  ·
                    refine ⟨689616842524093724023553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1838978246730916597396141 689616842524093724023553)
                    ·
                      refine ⟨517212631893070293017665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689616842524093724023553 517212631893070293017665)
                      ·
                        rfl

theorem cell23_1007268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_1007268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007268 prefixEnd_1007268 := by exact prefixLift 1007268
  have htrace : WordTrace (prefixWord ++ tailWord_1007268) baseStart_1007268 baseEnd_1007268 := by
    simpa [prefixWord, tailWord_1007268, baseEnd_1007268] using wordTrace_append hprefix tailTrace_1007268
  have hstable : (prefixWord ++ tailWord_1007268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007268).length < 2 ^ (prefixWord ++ tailWord_1007268).sum := by decide
  have hdescent : baseEnd_1007268 < baseStart_1007268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007302 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1007302 : Nat := 118140960795 + 1007302 * 2 ^ 59
def prefixEnd_1007302 : Nat := 4983230072969 + 3 ^ 40 * 1007302 * 2
def baseEnd_1007302 : Nat := 517230090235323159992509

theorem tailTrace_1007302 : CollatzResearch.WordTrace tailWord_1007302 prefixEnd_1007302 517230090235323159992509 := by
  unfold tailWord_1007302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148103818647636322825755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24492881464482908220282773 1148103818647636322825755)
  ·
    refine ⟨1722155727971454484238633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1148103818647636322825755 1722155727971454484238633)
    ·
      refine ⟨1291616795978590863178975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1722155727971454484238633 1291616795978590863178975)
      ·
        refine ⟨1937425193967886294768463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291616795978590863178975 1937425193967886294768463)
        ·
          refine ⟨2906137790951829442152695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937425193967886294768463 2906137790951829442152695)
          ·
            refine ⟨4359206686427744163229043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906137790951829442152695 4359206686427744163229043)
            ·
              refine ⟨6538810029641616244843565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359206686427744163229043 6538810029641616244843565)
              ·
                refine ⟨2452053761115606091816337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6538810029641616244843565 2452053761115606091816337)
                ·
                  refine ⟨1839040320836704568862253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2452053761115606091816337 1839040320836704568862253)
                  ·
                    refine ⟨689640120313764213323345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839040320836704568862253 689640120313764213323345)
                    ·
                      refine ⟨517230090235323159992509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689640120313764213323345 517230090235323159992509)
                      ·
                        rfl

theorem cell23_1007302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1007302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007302 prefixEnd_1007302 := by exact prefixLift 1007302
  have htrace : WordTrace (prefixWord ++ tailWord_1007302) baseStart_1007302 baseEnd_1007302 := by
    simpa [prefixWord, tailWord_1007302, baseEnd_1007302] using wordTrace_append hprefix tailTrace_1007302
  have hstable : (prefixWord ++ tailWord_1007302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007302).length < 2 ^ (prefixWord ++ tailWord_1007302).sum := by decide
  have hdescent : baseEnd_1007302 < baseStart_1007302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007354 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1007354 : Nat := 118140960795 + 1007354 * 2 ^ 59
def prefixEnd_1007354 : Nat := 4983230072969 + 3 ^ 40 * 1007354 * 2
def baseEnd_1007354 : Nat := 517256791229356956542269

theorem tailTrace_1007354 : CollatzResearch.WordTrace tailWord_1007354 prefixEnd_1007354 517256791229356956542269 := by
  unfold tailWord_1007354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9185304698133993802829279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24494145861690650140878077 9185304698133993802829279)
  ·
    refine ⟨13777957047200990704243919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9185304698133993802829279 13777957047200990704243919)
    ·
      refine ⟨20666935570801486056365879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13777957047200990704243919 20666935570801486056365879)
      ·
        refine ⟨31000403356202229084548819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20666935570801486056365879 31000403356202229084548819)
        ·
          refine ⟨46500605034303343626823229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31000403356202229084548819 46500605034303343626823229)
          ·
            refine ⟨17437726887863753860058711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46500605034303343626823229 17437726887863753860058711)
            ·
              refine ⟨26156590331795630790088067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17437726887863753860058711 26156590331795630790088067)
              ·
                refine ⟨39234885497693446185132101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26156590331795630790088067 39234885497693446185132101)
                ·
                  refine ⟨7356541030817521159712269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39234885497693446185132101 7356541030817521159712269)
                  ·
                    refine ⟨2758702886556570434892101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7356541030817521159712269 2758702886556570434892101)
                    ·
                      refine ⟨517256791229356956542269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2758702886556570434892101 517256791229356956542269)
                      ·
                        rfl

theorem cell23_1007354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1007354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007354 prefixEnd_1007354 := by exact prefixLift 1007354
  have htrace : WordTrace (prefixWord ++ tailWord_1007354) baseStart_1007354 baseEnd_1007354 := by
    simpa [prefixWord, tailWord_1007354, baseEnd_1007354] using wordTrace_append hprefix tailTrace_1007354
  have hstable : (prefixWord ++ tailWord_1007354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007354).length < 2 ^ (prefixWord ++ tailWord_1007354).sum := by decide
  have hdescent : baseEnd_1007354 < baseStart_1007354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007366 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1007366 : Nat := 118140960795 + 1007366 * 2 ^ 59
def prefixEnd_1007366 : Nat := 4983230072969 + 3 ^ 40 * 1007366 * 2
def baseEnd_1007366 : Nat := 517262952997210909592215

theorem tailTrace_1007366 : CollatzResearch.WordTrace tailWord_1007366 prefixEnd_1007366 517262952997210909592215 := by
  unfold tailWord_1007366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148176764640390664398561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24494437645661667507169301 1148176764640390664398561)
  ·
    refine ⟨861132573480292998298921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1148176764640390664398561 861132573480292998298921)
    ·
      refine ⟨645849430110219748724191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 861132573480292998298921 645849430110219748724191)
      ·
        refine ⟨968774145165329623086287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645849430110219748724191 968774145165329623086287)
        ·
          refine ⟨1453161217747994434629431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968774145165329623086287 1453161217747994434629431)
          ·
            refine ⟨2179741826621991651944147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453161217747994434629431 2179741826621991651944147)
            ·
              refine ⟨3269612739932987477916221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179741826621991651944147 3269612739932987477916221)
              ·
                refine ⟨1226104777474870304218583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3269612739932987477916221 1226104777474870304218583)
                ·
                  refine ⟨1839157166212305456327875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226104777474870304218583 1839157166212305456327875)
                  ·
                    refine ⟨2758735749318458184491813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1839157166212305456327875 2758735749318458184491813)
                    ·
                      refine ⟨517262952997210909592215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2758735749318458184491813 517262952997210909592215)
                      ·
                        rfl

theorem cell23_1007366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1007366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007366 prefixEnd_1007366 := by exact prefixLift 1007366
  have htrace : WordTrace (prefixWord ++ tailWord_1007366) baseStart_1007366 baseEnd_1007366 := by
    simpa [prefixWord, tailWord_1007366, baseEnd_1007366] using wordTrace_append hprefix tailTrace_1007366
  have hstable : (prefixWord ++ tailWord_1007366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007366).length < 2 ^ (prefixWord ++ tailWord_1007366).sum := by decide
  have hdescent : baseEnd_1007366 < baseStart_1007366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007441 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 4, 5]
def baseStart_1007441 : Nat := 118140960795 + 1007441 * 2 ^ 59
def prefixEnd_1007441 : Nat := 4983230072969 + 3 ^ 40 * 1007441 * 2
def baseEnd_1007441 : Nat := 172433821348766038718123

theorem tailTrace_1007441 : CollatzResearch.WordTrace tailWord_1007441 prefixEnd_1007441 172433821348766038718123 := by
  unfold tailWord_1007441
  simp only [CollatzResearch.WordTrace]
  refine ⟨36744391943220789069734177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24496261295480526046489451 36744391943220789069734177)
  ·
    refine ⟨27558293957415591802300633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36744391943220789069734177 27558293957415591802300633)
    ·
      refine ⟨20668720468061693851725475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27558293957415591802300633 20668720468061693851725475)
      ·
        refine ⟨31003080702092540777588213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20668720468061693851725475 31003080702092540777588213)
        ·
          refine ⟨2906538815821175697898895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31003080702092540777588213 2906538815821175697898895)
          ·
            refine ⟨4359808223731763546848343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906538815821175697898895 4359808223731763546848343)
            ·
              refine ⟨6539712335597645320272515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359808223731763546848343 6539712335597645320272515)
              ·
                refine ⟨9809568503396467980408773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539712335597645320272515 9809568503396467980408773)
                ·
                  refine ⟨1839294094386837746326645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9809568503396467980408773 1839294094386837746326645)
                  ·
                    refine ⟨172433821348766038718123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1839294094386837746326645 172433821348766038718123)
                    ·
                      rfl

theorem cell23_1007441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_1007441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007441 prefixEnd_1007441 := by exact prefixLift 1007441
  have htrace : WordTrace (prefixWord ++ tailWord_1007441) baseStart_1007441 baseEnd_1007441 := by
    simpa [prefixWord, tailWord_1007441, baseEnd_1007441] using wordTrace_append hprefix tailTrace_1007441
  have hstable : (prefixWord ++ tailWord_1007441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007441).length < 2 ^ (prefixWord ++ tailWord_1007441).sum := by decide
  have hdescent : baseEnd_1007441 < baseStart_1007441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007445 : List Nat := [1, 3, 2, 2, 2, 3, 3, 2, 5]
def baseStart_1007445 : Nat := 118140960795 + 1007445 * 2 ^ 59
def prefixEnd_1007445 : Nat := 4983230072969 + 3 ^ 40 * 1007445 * 2
def baseEnd_1007445 : Nat := 57478168663212900056039

theorem tailTrace_1007445 : CollatzResearch.WordTrace tailWord_1007445 prefixEnd_1007445 57478168663212900056039 := by
  unfold tailWord_1007445
  simp only [CollatzResearch.WordTrace]
  refine ⟨36744537835206297752879789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24496358556804198501919859 36744537835206297752879789)
  ·
    refine ⟨13779201688202361657329921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36744537835206297752879789 13779201688202361657329921)
    ·
      refine ⟨10334401266151771242997441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13779201688202361657329921 10334401266151771242997441)
      ·
        refine ⟨7750800949613828432248081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10334401266151771242997441 7750800949613828432248081)
        ·
          refine ⟨5813100712210371324186061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7750800949613828432248081 5813100712210371324186061)
          ·
            refine ⟨2179912767078889246569773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5813100712210371324186061 2179912767078889246569773)
            ·
              refine ⟨817467287654583467463665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2179912767078889246569773 817467287654583467463665)
              ·
                refine ⟨613100465740937600597749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817467287654583467463665 613100465740937600597749)
                ·
                  refine ⟨57478168663212900056039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 613100465740937600597749 57478168663212900056039)
                  ·
                    rfl

theorem cell23_1007445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_1007445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007445 prefixEnd_1007445 := by exact prefixLift 1007445
  have htrace : WordTrace (prefixWord ++ tailWord_1007445) baseStart_1007445 baseEnd_1007445 := by
    simpa [prefixWord, tailWord_1007445, baseEnd_1007445] using wordTrace_append hprefix tailTrace_1007445
  have hstable : (prefixWord ++ tailWord_1007445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007445).length < 2 ^ (prefixWord ++ tailWord_1007445).sum := by decide
  have hdescent : baseEnd_1007445 < baseStart_1007445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007461 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1007461 : Nat := 118140960795 + 1007461 * 2 ^ 59
def prefixEnd_1007461 : Nat := 4983230072969 + 3 ^ 40 * 1007461 * 2
def baseEnd_1007461 : Nat := 517311733659388037904277

theorem tailTrace_1007461 : CollatzResearch.WordTrace tailWord_1007461 prefixEnd_1007461 517311733659388037904277 := by
  unfold tailWord_1007461
  simp only [CollatzResearch.WordTrace]
  refine ⟨36745121403148332485462237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24496747602098888323641491 36745121403148332485462237)
  ·
    refine ⟨13779420526180624682048339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36745121403148332485462237 13779420526180624682048339)
    ·
      refine ⟨20669130789270937023072509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13779420526180624682048339 20669130789270937023072509)
      ·
        refine ⟨7750924045976601383652191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20669130789270937023072509 7750924045976601383652191)
        ·
          refine ⟨11626386068964902075478287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7750924045976601383652191 11626386068964902075478287)
          ·
            refine ⟨17439579103447353113217431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626386068964902075478287 17439579103447353113217431)
            ·
              refine ⟨26159368655171029669826147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17439579103447353113217431 26159368655171029669826147)
              ·
                refine ⟨39239052982756544504739221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26159368655171029669826147 39239052982756544504739221)
                ·
                  refine ⟨1839330608566713023659651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39239052982756544504739221 1839330608566713023659651)
                  ·
                    refine ⟨2758995912850069535489477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1839330608566713023659651 2758995912850069535489477)
                    ·
                      refine ⟨517311733659388037904277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2758995912850069535489477 517311733659388037904277)
                      ·
                        rfl

theorem cell23_1007461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1007461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007461 prefixEnd_1007461 := by exact prefixLift 1007461
  have htrace : WordTrace (prefixWord ++ tailWord_1007461) baseStart_1007461 baseEnd_1007461 := by
    simpa [prefixWord, tailWord_1007461, baseEnd_1007461] using wordTrace_append hprefix tailTrace_1007461
  have hstable : (prefixWord ++ tailWord_1007461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007461).length < 2 ^ (prefixWord ++ tailWord_1007461).sum := by decide
  have hdescent : baseEnd_1007461 < baseStart_1007461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007512 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1007512 : Nat := 118140960795 + 1007512 * 2 ^ 59
def prefixEnd_1007512 : Nat := 4983230072969 + 3 ^ 40 * 1007512 * 2
def baseEnd_1007512 : Nat := 517337921172767338366543

theorem tailTrace_1007512 : CollatzResearch.WordTrace tailWord_1007512 prefixEnd_1007512 517337921172767338366543 := by
  unfold tailWord_1007512
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373490762981784097784395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24497987683975712130379193 18373490762981784097784395)
  ·
    refine ⟨27560236144472676146676593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18373490762981784097784395 27560236144472676146676593)
    ·
      refine ⟨20670177108354507110007445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27560236144472676146676593 20670177108354507110007445)
      ·
        refine ⟨968914551954117520781599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20670177108354507110007445 968914551954117520781599)
        ·
          refine ⟨1453371827931176281172399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968914551954117520781599 1453371827931176281172399)
          ·
            refine ⟨2180057741896764421758599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453371827931176281172399 2180057741896764421758599)
            ·
              refine ⟨3270086612845146632637899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180057741896764421758599 3270086612845146632637899)
              ·
                refine ⟨4905129919267719948956849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270086612845146632637899 4905129919267719948956849)
                ·
                  refine ⟨3678847439450789961717637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4905129919267719948956849 3678847439450789961717637)
                  ·
                    refine ⟨689783894897023117822057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678847439450789961717637 689783894897023117822057)
                    ·
                      refine ⟨517337921172767338366543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689783894897023117822057 517337921172767338366543)
                      ·
                        rfl

theorem cell23_1007512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1007512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007512 prefixEnd_1007512 := by exact prefixLift 1007512
  have htrace : WordTrace (prefixWord ++ tailWord_1007512) baseStart_1007512 baseEnd_1007512 := by
    simpa [prefixWord, tailWord_1007512, baseEnd_1007512] using wordTrace_append hprefix tailTrace_1007512
  have hstable : (prefixWord ++ tailWord_1007512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007512).length < 2 ^ (prefixWord ++ tailWord_1007512).sum := by decide
  have hdescent : baseEnd_1007512 < baseStart_1007512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007562 : List Nat := [3, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_1007562 : Nat := 118140960795 + 1007562 * 2 ^ 59
def prefixEnd_1007562 : Nat := 4983230072969 + 3 ^ 40 * 1007562 * 2
def baseEnd_1007562 : Nat := 517363595205492142741313

theorem tailTrace_1007562 : CollatzResearch.WordTrace tailWord_1007562 prefixEnd_1007562 517363595205492142741313 := by
  unfold tailWord_1007562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187201293945606683722235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24499203450521617823259293 9187201293945606683722235)
  ·
    refine ⟨13780801940918410025583353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9187201293945606683722235 13780801940918410025583353)
    ·
      refine ⟨10335601455688807519187515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13780801940918410025583353 10335601455688807519187515)
      ·
        refine ⟨15503402183533211278781273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335601455688807519187515 15503402183533211278781273)
        ·
          refine ⟨11627551637649908459085955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15503402183533211278781273 11627551637649908459085955)
          ·
            refine ⟨17441327456474862688628933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11627551637649908459085955 17441327456474862688628933)
            ·
              refine ⟨3270248898089036754117925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17441327456474862688628933 3270248898089036754117925)
              ·
                refine ⟨613171668391694391397111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3270248898089036754117925 613171668391694391397111)
                ·
                  refine ⟨919757502587541587095667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613171668391694391397111 919757502587541587095667)
                  ·
                    refine ⟨1379636253881312380643501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 919757502587541587095667 1379636253881312380643501)
                    ·
                      refine ⟨517363595205492142741313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1379636253881312380643501 517363595205492142741313)
                      ·
                        rfl

theorem cell23_1007562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_1007562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007562 prefixEnd_1007562 := by exact prefixLift 1007562
  have htrace : WordTrace (prefixWord ++ tailWord_1007562) baseStart_1007562 baseEnd_1007562 := by
    simpa [prefixWord, tailWord_1007562, baseEnd_1007562] using wordTrace_append hprefix tailTrace_1007562
  have hstable : (prefixWord ++ tailWord_1007562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007562).length < 2 ^ (prefixWord ++ tailWord_1007562).sum := by decide
  have hdescent : baseEnd_1007562 < baseStart_1007562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007636 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1007636 : Nat := 118140960795 + 1007636 * 2 ^ 59
def prefixEnd_1007636 : Nat := 4983230072969 + 3 ^ 40 * 1007636 * 2
def baseEnd_1007636 : Nat := 517401592773924853215973

theorem tailTrace_1007636 : CollatzResearch.WordTrace tailWord_1007636 prefixEnd_1007636 517401592773924853215973 := by
  unfold tailWord_1007636
  simp only [CollatzResearch.WordTrace]
  refine ⟨18375752088757168686541381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24501002785009558248721841 18375752088757168686541381)
  ·
    refine ⟨3445453516641969128726509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18375752088757168686541381 3445453516641969128726509)
    ·
      refine ⟨1292045068740738423272441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3445453516641969128726509 1292045068740738423272441)
      ·
        refine ⟨969033801555553817454331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1292045068740738423272441 969033801555553817454331)
        ·
          refine ⟨1453550702333330726181497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969033801555553817454331 1453550702333330726181497)
          ·
            refine ⟨1090163026749998044636123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453550702333330726181497 1090163026749998044636123)
            ·
              refine ⟨1635244540124997066954185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090163026749998044636123 1635244540124997066954185)
              ·
                refine ⟨1226433405093747800215639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1635244540124997066954185 1226433405093747800215639)
                ·
                  refine ⟨1839650107640621700323459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226433405093747800215639 1839650107640621700323459)
                  ·
                    refine ⟨2759475161460932550485189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1839650107640621700323459 2759475161460932550485189)
                    ·
                      refine ⟨517401592773924853215973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2759475161460932550485189 517401592773924853215973)
                      ·
                        rfl

theorem cell23_1007636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1007636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007636 prefixEnd_1007636 := by exact prefixLift 1007636
  have htrace : WordTrace (prefixWord ++ tailWord_1007636) baseStart_1007636 baseEnd_1007636 := by
    simpa [prefixWord, tailWord_1007636, baseEnd_1007636] using wordTrace_append hprefix tailTrace_1007636
  have hstable : (prefixWord ++ tailWord_1007636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007636).length < 2 ^ (prefixWord ++ tailWord_1007636).sum := by decide
  have hdescent : baseEnd_1007636 < baseStart_1007636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007639 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1007639 : Nat := 118140960795 + 1007639 * 2 ^ 59
def prefixEnd_1007639 : Nat := 4983230072969 + 3 ^ 40 * 1007639 * 2
def baseEnd_1007639 : Nat := 517403133215888341478459

theorem tailTrace_1007639 : CollatzResearch.WordTrace tailWord_1007639 prefixEnd_1007639 517403133215888341478459 := by
  unfold tailWord_1007639
  simp only [CollatzResearch.WordTrace]
  refine ⟨36751613596503468885441971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24501075731002312590294647 36751613596503468885441971)
  ·
    refine ⟨55127420394755203328162957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36751613596503468885441971 55127420394755203328162957)
    ·
      refine ⟨20672782648033201248061109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55127420394755203328162957 20672782648033201248061109)
      ·
        refine ⟨1938073373253112617005729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20672782648033201248061109 1938073373253112617005729)
        ·
          refine ⟨1453555029939834462754297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1938073373253112617005729 1453555029939834462754297)
          ·
            refine ⟨1090166272454875847065723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453555029939834462754297 1090166272454875847065723)
            ·
              refine ⟨1635249408682313770598585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090166272454875847065723 1635249408682313770598585)
              ·
                refine ⟨1226437056511735327948939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1635249408682313770598585 1226437056511735327948939)
                ·
                  refine ⟨1839655584767602991923409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226437056511735327948939 1839655584767602991923409)
                  ·
                    refine ⟨1379741688575702243942557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1839655584767602991923409 1379741688575702243942557)
                    ·
                      refine ⟨517403133215888341478459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1379741688575702243942557 517403133215888341478459)
                      ·
                        rfl

theorem cell23_1007639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1007639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007639 prefixEnd_1007639 := by exact prefixLift 1007639
  have htrace : WordTrace (prefixWord ++ tailWord_1007639) baseStart_1007639 baseEnd_1007639 := by
    simpa [prefixWord, tailWord_1007639, baseEnd_1007639] using wordTrace_append hprefix tailTrace_1007639
  have hstable : (prefixWord ++ tailWord_1007639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007639).length < 2 ^ (prefixWord ++ tailWord_1007639).sum := by decide
  have hdescent : baseEnd_1007639 < baseStart_1007639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007641 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_1007641 : Nat := 118140960795 + 1007641 * 2 ^ 59
def prefixEnd_1007641 : Nat := 4983230072969 + 3 ^ 40 * 1007641 * 2
def baseEnd_1007641 : Nat := 517404160177197333653449

theorem tailTrace_1007641 : CollatzResearch.WordTrace tailWord_1007641 prefixEnd_1007641 517404160177197333653449 := by
  unfold tailWord_1007641
  simp only [CollatzResearch.WordTrace]
  refine ⟨36751686542496223227014777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24501124361664148818009851 36751686542496223227014777)
  ·
    refine ⟨27563764906872167420261083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36751686542496223227014777 27563764906872167420261083)
    ·
      refine ⟨41345647360308251130391625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27563764906872167420261083 41345647360308251130391625)
      ·
        refine ⟨31009235520231188347793719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41345647360308251130391625 31009235520231188347793719)
        ·
          refine ⟨46513853280346782521690579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31009235520231188347793719 46513853280346782521690579)
          ·
            refine ⟨69770779920520173782535869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46513853280346782521690579 69770779920520173782535869)
            ·
              refine ⟨26164042470195065168450951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69770779920520173782535869 26164042470195065168450951)
              ·
                refine ⟨39246063705292597752676427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26164042470195065168450951 39246063705292597752676427)
                ·
                  refine ⟨58869095557938896629014641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39246063705292597752676427 58869095557938896629014641)
                  ·
                    refine ⟨44151821668454172471760981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58869095557938896629014641 44151821668454172471760981)
                    ·
                      refine ⟨517404160177197333653449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 44151821668454172471760981 517404160177197333653449)
                      ·
                        rfl

theorem cell23_1007641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_1007641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007641 prefixEnd_1007641 := by exact prefixLift 1007641
  have htrace : WordTrace (prefixWord ++ tailWord_1007641) baseStart_1007641 baseEnd_1007641 := by
    simpa [prefixWord, tailWord_1007641, baseEnd_1007641] using wordTrace_append hprefix tailTrace_1007641
  have hstable : (prefixWord ++ tailWord_1007641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007641).length < 2 ^ (prefixWord ++ tailWord_1007641).sum := by decide
  have hdescent : baseEnd_1007641 < baseStart_1007641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007652 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1007652 : Nat := 118140960795 + 1007652 * 2 ^ 59
def prefixEnd_1007652 : Nat := 4983230072969 + 3 ^ 40 * 1007652 * 2
def baseEnd_1007652 : Nat := 517409808464396790615899

theorem tailTrace_1007652 : CollatzResearch.WordTrace tailWord_1007652 prefixEnd_1007652 517409808464396790615899 := by
  unfold tailWord_1007652
  simp only [CollatzResearch.WordTrace]
  refine ⟨18376043872728186052832605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24501391830304248070443473 18376043872728186052832605)
  ·
    refine ⟨6891016452273069769812227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18376043872728186052832605 6891016452273069769812227)
    ·
      refine ⟨10336524678409604654718341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6891016452273069769812227 10336524678409604654718341)
      ·
        refine ⟨1938098377201800872759689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10336524678409604654718341 1938098377201800872759689)
        ·
          refine ⟨1453573782901350654569767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1938098377201800872759689 1453573782901350654569767)
          ·
            refine ⟨2180360674352025981854651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453573782901350654569767 2180360674352025981854651)
            ·
              refine ⟨3270541011528038972781977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180360674352025981854651 3270541011528038972781977)
              ·
                refine ⟨2452905758646029229586483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270541011528038972781977 2452905758646029229586483)
                ·
                  refine ⟨3679358637969043844379725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452905758646029229586483 3679358637969043844379725)
                  ·
                    refine ⟨1379759489238391441642397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679358637969043844379725 1379759489238391441642397)
                    ·
                      refine ⟨517409808464396790615899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1379759489238391441642397 517409808464396790615899)
                      ·
                        rfl

theorem cell23_1007652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1007652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007652 prefixEnd_1007652 := by exact prefixLift 1007652
  have htrace : WordTrace (prefixWord ++ tailWord_1007652) baseStart_1007652 baseEnd_1007652 := by
    simpa [prefixWord, tailWord_1007652, baseEnd_1007652] using wordTrace_append hprefix tailTrace_1007652
  have hstable : (prefixWord ++ tailWord_1007652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007652).length < 2 ^ (prefixWord ++ tailWord_1007652).sum := by decide
  have hdescent : baseEnd_1007652 < baseStart_1007652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007656 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1007656 : Nat := 118140960795 + 1007656 * 2 ^ 59
def prefixEnd_1007656 : Nat := 4983230072969 + 3 ^ 40 * 1007656 * 2
def baseEnd_1007656 : Nat := 517411862387014774965881

theorem tailTrace_1007656 : CollatzResearch.WordTrace tailWord_1007656 prefixEnd_1007656 517411862387014774965881 := by
  unfold tailWord_1007656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18376116818720940394405411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24501489091627920525873881 18376116818720940394405411)
  ·
    refine ⟨27564175228081410591608117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18376116818720940394405411 27564175228081410591608117)
    ·
      refine ⟨2584141427632632242963261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27564175228081410591608117 2584141427632632242963261)
      ·
        refine ⟨969053035362237091111223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2584141427632632242963261 969053035362237091111223)
        ·
          refine ⟨1453579553043355636666835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969053035362237091111223 1453579553043355636666835)
          ·
            refine ⟨2180369329565033455000253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1453579553043355636666835 2180369329565033455000253)
            ·
              refine ⟨817638498586887545625095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2180369329565033455000253 817638498586887545625095)
              ·
                refine ⟨1226457747880331318437643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817638498586887545625095 1226457747880331318437643)
                ·
                  refine ⟨1839686621820496977656465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226457747880331318437643 1839686621820496977656465)
                  ·
                    refine ⟨1379764966365372733242349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1839686621820496977656465 1379764966365372733242349)
                    ·
                      refine ⟨517411862387014774965881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1379764966365372733242349 517411862387014774965881)
                      ·
                        rfl

theorem cell23_1007656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1007656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007656 prefixEnd_1007656 := by exact prefixLift 1007656
  have htrace : WordTrace (prefixWord ++ tailWord_1007656) baseStart_1007656 baseEnd_1007656 := by
    simpa [prefixWord, tailWord_1007656, baseEnd_1007656] using wordTrace_append hprefix tailTrace_1007656
  have hstable : (prefixWord ++ tailWord_1007656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007656).length < 2 ^ (prefixWord ++ tailWord_1007656).sum := by decide
  have hdescent : baseEnd_1007656 < baseStart_1007656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007709 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_1007709 : Nat := 118140960795 + 1007709 * 2 ^ 59
def prefixEnd_1007709 : Nat := 4983230072969 + 3 ^ 40 * 1007709 * 2
def baseEnd_1007709 : Nat := 517439076861703067603137

theorem tailTrace_1007709 : CollatzResearch.WordTrace tailWord_1007709 prefixEnd_1007709 517439076861703067603137 := by
  unfold tailWord_1007709
  simp only [CollatzResearch.WordTrace]
  refine ⟨36754166706249870840490181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24502777804166580560326787 36754166706249870840490181)
  ·
    refine ⟨6891406257421850782591909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36754166706249870840490181 6891406257421850782591909)
    ·
      refine ⟨1292138673266597021735983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6891406257421850782591909 1292138673266597021735983)
      ·
        refine ⟨1938208009899895532603975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292138673266597021735983 1938208009899895532603975)
        ·
          refine ⟨2907312014849843298905963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938208009899895532603975 2907312014849843298905963)
          ·
            refine ⟨4360968022274764948358945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907312014849843298905963 4360968022274764948358945)
            ·
              refine ⟨3270726016706073711269209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4360968022274764948358945 3270726016706073711269209)
              ·
                refine ⟨2453044512529555283451907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270726016706073711269209 2453044512529555283451907)
                ·
                  refine ⟨3679566768794332925177861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453044512529555283451907 3679566768794332925177861)
                  ·
                    refine ⟨689918769148937423470849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679566768794332925177861 689918769148937423470849)
                    ·
                      refine ⟨517439076861703067603137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 689918769148937423470849 517439076861703067603137)
                      ·
                        rfl

theorem cell23_1007709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_1007709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007709 prefixEnd_1007709 := by exact prefixLift 1007709
  have htrace : WordTrace (prefixWord ++ tailWord_1007709) baseStart_1007709 baseEnd_1007709 := by
    simpa [prefixWord, tailWord_1007709, baseEnd_1007709] using wordTrace_append hprefix tailTrace_1007709
  have hstable : (prefixWord ++ tailWord_1007709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007709).length < 2 ^ (prefixWord ++ tailWord_1007709).sum := by decide
  have hdescent : baseEnd_1007709 < baseStart_1007709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007715 : List Nat := [1, 1, 1, 5, 1, 1, 3, 5, 5]
def baseStart_1007715 : Nat := 118140960795 + 1007715 * 2 ^ 59
def prefixEnd_1007715 : Nat := 4983230072969 + 3 ^ 40 * 1007715 * 2
def baseEnd_1007715 : Nat := 57493573082847782680901

theorem tailTrace_1007715 : CollatzResearch.WordTrace tailWord_1007715 prefixEnd_1007715 57493573082847782680901 := by
  unfold tailWord_1007715
  simp only [CollatzResearch.WordTrace]
  refine ⟨36754385544228133865208599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24502923696152089243472399 36754385544228133865208599)
  ·
    refine ⟨55131578316342200797812899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36754385544228133865208599 55131578316342200797812899)
    ·
      refine ⟨82697367474513301196719349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55131578316342200797812899 82697367474513301196719349)
      ·
        refine ⟨7752878200735621987192439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82697367474513301196719349 7752878200735621987192439)
        ·
          refine ⟨11629317301103432980788659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752878200735621987192439 11629317301103432980788659)
          ·
            refine ⟨17443975951655149471182989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11629317301103432980788659 17443975951655149471182989)
            ·
              refine ⟨6541490981870681051693621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17443975951655149471182989 6541490981870681051693621)
              ·
                refine ⟨613264779550376348596277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6541490981870681051693621 613264779550376348596277)
                ·
                  refine ⟨57493573082847782680901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 613264779550376348596277 57493573082847782680901)
                  ·
                    rfl

theorem cell23_1007715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 5].length) (baseStart_1007715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007715 prefixEnd_1007715 := by exact prefixLift 1007715
  have htrace : WordTrace (prefixWord ++ tailWord_1007715) baseStart_1007715 baseEnd_1007715 := by
    simpa [prefixWord, tailWord_1007715, baseEnd_1007715] using wordTrace_append hprefix tailTrace_1007715
  have hstable : (prefixWord ++ tailWord_1007715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007715).length < 2 ^ (prefixWord ++ tailWord_1007715).sum := by decide
  have hdescent : baseEnd_1007715 < baseStart_1007715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007725 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1007725 : Nat := 118140960795 + 1007725 * 2 ^ 59
def prefixEnd_1007725 : Nat := 4983230072969 + 3 ^ 40 * 1007725 * 2
def baseEnd_1007725 : Nat := 517447292552175005003063

theorem tailTrace_1007725 : CollatzResearch.WordTrace tailWord_1007725 prefixEnd_1007725 517447292552175005003063 := by
  unfold tailWord_1007725
  simp only [CollatzResearch.WordTrace]
  refine ⟨36754750274191905573072629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24503166849461270382048419 36754750274191905573072629)
  ·
    refine ⟨3445757838205491147475559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36754750274191905573072629 3445757838205491147475559)
    ·
      refine ⟨5168636757308236721213339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445757838205491147475559 5168636757308236721213339)
      ·
        refine ⟨7752955135962355081820009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168636757308236721213339 7752955135962355081820009)
        ·
          refine ⟨5814716351971766311365007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7752955135962355081820009 5814716351971766311365007)
          ·
            refine ⟨8722074527957649467047511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5814716351971766311365007 8722074527957649467047511)
            ·
              refine ⟨13083111791936474200571267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8722074527957649467047511 13083111791936474200571267)
              ·
                refine ⟨19624667687904711300856901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13083111791936474200571267 19624667687904711300856901)
                ·
                  refine ⟨3679625191482133368910669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19624667687904711300856901 3679625191482133368910669)
                  ·
                    refine ⟨1379859446805800013341501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3679625191482133368910669 1379859446805800013341501)
                    ·
                      refine ⟨517447292552175005003063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1379859446805800013341501 517447292552175005003063)
                      ·
                        rfl

theorem cell23_1007725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1007725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007725 prefixEnd_1007725 := by exact prefixLift 1007725
  have htrace : WordTrace (prefixWord ++ tailWord_1007725) baseStart_1007725 baseEnd_1007725 := by
    simpa [prefixWord, tailWord_1007725, baseEnd_1007725] using wordTrace_append hprefix tailTrace_1007725
  have hstable : (prefixWord ++ tailWord_1007725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007725).length < 2 ^ (prefixWord ++ tailWord_1007725).sum := by decide
  have hdescent : baseEnd_1007725 < baseStart_1007725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007765 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1007765 : Nat := 118140960795 + 1007765 * 2 ^ 59
def prefixEnd_1007765 : Nat := 4983230072969 + 3 ^ 40 * 1007765 * 2
def baseEnd_1007765 : Nat := 517467831778354848502879

theorem tailTrace_1007765 : CollatzResearch.WordTrace tailWord_1007765 prefixEnd_1007765 517467831778354848502879 := by
  unfold tailWord_1007765
  simp only [CollatzResearch.WordTrace]
  refine ⟨36756209194046992404528749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24504139462697994936352499 36756209194046992404528749)
  ·
    refine ⟨13783578447767622151698281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36756209194046992404528749 13783578447767622151698281)
    ·
      refine ⟨10337683835825716613773711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13783578447767622151698281 10337683835825716613773711)
      ·
        refine ⟨15506525753738574920660567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10337683835825716613773711 15506525753738574920660567)
        ·
          refine ⟨23259788630607862380990851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15506525753738574920660567 23259788630607862380990851)
          ·
            refine ⟨34889682945911793571486277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23259788630607862380990851 34889682945911793571486277)
            ·
              refine ⟨6541815552358461294653677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34889682945911793571486277 6541815552358461294653677)
              ·
                refine ⟨2453180832134422985495129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6541815552358461294653677 2453180832134422985495129)
                ·
                  refine ⟨1839885624100817239121347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453180832134422985495129 1839885624100817239121347)
                  ·
                    refine ⟨2759828436151225858682021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1839885624100817239121347 2759828436151225858682021)
                    ·
                      refine ⟨517467831778354848502879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2759828436151225858682021 517467831778354848502879)
                      ·
                        rfl

theorem cell23_1007765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1007765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007765 prefixEnd_1007765 := by exact prefixLift 1007765
  have htrace : WordTrace (prefixWord ++ tailWord_1007765) baseStart_1007765 baseEnd_1007765 := by
    simpa [prefixWord, tailWord_1007765, baseEnd_1007765] using wordTrace_append hprefix tailTrace_1007765
  have hstable : (prefixWord ++ tailWord_1007765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007765).length < 2 ^ (prefixWord ++ tailWord_1007765).sum := by decide
  have hdescent : baseEnd_1007765 < baseStart_1007765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007849 : List Nat := [1, 2, 1, 1, 1, 2, 2, 8, 1, 1, 3]
def baseStart_1007849 : Nat := 118140960795 + 1007849 * 2 ^ 59
def prefixEnd_1007849 : Nat := 4983230072969 + 3 ^ 40 * 1007849 * 2
def baseEnd_1007849 : Nat := 517510964153332519852493

theorem tailTrace_1007849 : CollatzResearch.WordTrace tailWord_1007849 prefixEnd_1007849 517510964153332519852493 := by
  unfold tailWord_1007849
  simp only [CollatzResearch.WordTrace]
  refine ⟨36759272925742674750586601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24506181950495116500391067 36759272925742674750586601)
  ·
    refine ⟨27569454694307006062939951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36759272925742674750586601 27569454694307006062939951)
    ·
      refine ⟨41354182041460509094409927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27569454694307006062939951 41354182041460509094409927)
      ·
        refine ⟨62031273062190763641614891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41354182041460509094409927 62031273062190763641614891)
        ·
          refine ⟨93046909593286145462422337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62031273062190763641614891 93046909593286145462422337)
          ·
            refine ⟨69785182194964609096816753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93046909593286145462422337 69785182194964609096816753)
            ·
              refine ⟨52338886646223456822612565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69785182194964609096816753 52338886646223456822612565)
              ·
                refine ⟨613346327885431134639991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 52338886646223456822612565 613346327885431134639991)
                ·
                  refine ⟨920019491828146701959987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613346327885431134639991 920019491828146701959987)
                  ·
                    refine ⟨1380029237742220052939981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 920019491828146701959987 1380029237742220052939981)
                    ·
                      refine ⟨517510964153332519852493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1380029237742220052939981 517510964153332519852493)
                      ·
                        rfl

theorem cell23_1007849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 1, 3].length) (baseStart_1007849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007849 prefixEnd_1007849 := by exact prefixLift 1007849
  have htrace : WordTrace (prefixWord ++ tailWord_1007849) baseStart_1007849 baseEnd_1007849 := by
    simpa [prefixWord, tailWord_1007849, baseEnd_1007849] using wordTrace_append hprefix tailTrace_1007849
  have hstable : (prefixWord ++ tailWord_1007849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007849).length < 2 ^ (prefixWord ++ tailWord_1007849).sum := by decide
  have hdescent : baseEnd_1007849 < baseStart_1007849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007889 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 1, 1, 4]
def baseStart_1007889 : Nat := 118140960795 + 1007889 * 2 ^ 59
def prefixEnd_1007889 : Nat := 4983230072969 + 3 ^ 40 * 1007889 * 2
def baseEnd_1007889 : Nat := 517531503379512363352309

theorem tailTrace_1007889 : CollatzResearch.WordTrace tailWord_1007889 prefixEnd_1007889 517531503379512363352309 := by
  unfold tailWord_1007889
  simp only [CollatzResearch.WordTrace]
  refine ⟨36760731845597761582042721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24507154563731841054695147 36760731845597761582042721)
  ·
    refine ⟨27570548884198321186532041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36760731845597761582042721 27570548884198321186532041)
    ·
      refine ⟨20677911663148740889899031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27570548884198321186532041 20677911663148740889899031)
      ·
        refine ⟨31016867494723111334848547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20677911663148740889899031 31016867494723111334848547)
        ·
          refine ⟨46525301242084667002272821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31016867494723111334848547 46525301242084667002272821)
          ·
            refine ⟨4361746991445437531463077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46525301242084667002272821 4361746991445437531463077)
            ·
              refine ⟨817827560896019537149327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4361746991445437531463077 817827560896019537149327)
              ·
                refine ⟨1226741341344029305723991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817827560896019537149327 1226741341344029305723991)
                ·
                  refine ⟨1840112012016043958585987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226741341344029305723991 1840112012016043958585987)
                  ·
                    refine ⟨2760168018024065937878981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1840112012016043958585987 2760168018024065937878981)
                    ·
                      refine ⟨517531503379512363352309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2760168018024065937878981 517531503379512363352309)
                      ·
                        rfl

theorem cell23_1007889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_1007889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007889 prefixEnd_1007889 := by exact prefixLift 1007889
  have htrace : WordTrace (prefixWord ++ tailWord_1007889) baseStart_1007889 baseEnd_1007889 := by
    simpa [prefixWord, tailWord_1007889, baseEnd_1007889] using wordTrace_append hprefix tailTrace_1007889
  have hstable : (prefixWord ++ tailWord_1007889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007889).length < 2 ^ (prefixWord ++ tailWord_1007889).sum := by decide
  have hdescent : baseEnd_1007889 < baseStart_1007889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007895 : List Nat := [1, 1, 3, 4, 1, 3, 10]
def baseStart_1007895 : Nat := 118140960795 + 1007895 * 2 ^ 59
def prefixEnd_1007895 : Nat := 4983230072969 + 3 ^ 40 * 1007895 * 2
def baseEnd_1007895 : Nat := 6389315855104189381201

theorem tailTrace_1007895 : CollatzResearch.WordTrace tailWord_1007895 prefixEnd_1007895 6389315855104189381201 := by
  unfold tailWord_1007895
  simp only [CollatzResearch.WordTrace]
  refine ⟨36760950683576024606761139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24507300455717349737840759 36760950683576024606761139)
  ·
    refine ⟨55141426025364036910141709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36760950683576024606761139 55141426025364036910141709)
    ·
      refine ⟨20678034759511513841303141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55141426025364036910141709 20678034759511513841303141)
      ·
        refine ⟨3877131517408408845244339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20678034759511513841303141 3877131517408408845244339)
        ·
          refine ⟨5815697276112613267866509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877131517408408845244339 5815697276112613267866509)
          ·
            refine ⟨2180886478542229975449941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5815697276112613267866509 2180886478542229975449941)
            ·
              refine ⟨6389315855104189381201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2180886478542229975449941 6389315855104189381201)
              ·
                rfl

theorem cell23_1007895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 10].length) (baseStart_1007895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007895 prefixEnd_1007895 := by exact prefixLift 1007895
  have htrace : WordTrace (prefixWord ++ tailWord_1007895) baseStart_1007895 baseEnd_1007895 := by
    simpa [prefixWord, tailWord_1007895, baseEnd_1007895] using wordTrace_append hprefix tailTrace_1007895
  have hstable : (prefixWord ++ tailWord_1007895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007895).length < 2 ^ (prefixWord ++ tailWord_1007895).sum := by decide
  have hdescent : baseEnd_1007895 < baseStart_1007895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007906 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_1007906 : Nat := 118140960795 + 1007906 * 2 ^ 59
def prefixEnd_1007906 : Nat := 4983230072969 + 3 ^ 40 * 1007906 * 2
def baseEnd_1007906 : Nat := 517540232550638796839731

theorem tailTrace_1007906 : CollatzResearch.WordTrace tailWord_1007906 prefixEnd_1007906 517540232550638796839731 := by
  unfold tailWord_1007906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9190337971634043371352893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24507567924357448990274381 9190337971634043371352893)
  ·
    refine ⟨3446376739362766264257335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9190337971634043371352893 3446376739362766264257335)
    ·
      refine ⟨5169565109044149396386003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446376739362766264257335 5169565109044149396386003)
      ·
        refine ⟨7754347663566224094579005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169565109044149396386003 7754347663566224094579005)
        ·
          refine ⟨2907880373837334035467127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7754347663566224094579005 2907880373837334035467127)
          ·
            refine ⟨4361820560756001053200691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907880373837334035467127 4361820560756001053200691)
            ·
              refine ⟨6542730841134001579801037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361820560756001053200691 6542730841134001579801037)
              ·
                refine ⟨2453524065425250592425389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6542730841134001579801037 2453524065425250592425389)
                ·
                  refine ⟨920071524534468972159521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2453524065425250592425389 920071524534468972159521)
                  ·
                    refine ⟨690053643400851729119641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 920071524534468972159521 690053643400851729119641)
                    ·
                      refine ⟨517540232550638796839731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690053643400851729119641 517540232550638796839731)
                      ·
                        rfl

theorem cell23_1007906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_1007906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007906 prefixEnd_1007906 := by exact prefixLift 1007906
  have htrace : WordTrace (prefixWord ++ tailWord_1007906) baseStart_1007906 baseEnd_1007906 := by
    simpa [prefixWord, tailWord_1007906, baseEnd_1007906] using wordTrace_append hprefix tailTrace_1007906
  have hstable : (prefixWord ++ tailWord_1007906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007906).length < 2 ^ (prefixWord ++ tailWord_1007906).sum := by decide
  have hdescent : baseEnd_1007906 < baseStart_1007906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007929 : List Nat := [1, 2, 1, 6, 1, 3, 2, 7]
def baseStart_1007929 : Nat := 118140960795 + 1007929 * 2 ^ 59
def prefixEnd_1007929 : Nat := 4983230072969 + 3 ^ 40 * 1007929 * 2
def baseEnd_1007929 : Nat := 19168594170581192846375

theorem tailTrace_1007929 : CollatzResearch.WordTrace tailWord_1007929 prefixEnd_1007929 19168594170581192846375 := by
  unfold tailWord_1007929
  simp only [CollatzResearch.WordTrace]
  refine ⟨36762190765452848413498841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24508127176968565608999227 36762190765452848413498841)
  ·
    refine ⟨27571643074089636310124131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36762190765452848413498841 27571643074089636310124131)
    ·
      refine ⟨41357464611134454465186197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27571643074089636310124131 41357464611134454465186197)
      ·
        refine ⟨1938631153646927553055603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41357464611134454465186197 1938631153646927553055603)
        ·
          refine ⟨2907946730470391329583405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938631153646927553055603 2907946730470391329583405)
          ·
            refine ⟨1090480023926396748593777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2907946730470391329583405 1090480023926396748593777)
            ·
              refine ⟨817860017944797561445333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090480023926396748593777 817860017944797561445333)
              ·
                refine ⟨19168594170581192846375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 817860017944797561445333 19168594170581192846375)
                ·
                  rfl

theorem cell23_1007929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 7].length) (baseStart_1007929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007929 prefixEnd_1007929 := by exact prefixLift 1007929
  have htrace : WordTrace (prefixWord ++ tailWord_1007929) baseStart_1007929 baseEnd_1007929 := by
    simpa [prefixWord, tailWord_1007929, baseEnd_1007929] using wordTrace_append hprefix tailTrace_1007929
  have hstable : (prefixWord ++ tailWord_1007929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007929).length < 2 ^ (prefixWord ++ tailWord_1007929).sum := by decide
  have hdescent : baseEnd_1007929 < baseStart_1007929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007935 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_1007935 : Nat := 118140960795 + 1007935 * 2 ^ 59
def prefixEnd_1007935 : Nat := 4983230072969 + 3 ^ 40 * 1007935 * 2
def baseEnd_1007935 : Nat := 517555123489619183377097

theorem tailTrace_1007935 : CollatzResearch.WordTrace tailWord_1007935 prefixEnd_1007935 517555123489619183377097 := by
  unfold tailWord_1007935
  simp only [CollatzResearch.WordTrace]
  refine ⟨36762409603431111438217259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24508273068954074292144839 36762409603431111438217259)
  ·
    refine ⟨55143614405146667157325889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36762409603431111438217259 55143614405146667157325889)
    ·
      refine ⟨41357710803860000367994417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55143614405146667157325889 41357710803860000367994417)
      ·
        refine ⟨31018283102895000275995813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41357710803860000367994417 31018283102895000275995813)
        ·
          refine ⟨5815928081792812551749215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31018283102895000275995813 5815928081792812551749215)
          ·
            refine ⟨8723892122689218827623823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5815928081792812551749215 8723892122689218827623823)
            ·
              refine ⟨13085838184033828241435735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8723892122689218827623823 13085838184033828241435735)
              ·
                refine ⟨19628757276050742362153603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13085838184033828241435735 19628757276050742362153603)
                ·
                  refine ⟨29443135914076113543230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19628757276050742362153603 29443135914076113543230405)
                  ·
                    refine ⟨5520587983889271289355701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29443135914076113543230405 5520587983889271289355701)
                    ·
                      refine ⟨517555123489619183377097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5520587983889271289355701 517555123489619183377097)
                      ·
                        rfl

theorem cell23_1007935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_1007935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007935 prefixEnd_1007935 := by exact prefixLift 1007935
  have htrace : WordTrace (prefixWord ++ tailWord_1007935) baseStart_1007935 baseEnd_1007935 := by
    simpa [prefixWord, tailWord_1007935, baseEnd_1007935] using wordTrace_append hprefix tailTrace_1007935
  have hstable : (prefixWord ++ tailWord_1007935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007935).length < 2 ^ (prefixWord ++ tailWord_1007935).sum := by decide
  have hdescent : baseEnd_1007935 < baseStart_1007935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007945 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_1007945 : Nat := 118140960795 + 1007945 * 2 ^ 59
def prefixEnd_1007945 : Nat := 4983230072969 + 3 ^ 40 * 1007945 * 2
def baseEnd_1007945 : Nat := 517560258296164144252051

theorem tailTrace_1007945 : CollatzResearch.WordTrace tailWord_1007945 prefixEnd_1007945 517560258296164144252051 := by
  unfold tailWord_1007945
  simp only [CollatzResearch.WordTrace]
  refine ⟨36762774333394883146081289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24508516222263255430720859 36762774333394883146081289)
  ·
    refine ⟨27572080750046162359560967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36762774333394883146081289 27572080750046162359560967)
    ·
      refine ⟨41358121125069243539341451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27572080750046162359560967 41358121125069243539341451)
      ·
        refine ⟨62037181687603865309012177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41358121125069243539341451 62037181687603865309012177)
        ·
          refine ⟨46527886265702898981759133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62037181687603865309012177 46527886265702898981759133)
          ·
            refine ⟨17447957349638587118159675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46527886265702898981759133 17447957349638587118159675)
            ·
              refine ⟨26171936024457880677239513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17447957349638587118159675 26171936024457880677239513)
              ·
                refine ⟨19628952018343410507929635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26171936024457880677239513 19628952018343410507929635)
                ·
                  refine ⟨29443428027515115761894453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19628952018343410507929635 29443428027515115761894453)
                  ·
                    refine ⟨2760321377579542102677605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29443428027515115761894453 2760321377579542102677605)
                    ·
                      refine ⟨517560258296164144252051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2760321377579542102677605 517560258296164144252051)
                      ·
                        rfl

theorem cell23_1007945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_1007945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007945 prefixEnd_1007945 := by exact prefixLift 1007945
  have htrace : WordTrace (prefixWord ++ tailWord_1007945) baseStart_1007945 baseEnd_1007945 := by
    simpa [prefixWord, tailWord_1007945, baseEnd_1007945] using wordTrace_append hprefix tailTrace_1007945
  have hstable : (prefixWord ++ tailWord_1007945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007945).length < 2 ^ (prefixWord ++ tailWord_1007945).sum := by decide
  have hdescent : baseEnd_1007945 < baseStart_1007945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007955 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 2, 6]
def baseStart_1007955 : Nat := 118140960795 + 1007955 * 2 ^ 59
def prefixEnd_1007955 : Nat := 4983230072969 + 3 ^ 40 * 1007955 * 2
def baseEnd_1007955 : Nat := 172521797700903035042335

theorem tailTrace_1007955 : CollatzResearch.WordTrace tailWord_1007955 prefixEnd_1007955 172521797700903035042335 := by
  unfold tailWord_1007955
  simp only [CollatzResearch.WordTrace]
  refine ⟨36763139063358654853945319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24508759375572436569296879 36763139063358654853945319)
  ·
    refine ⟨55144708595037982280917979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36763139063358654853945319 55144708595037982280917979)
    ·
      refine ⟨82717062892556973421376969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55144708595037982280917979 82717062892556973421376969)
      ·
        refine ⟨62037797169417730066032727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82717062892556973421376969 62037797169417730066032727)
        ·
          refine ⟨93056695754126595099049091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62037797169417730066032727 93056695754126595099049091)
          ·
            refine ⟨139585043631189892648573637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93056695754126595099049091 139585043631189892648573637)
            ·
              refine ⟨26172195680848104871607557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139585043631189892648573637 26172195680848104871607557)
              ·
                refine ⟨4907286690159019663426417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26172195680848104871607557 4907286690159019663426417)
                ·
                  refine ⟨3680465017619264747569813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907286690159019663426417 3680465017619264747569813)
                  ·
                    refine ⟨172521797700903035042335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3680465017619264747569813 172521797700903035042335)
                    ·
                      rfl

theorem cell23_1007955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 6].length) (baseStart_1007955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007955 prefixEnd_1007955 := by exact prefixLift 1007955
  have htrace : WordTrace (prefixWord ++ tailWord_1007955) baseStart_1007955 baseEnd_1007955 := by
    simpa [prefixWord, tailWord_1007955, baseEnd_1007955] using wordTrace_append hprefix tailTrace_1007955
  have hstable : (prefixWord ++ tailWord_1007955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007955).length < 2 ^ (prefixWord ++ tailWord_1007955).sum := by decide
  have hdescent : baseEnd_1007955 < baseStart_1007955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007973 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 2, 1, 3]
def baseStart_1007973 : Nat := 118140960795 + 1007973 * 2 ^ 59
def prefixEnd_1007973 : Nat := 4983230072969 + 3 ^ 40 * 1007973 * 2
def baseEnd_1007973 : Nat := 517574635754490034701923

theorem tailTrace_1007973 : CollatzResearch.WordTrace tailWord_1007973 prefixEnd_1007973 517574635754490034701923 := by
  unfold tailWord_1007973
  simp only [CollatzResearch.WordTrace]
  refine ⟨36763795577293443928100573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24509197051528962618733715 36763795577293443928100573)
  ·
    refine ⟨13786423341485041473037715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36763795577293443928100573 13786423341485041473037715)
    ·
      refine ⟨20679635012227562209556573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13786423341485041473037715 20679635012227562209556573)
      ·
        refine ⟨7754863129585335828583715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20679635012227562209556573 7754863129585335828583715)
        ·
          refine ⟨11632294694378003742875573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754863129585335828583715 11632294694378003742875573)
          ·
            refine ⟨1090527627597937850894585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11632294694378003742875573 1090527627597937850894585)
            ·
              refine ⟨817895720698453388170939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090527627597937850894585 817895720698453388170939)
              ·
                refine ⟨1226843581047680082256409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817895720698453388170939 1226843581047680082256409)
                ·
                  refine ⟨920132685785760061692307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1226843581047680082256409 920132685785760061692307)
                  ·
                    refine ⟨1380199028678640092538461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 920132685785760061692307 1380199028678640092538461)
                    ·
                      refine ⟨517574635754490034701923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1380199028678640092538461 517574635754490034701923)
                      ·
                        rfl

theorem cell23_1007973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_1007973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007973 prefixEnd_1007973 := by exact prefixLift 1007973
  have htrace : WordTrace (prefixWord ++ tailWord_1007973) baseStart_1007973 baseEnd_1007973 := by
    simpa [prefixWord, tailWord_1007973, baseEnd_1007973] using wordTrace_append hprefix tailTrace_1007973
  have hstable : (prefixWord ++ tailWord_1007973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007973).length < 2 ^ (prefixWord ++ tailWord_1007973).sum := by decide
  have hdescent : baseEnd_1007973 < baseStart_1007973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007985 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 9]
def baseStart_1007985 : Nat := 118140960795 + 1007985 * 2 ^ 59
def prefixEnd_1007985 : Nat := 4983230072969 + 3 ^ 40 * 1007985 * 2
def baseEnd_1007985 : Nat := 57508977502482665305763

theorem tailTrace_1007985 : CollatzResearch.WordTrace tailWord_1007985 prefixEnd_1007985 57508977502482665305763 := by
  unfold tailWord_1007985
  simp only [CollatzResearch.WordTrace]
  refine ⟨36764233253249969977537409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24509488835499979985024939 36764233253249969977537409)
  ·
    refine ⟨27573174939937477483153057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36764233253249969977537409 27573174939937477483153057)
    ·
      refine ⟨20679881204953108112364793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27573174939937477483153057 20679881204953108112364793)
      ·
        refine ⟨15509910903714831084273595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20679881204953108112364793 15509910903714831084273595)
        ·
          refine ⟨23264866355572246626410393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15509910903714831084273595 23264866355572246626410393)
          ·
            refine ⟨17448649766679184969807795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23264866355572246626410393 17448649766679184969807795)
            ·
              refine ⟨26172974650018777454711693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17448649766679184969807795 26172974650018777454711693)
              ·
                refine ⟨9814865493757041545516885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26172974650018777454711693 9814865493757041545516885)
                ·
                  refine ⟨57508977502482665305763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9814865493757041545516885 57508977502482665305763)
                  ·
                    rfl

theorem cell23_1007985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 9].length) (baseStart_1007985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1007985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1007985 prefixEnd_1007985 := by exact prefixLift 1007985
  have htrace : WordTrace (prefixWord ++ tailWord_1007985) baseStart_1007985 baseEnd_1007985 := by
    simpa [prefixWord, tailWord_1007985, baseEnd_1007985] using wordTrace_append hprefix tailTrace_1007985
  have hstable : (prefixWord ++ tailWord_1007985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007985).length < 2 ^ (prefixWord ++ tailWord_1007985).sum := by decide
  have hdescent : baseEnd_1007985 < baseStart_1007985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008030 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_1008030 : Nat := 118140960795 + 1008030 * 2 ^ 59
def prefixEnd_1008030 : Nat := 4983230072969 + 3 ^ 40 * 1008030 * 2
def baseEnd_1008030 : Nat := 517603904151796311689161

theorem tailTrace_1008030 : CollatzResearch.WordTrace tailWord_1008030 prefixEnd_1008030 517603904151796311689161 := by
  unfold tailWord_1008030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595734317260867832865693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24510583025391295108617029 4595734317260867832865693)
  ·
    refine ⟨1723400368972825437324635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4595734317260867832865693 1723400368972825437324635)
    ·
      refine ⟨2585100553459238155986953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723400368972825437324635 2585100553459238155986953)
      ·
        refine ⟨1938825415094428616990215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2585100553459238155986953 1938825415094428616990215)
        ·
          refine ⟨2908238122641642925485323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938825415094428616990215 2908238122641642925485323)
          ·
            refine ⟨4362357183962464388227985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908238122641642925485323 4362357183962464388227985)
            ·
              refine ⟨3271767887971848291170989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4362357183962464388227985 3271767887971848291170989)
              ·
                refine ⟨1226912957989443109189121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3271767887971848291170989 1226912957989443109189121)
                ·
                  refine ⟨920184718492082331891841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1226912957989443109189121 920184718492082331891841)
                  ·
                    refine ⟨690138538869061748918881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 920184718492082331891841 690138538869061748918881)
                    ·
                      refine ⟨517603904151796311689161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690138538869061748918881 517603904151796311689161)
                      ·
                        rfl

theorem cell23_1008030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_1008030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008030 prefixEnd_1008030 := by exact prefixLift 1008030
  have htrace : WordTrace (prefixWord ++ tailWord_1008030) baseStart_1008030 baseEnd_1008030 := by
    simpa [prefixWord, tailWord_1008030, baseEnd_1008030] using wordTrace_append hprefix tailTrace_1008030
  have hstable : (prefixWord ++ tailWord_1008030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008030).length < 2 ^ (prefixWord ++ tailWord_1008030).sum := by decide
  have hdescent : baseEnd_1008030 < baseStart_1008030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008049 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 2, 5]
def baseStart_1008049 : Nat := 118140960795 + 1008049 * 2 ^ 59
def prefixEnd_1008049 : Nat := 4983230072969 + 3 ^ 40 * 1008049 * 2
def baseEnd_1008049 : Nat := 172537886761410579117191

theorem tailTrace_1008049 : CollatzResearch.WordTrace tailWord_1008049 prefixEnd_1008049 172537886761410579117191 := by
  unfold tailWord_1008049
  simp only [CollatzResearch.WordTrace]
  refine ⟨36766567525018108907867201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24511045016678739271911467 36766567525018108907867201)
  ·
    refine ⟨27574925643763581680900401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36766567525018108907867201 27574925643763581680900401)
    ·
      refine ⟨20681194232822686260675301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27574925643763581680900401 20681194232822686260675301)
      ·
        refine ⟨3877723918654253673876619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20681194232822686260675301 3877723918654253673876619)
        ·
          refine ⟨5816585877981380510814929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877723918654253673876619 5816585877981380510814929)
          ·
            refine ⟨4362439408486035383111197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5816585877981380510814929 4362439408486035383111197)
            ·
              refine ⟨1635914778182263268666699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4362439408486035383111197 1635914778182263268666699)
              ·
                refine ⟨2453872167273394903000049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635914778182263268666699 2453872167273394903000049)
                ·
                  refine ⟨1840404125455046177250037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453872167273394903000049 1840404125455046177250037)
                  ·
                    refine ⟨172537886761410579117191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1840404125455046177250037 172537886761410579117191)
                    ·
                      rfl

theorem cell23_1008049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_1008049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008049 prefixEnd_1008049 := by exact prefixLift 1008049
  have htrace : WordTrace (prefixWord ++ tailWord_1008049) baseStart_1008049 baseEnd_1008049 := by
    simpa [prefixWord, tailWord_1008049, baseEnd_1008049] using wordTrace_append hprefix tailTrace_1008049
  have hstable : (prefixWord ++ tailWord_1008049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008049).length < 2 ^ (prefixWord ++ tailWord_1008049).sum := by decide
  have hdescent : baseEnd_1008049 < baseStart_1008049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008109 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 8]
def baseStart_1008109 : Nat := 118140960795 + 1008109 * 2 ^ 59
def prefixEnd_1008109 : Nat := 4983230072969 + 3 ^ 40 * 1008109 * 2
def baseEnd_1008109 : Nat := 57516052124833500289033

theorem tailTrace_1008109 : CollatzResearch.WordTrace tailWord_1008109 prefixEnd_1008109 57516052124833500289033 := by
  unfold tailWord_1008109
  simp only [CollatzResearch.WordTrace]
  refine ⟨36768755904800739155051381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24512503936533826103367587 36768755904800739155051381)
  ·
    refine ⟨3447070866075069295786067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36768755904800739155051381 3447070866075069295786067)
    ·
      refine ⟨5170606299112603943679101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447070866075069295786067 5170606299112603943679101)
      ·
        refine ⟨1938977362167226478879663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5170606299112603943679101 1938977362167226478879663)
        ·
          refine ⟨2908466043250839718319495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938977362167226478879663 2908466043250839718319495)
          ·
            refine ⟨4362699064876259577479243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908466043250839718319495 4362699064876259577479243)
            ·
              refine ⟨6544048597314389366218865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362699064876259577479243 6544048597314389366218865)
              ·
                refine ⟨4908036447985792024664149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544048597314389366218865 4908036447985792024664149)
                ·
                  refine ⟨57516052124833500289033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4908036447985792024664149 57516052124833500289033)
                  ·
                    rfl

theorem cell23_1008109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_1008109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008109 prefixEnd_1008109 := by exact prefixLift 1008109
  have htrace : WordTrace (prefixWord ++ tailWord_1008109) baseStart_1008109 baseEnd_1008109 := by
    simpa [prefixWord, tailWord_1008109, baseEnd_1008109] using wordTrace_append hprefix tailTrace_1008109
  have hstable : (prefixWord ++ tailWord_1008109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008109).length < 2 ^ (prefixWord ++ tailWord_1008109).sum := by decide
  have hdescent : baseEnd_1008109 < baseStart_1008109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008130 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1008130 : Nat := 118140960795 + 1008130 * 2 ^ 59
def prefixEnd_1008130 : Nat := 4983230072969 + 3 ^ 40 * 1008130 * 2
def baseEnd_1008130 : Nat := 172551750739081973479567

theorem tailTrace_1008130 : CollatzResearch.WordTrace tailWord_1008130 prefixEnd_1008130 172551750739081973479567 := by
  unfold tailWord_1008130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9192380459431164935391461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24513014558483106494377229 9192380459431164935391461)
  ·
    refine ⟨1723571336143343425385899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9192380459431164935391461 1723571336143343425385899)
    ·
      refine ⟨2585357004215015138078849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723571336143343425385899 2585357004215015138078849)
      ·
        refine ⟨1939017753161261353559137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2585357004215015138078849 1939017753161261353559137)
        ·
          refine ⟨1454263314870946015169353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1939017753161261353559137 1454263314870946015169353)
          ·
            refine ⟨1090697486153209511377015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454263314870946015169353 1090697486153209511377015)
            ·
              refine ⟨1636046229229814267065523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090697486153209511377015 1636046229229814267065523)
              ·
                refine ⟨2454069343844721400598285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636046229229814267065523 2454069343844721400598285)
                ·
                  refine ⟨920276003941770525224357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2454069343844721400598285 920276003941770525224357)
                  ·
                    refine ⟨172551750739081973479567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 920276003941770525224357 172551750739081973479567)
                    ·
                      rfl

theorem cell23_1008130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1008130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008130 prefixEnd_1008130 := by exact prefixLift 1008130
  have htrace : WordTrace (prefixWord ++ tailWord_1008130) baseStart_1008130 baseEnd_1008130 := by
    simpa [prefixWord, tailWord_1008130, baseEnd_1008130] using wordTrace_append hprefix tailTrace_1008130
  have hstable : (prefixWord ++ tailWord_1008130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008130).length < 2 ^ (prefixWord ++ tailWord_1008130).sum := by decide
  have hdescent : baseEnd_1008130 < baseStart_1008130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008156 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_1008156 : Nat := 118140960795 + 1008156 * 2 ^ 59
def prefixEnd_1008156 : Nat := 4983230072969 + 3 ^ 40 * 1008156 * 2
def baseEnd_1008156 : Nat := 172556200904754272904527

theorem tailTrace_1008156 : CollatzResearch.WordTrace tailWord_1008156 prefixEnd_1008156 172556200904754272904527 := by
  unfold tailWord_1008156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18385235067815233091006161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24513646757086977454674881 18385235067815233091006161)
  ·
    refine ⟨13788926300861424818254621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18385235067815233091006161 13788926300861424818254621)
    ·
      refine ⟨5170847362823034306845483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13788926300861424818254621 5170847362823034306845483)
      ·
        refine ⟨7756271044234551460268225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170847362823034306845483 7756271044234551460268225)
        ·
          refine ⟨5817203283175913595201169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7756271044234551460268225 5817203283175913595201169)
          ·
            refine ⟨4362902462381935196400877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5817203283175913595201169 4362902462381935196400877)
            ·
              refine ⟨1636088423393225698650329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4362902462381935196400877 1636088423393225698650329)
              ·
                refine ⟨1227066317544919273987747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636088423393225698650329 1227066317544919273987747)
                ·
                  refine ⟨1840599476317378910981621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227066317544919273987747 1840599476317378910981621)
                  ·
                    refine ⟨172556200904754272904527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1840599476317378910981621 172556200904754272904527)
                    ·
                      rfl

theorem cell23_1008156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_1008156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008156 prefixEnd_1008156 := by exact prefixLift 1008156
  have htrace : WordTrace (prefixWord ++ tailWord_1008156) baseStart_1008156 baseEnd_1008156 := by
    simpa [prefixWord, tailWord_1008156, baseEnd_1008156] using wordTrace_append hprefix tailTrace_1008156
  have hstable : (prefixWord ++ tailWord_1008156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008156).length < 2 ^ (prefixWord ++ tailWord_1008156).sum := by decide
  have hdescent : baseEnd_1008156 < baseStart_1008156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008163 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 2, 3, 2]
def baseStart_1008163 : Nat := 118140960795 + 1008163 * 2 ^ 59
def prefixEnd_1008163 : Nat := 4983230072969 + 3 ^ 40 * 1008163 * 2
def baseEnd_1008163 : Nat := 517672197078844291326049

theorem tailTrace_1008163 : CollatzResearch.WordTrace tailWord_1008163 prefixEnd_1008163 517672197078844291326049 := by
  unfold tailWord_1008163
  simp only [CollatzResearch.WordTrace]
  refine ⟨36770725446605106377517143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24513816964403404251678095 36770725446605106377517143)
  ·
    refine ⟨55156088169907659566275715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36770725446605106377517143 55156088169907659566275715)
    ·
      refine ⟨82734132254861489349413573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55156088169907659566275715 82734132254861489349413573)
      ·
        refine ⟨15512649797786529253015045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82734132254861489349413573 15512649797786529253015045)
        ·
          refine ⟨2908621837084974234940321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15512649797786529253015045 2908621837084974234940321)
          ·
            refine ⟨2181466377813730676205241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2908621837084974234940321 2181466377813730676205241)
            ·
              refine ⟨1636099783360298007153931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181466377813730676205241 1636099783360298007153931)
              ·
                refine ⟨2454149675040447010730897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636099783360298007153931 2454149675040447010730897)
                ·
                  refine ⟨1840612256280335258048173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2454149675040447010730897 1840612256280335258048173)
                  ·
                    refine ⟨690229596105125721768065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840612256280335258048173 690229596105125721768065)
                    ·
                      refine ⟨517672197078844291326049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690229596105125721768065 517672197078844291326049)
                      ·
                        rfl

theorem cell23_1008163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_1008163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008163 prefixEnd_1008163 := by exact prefixLift 1008163
  have htrace : WordTrace (prefixWord ++ tailWord_1008163) baseStart_1008163 baseEnd_1008163 := by
    simpa [prefixWord, tailWord_1008163, baseEnd_1008163] using wordTrace_append hprefix tailTrace_1008163
  have hstable : (prefixWord ++ tailWord_1008163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008163).length < 2 ^ (prefixWord ++ tailWord_1008163).sum := by decide
  have hdescent : baseEnd_1008163 < baseStart_1008163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008186 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_1008186 : Nat := 118140960795 + 1008186 * 2 ^ 59
def prefixEnd_1008186 : Nat := 4983230072969 + 3 ^ 40 * 1008186 * 2
def baseEnd_1008186 : Nat := 172561335711299233779481

theorem tailTrace_1008186 : CollatzResearch.WordTrace tailWord_1008186 prefixEnd_1008186 172561335711299233779481 := by
  unfold tailWord_1008186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9192891081380445326401103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24514376217014520870402941 9192891081380445326401103)
  ·
    refine ⟨13789336622070667989601655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9192891081380445326401103 13789336622070667989601655)
    ·
      refine ⟨20684004933106001984402483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13789336622070667989601655 20684004933106001984402483)
      ·
        refine ⟨31026007399659002976603725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20684004933106001984402483 31026007399659002976603725)
        ·
          refine ⟨11634752774872126116226397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31026007399659002976603725 11634752774872126116226397)
          ·
            refine ⟨4363032290577047293584899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11634752774872126116226397 4363032290577047293584899)
            ·
              refine ⟨6544548435865570940377349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363032290577047293584899 6544548435865570940377349)
              ·
                refine ⟨1227102831724794551320753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6544548435865570940377349 1227102831724794551320753)
                ·
                  refine ⟨920327123793595913490565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1227102831724794551320753 920327123793595913490565)
                  ·
                    refine ⟨172561335711299233779481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 920327123793595913490565 172561335711299233779481)
                    ·
                      rfl

theorem cell23_1008186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_1008186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008186 prefixEnd_1008186 := by exact prefixLift 1008186
  have htrace : WordTrace (prefixWord ++ tailWord_1008186) baseStart_1008186 baseEnd_1008186 := by
    simpa [prefixWord, tailWord_1008186, baseEnd_1008186] using wordTrace_append hprefix tailTrace_1008186
  have hstable : (prefixWord ++ tailWord_1008186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008186).length < 2 ^ (prefixWord ++ tailWord_1008186).sum := by decide
  have hdescent : baseEnd_1008186 < baseStart_1008186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008199 : List Nat := [1, 1, 4, 1, 4, 1, 3, 8]
def baseStart_1008199 : Nat := 118140960795 + 1008199 * 2 ^ 59
def prefixEnd_1008199 : Nat := 4983230072969 + 3 ^ 40 * 1008199 * 2
def baseEnd_1008199 : Nat := 19173728977126153721329

theorem tailTrace_1008199 : CollatzResearch.WordTrace tailWord_1008199 prefixEnd_1008199 19173728977126153721329 := by
  unfold tailWord_1008199
  simp only [CollatzResearch.WordTrace]
  refine ⟨36772038474474684525827651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24514692316316456350551767 36772038474474684525827651)
  ·
    refine ⟨55158057711712026788741477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36772038474474684525827651 55158057711712026788741477)
    ·
      refine ⟨10342135820946005022889027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55158057711712026788741477 10342135820946005022889027)
      ·
        refine ⟨15513203731419007534333541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10342135820946005022889027 15513203731419007534333541)
        ·
          refine ⟨2908725699641063912687539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15513203731419007534333541 2908725699641063912687539)
          ·
            refine ⟨4363088549461595869031309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908725699641063912687539 4363088549461595869031309)
            ·
              refine ⟨1636158206048098450886741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4363088549461595869031309 1636158206048098450886741)
              ·
                refine ⟨19173728977126153721329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1636158206048098450886741 19173728977126153721329)
                ·
                  rfl

theorem cell23_1008199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 8].length) (baseStart_1008199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008199 prefixEnd_1008199 := by exact prefixLift 1008199
  have htrace : WordTrace (prefixWord ++ tailWord_1008199) baseStart_1008199 baseEnd_1008199 := by
    simpa [prefixWord, tailWord_1008199, baseEnd_1008199] using wordTrace_append hprefix tailTrace_1008199
  have hstable : (prefixWord ++ tailWord_1008199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008199).length < 2 ^ (prefixWord ++ tailWord_1008199).sum := by decide
  have hdescent : baseEnd_1008199 < baseStart_1008199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008259 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 2, 6]
def baseStart_1008259 : Nat := 118140960795 + 1008259 * 2 ^ 59
def prefixEnd_1008259 : Nat := 4983230072969 + 3 ^ 40 * 1008259 * 2
def baseEnd_1008259 : Nat := 172573830407225305241869

theorem tailTrace_1008259 : CollatzResearch.WordTrace tailWord_1008259 prefixEnd_1008259 172573830407225305241869 := by
  unfold tailWord_1008259
  simp only [CollatzResearch.WordTrace]
  refine ⟨36774226854257314773011831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24516151236171543182007887 36774226854257314773011831)
  ·
    refine ⟨55161340281385972159517747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36774226854257314773011831 55161340281385972159517747)
    ·
      refine ⟨82742010422078958239276621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55161340281385972159517747 82742010422078958239276621)
      ·
        refine ⟨31028253908279609339728733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82742010422078958239276621 31028253908279609339728733)
        ·
          refine ⟨11635595215604853502398275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31028253908279609339728733 11635595215604853502398275)
          ·
            refine ⟨17453392823407280253597413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635595215604853502398275 17453392823407280253597413)
            ·
              refine ⟨3272511154388865047549515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17453392823407280253597413 3272511154388865047549515)
              ·
                refine ⟨4908766731583297571324273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272511154388865047549515 4908766731583297571324273)
                ·
                  refine ⟨3681575048687473178493205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908766731583297571324273 3681575048687473178493205)
                  ·
                    refine ⟨172573830407225305241869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3681575048687473178493205 172573830407225305241869)
                    ·
                      rfl

theorem cell23_1008259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 6].length) (baseStart_1008259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008259 prefixEnd_1008259 := by exact prefixLift 1008259
  have htrace : WordTrace (prefixWord ++ tailWord_1008259) baseStart_1008259 baseEnd_1008259 := by
    simpa [prefixWord, tailWord_1008259, baseEnd_1008259] using wordTrace_append hprefix tailTrace_1008259
  have hstable : (prefixWord ++ tailWord_1008259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008259).length < 2 ^ (prefixWord ++ tailWord_1008259).sum := by decide
  have hdescent : baseEnd_1008259 < baseStart_1008259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008270 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_1008270 : Nat := 118140960795 + 1008270 * 2 ^ 59
def prefixEnd_1008270 : Nat := 4983230072969 + 3 ^ 40 * 1008270 * 2
def baseEnd_1008270 : Nat := 517727139508875372688057

theorem tailTrace_1008270 : CollatzResearch.WordTrace tailWord_1008270 prefixEnd_1008270 517727139508875372688057 := by
  unfold tailWord_1008270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596828507152182956457783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24516418704811642434441509 4596828507152182956457783)
  ·
    refine ⟨6895242760728274434686675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4596828507152182956457783 6895242760728274434686675)
    ·
      refine ⟨10342864141092411652030013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895242760728274434686675 10342864141092411652030013)
      ·
        refine ⟨3878574052909654369511255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10342864141092411652030013 3878574052909654369511255)
        ·
          refine ⟨5817861079364481554266883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3878574052909654369511255 5817861079364481554266883)
          ·
            refine ⟨8726791619046722331400325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817861079364481554266883 8726791619046722331400325)
            ·
              refine ⟨1636273428571260437137561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8726791619046722331400325 1636273428571260437137561)
              ·
                refine ⟨1227205071428445327853171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636273428571260437137561 1227205071428445327853171)
                ·
                  refine ⟨1840807607142667991779757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227205071428445327853171 1840807607142667991779757)
                  ·
                    refine ⟨690302852678500496917409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840807607142667991779757 690302852678500496917409)
                    ·
                      refine ⟨517727139508875372688057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690302852678500496917409 517727139508875372688057)
                      ·
                        rfl

theorem cell23_1008270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_1008270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008270 prefixEnd_1008270 := by exact prefixLift 1008270
  have htrace : WordTrace (prefixWord ++ tailWord_1008270) baseStart_1008270 baseEnd_1008270 := by
    simpa [prefixWord, tailWord_1008270, baseEnd_1008270] using wordTrace_append hprefix tailTrace_1008270
  have hstable : (prefixWord ++ tailWord_1008270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008270).length < 2 ^ (prefixWord ++ tailWord_1008270).sum := by decide
  have hdescent : baseEnd_1008270 < baseStart_1008270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008316 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1008316 : Nat := 118140960795 + 1008316 * 2 ^ 59
def prefixEnd_1008316 : Nat := 4983230072969 + 3 ^ 40 * 1008316 * 2
def baseEnd_1008316 : Nat := 517750759618982192712845

theorem tailTrace_1008316 : CollatzResearch.WordTrace tailWord_1008316 prefixEnd_1008316 517750759618982192712845 := by
  unfold tailWord_1008316
  simp only [CollatzResearch.WordTrace]
  refine ⟨18388152907525406753918401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24517537210033875671891201 18388152907525406753918401)
  ·
    refine ⟨13791114680644055065438801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18388152907525406753918401 13791114680644055065438801)
    ·
      refine ⟨10343336010483041299079101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13791114680644055065438801 10343336010483041299079101)
      ·
        refine ⟨3878751003931140487154663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10343336010483041299079101 3878751003931140487154663)
        ·
          refine ⟨5818126505896710730731995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3878751003931140487154663 5818126505896710730731995)
          ·
            refine ⟨8727189758845066096097993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818126505896710730731995 8727189758845066096097993)
            ·
              refine ⟨6545392319133799572073495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8727189758845066096097993 6545392319133799572073495)
              ·
                refine ⟨9818088478700699358110243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545392319133799572073495 9818088478700699358110243)
                ·
                  refine ⟨14727132718051049037165365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9818088478700699358110243 14727132718051049037165365)
                  ·
                    refine ⟨1380668692317285847234253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14727132718051049037165365 1380668692317285847234253)
                    ·
                      refine ⟨517750759618982192712845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1380668692317285847234253 517750759618982192712845)
                      ·
                        rfl

theorem cell23_1008316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1008316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008316 prefixEnd_1008316 := by exact prefixLift 1008316
  have htrace : WordTrace (prefixWord ++ tailWord_1008316) baseStart_1008316 baseEnd_1008316 := by
    simpa [prefixWord, tailWord_1008316, baseEnd_1008316] using wordTrace_append hprefix tailTrace_1008316
  have hstable : (prefixWord ++ tailWord_1008316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008316).length < 2 ^ (prefixWord ++ tailWord_1008316).sum := by decide
  have hdescent : baseEnd_1008316 < baseStart_1008316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008317 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_1008317 : Nat := 118140960795 + 1008317 * 2 ^ 59
def prefixEnd_1008317 : Nat := 4983230072969 + 3 ^ 40 * 1008317 * 2
def baseEnd_1008317 : Nat := 517751273099636688800341

theorem tailTrace_1008317 : CollatzResearch.WordTrace tailWord_1008317 prefixEnd_1008317 517751273099636688800341 := by
  unfold tailWord_1008317
  simp only [CollatzResearch.WordTrace]
  refine ⟨36776342288047190678623205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24517561525364793785748803 36776342288047190678623205)
  ·
    refine ⟨6895564179008848252241851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36776342288047190678623205 6895564179008848252241851)
    ·
      refine ⟨10343346268513272378362777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895564179008848252241851 10343346268513272378362777)
      ·
        refine ⟨7757509701384954283772083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10343346268513272378362777 7757509701384954283772083)
        ·
          refine ⟨11636264552077431425658125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757509701384954283772083 11636264552077431425658125)
          ·
            refine ⟨4363599207029036784621797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11636264552077431425658125 4363599207029036784621797)
            ·
              refine ⟨818174851317944397116587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4363599207029036784621797 818174851317944397116587)
              ·
                refine ⟨1227262276976916595674881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818174851317944397116587 1227262276976916595674881)
                ·
                  refine ⟨920446707732687446756161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1227262276976916595674881 920446707732687446756161)
                  ·
                    refine ⟨690335030799515585067121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 920446707732687446756161 690335030799515585067121)
                    ·
                      refine ⟨517751273099636688800341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690335030799515585067121 517751273099636688800341)
                      ·
                        rfl

theorem cell23_1008317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_1008317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008317 prefixEnd_1008317 := by exact prefixLift 1008317
  have htrace : WordTrace (prefixWord ++ tailWord_1008317) baseStart_1008317 baseEnd_1008317 := by
    simpa [prefixWord, tailWord_1008317, baseEnd_1008317] using wordTrace_append hprefix tailTrace_1008317
  have hstable : (prefixWord ++ tailWord_1008317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008317).length < 2 ^ (prefixWord ++ tailWord_1008317).sum := by decide
  have hdescent : baseEnd_1008317 < baseStart_1008317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008321 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1008321 : Nat := 118140960795 + 1008321 * 2 ^ 59
def prefixEnd_1008321 : Nat := 4983230072969 + 3 ^ 40 * 1008321 * 2
def baseEnd_1008321 : Nat := 517753327022254673150323

theorem tailTrace_1008321 : CollatzResearch.WordTrace tailWord_1008321 prefixEnd_1008321 517753327022254673150323 := by
  unfold tailWord_1008321
  simp only [CollatzResearch.WordTrace]
  refine ⟨36776488180032699361768817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24517658786688466241179211 36776488180032699361768817)
  ·
    refine ⟨27582366135024524521326613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36776488180032699361768817 27582366135024524521326613)
    ·
      refine ⟨1292923412579274586937185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27582366135024524521326613 1292923412579274586937185)
      ·
        refine ⟨969692559434455940202889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1292923412579274586937185 969692559434455940202889)
        ·
          refine ⟨727269419575841955152167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969692559434455940202889 727269419575841955152167)
          ·
            refine ⟨1090904129363762932728251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727269419575841955152167 1090904129363762932728251)
            ·
              refine ⟨1636356194045644399092377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090904129363762932728251 1636356194045644399092377)
              ·
                refine ⟨1227267145534233299319283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636356194045644399092377 1227267145534233299319283)
                ·
                  refine ⟨1840900718301349948978925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227267145534233299319283 1840900718301349948978925)
                  ·
                    refine ⟨690337769363006230867097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840900718301349948978925 690337769363006230867097)
                    ·
                      refine ⟨517753327022254673150323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690337769363006230867097 517753327022254673150323)
                      ·
                        rfl

theorem cell23_1008321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1008321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008321 prefixEnd_1008321 := by exact prefixLift 1008321
  have htrace : WordTrace (prefixWord ++ tailWord_1008321) baseStart_1008321 baseEnd_1008321 := by
    simpa [prefixWord, tailWord_1008321, baseEnd_1008321] using wordTrace_append hprefix tailTrace_1008321
  have hstable : (prefixWord ++ tailWord_1008321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008321).length < 2 ^ (prefixWord ++ tailWord_1008321).sum := by decide
  have hdescent : baseEnd_1008321 < baseStart_1008321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008376 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_1008376 : Nat := 118140960795 + 1008376 * 2 ^ 59
def prefixEnd_1008376 : Nat := 4983230072969 + 3 ^ 40 * 1008376 * 2
def baseEnd_1008376 : Nat := 517781568458251957962569

theorem tailTrace_1008376 : CollatzResearch.WordTrace tailWord_1008376 prefixEnd_1008376 517781568458251957962569 := by
  unfold tailWord_1008376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18389247097416721877510491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24518996129888962503347321 18389247097416721877510491)
  ·
    refine ⟨27583870646125082816265737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18389247097416721877510491 27583870646125082816265737)
    ·
      refine ⟨20687902984593812112199303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27583870646125082816265737 20687902984593812112199303)
      ·
        refine ⟨31031854476890718168298955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20687902984593812112199303 31031854476890718168298955)
        ·
          refine ⟨46547781715336077252448433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31031854476890718168298955 46547781715336077252448433)
          ·
            refine ⟨34910836286502057939336325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46547781715336077252448433 34910836286502057939336325)
            ·
              refine ⟨6545781803719135863625561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34910836286502057939336325 6545781803719135863625561)
              ·
                refine ⟨4909336352789351897719171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545781803719135863625561 4909336352789351897719171)
                ·
                  refine ⟨7364004529184027846578757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909336352789351897719171 7364004529184027846578757)
                  ·
                    refine ⟨1380750849222005221233517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7364004529184027846578757 1380750849222005221233517)
                    ·
                      refine ⟨517781568458251957962569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1380750849222005221233517 517781568458251957962569)
                      ·
                        rfl

theorem cell23_1008376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_1008376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008376 prefixEnd_1008376 := by exact prefixLift 1008376
  have htrace : WordTrace (prefixWord ++ tailWord_1008376) baseStart_1008376 baseEnd_1008376 := by
    simpa [prefixWord, tailWord_1008376, baseEnd_1008376] using wordTrace_append hprefix tailTrace_1008376
  have hstable : (prefixWord ++ tailWord_1008376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008376).length < 2 ^ (prefixWord ++ tailWord_1008376).sum := by decide
  have hdescent : baseEnd_1008376 < baseStart_1008376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008393 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 3]
def baseStart_1008393 : Nat := 118140960795 + 1008393 * 2 ^ 59
def prefixEnd_1008393 : Nat := 4983230072969 + 3 ^ 40 * 1008393 * 2
def baseEnd_1008393 : Nat := 517790297629378391449991

theorem tailTrace_1008393 : CollatzResearch.WordTrace tailWord_1008393 prefixEnd_1008393 517790297629378391449991 := by
  unfold tailWord_1008393
  simp only [CollatzResearch.WordTrace]
  refine ⟨36779114235771855658389833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24519409490514570438926555 36779114235771855658389833)
  ·
    refine ⟨27584335676828891743792375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36779114235771855658389833 27584335676828891743792375)
    ·
      refine ⟨41376503515243337615688563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27584335676828891743792375 41376503515243337615688563)
      ·
        refine ⟨62064755272865006423532845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41376503515243337615688563 62064755272865006423532845)
        ·
          refine ⟨23274283227324377408824817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62064755272865006423532845 23274283227324377408824817)
          ·
            refine ⟨17455712420493283056618613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23274283227324377408824817 17455712420493283056618613)
            ·
              refine ⟨1636473039421245286557995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17455712420493283056618613 1636473039421245286557995)
              ·
                refine ⟨2454709559131867929836993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636473039421245286557995 2454709559131867929836993)
                ·
                  refine ⟨1841032169348900947377745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2454709559131867929836993 1841032169348900947377745)
                  ·
                    refine ⟨1380774127011675710533309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1841032169348900947377745 1380774127011675710533309)
                    ·
                      refine ⟨517790297629378391449991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1380774127011675710533309 517790297629378391449991)
                      ·
                        rfl

theorem cell23_1008393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_1008393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008393 prefixEnd_1008393 := by exact prefixLift 1008393
  have htrace : WordTrace (prefixWord ++ tailWord_1008393) baseStart_1008393 baseEnd_1008393 := by
    simpa [prefixWord, tailWord_1008393, baseEnd_1008393] using wordTrace_append hprefix tailTrace_1008393
  have hstable : (prefixWord ++ tailWord_1008393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008393).length < 2 ^ (prefixWord ++ tailWord_1008393).sum := by decide
  have hdescent : baseEnd_1008393 < baseStart_1008393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008416 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1008416 : Nat := 118140960795 + 1008416 * 2 ^ 59
def prefixEnd_1008416 : Nat := 4983230072969 + 3 ^ 40 * 1008416 * 2
def baseEnd_1008416 : Nat := 517802107684431801462385

theorem tailTrace_1008416 : CollatzResearch.WordTrace tailWord_1008416 prefixEnd_1008416 517802107684431801462385 := by
  unfold tailWord_1008416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18389976557344265293238551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24519968743125687057651401 18389976557344265293238551)
  ·
    refine ⟨27584964836016397939857827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18389976557344265293238551 27584964836016397939857827)
    ·
      refine ⟨41377447254024596909786741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27584964836016397939857827 41377447254024596909786741)
      ·
        refine ⟨3879135680064805960292507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41377447254024596909786741 3879135680064805960292507)
        ·
          refine ⟨5818703520097208940438761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3879135680064805960292507 5818703520097208940438761)
          ·
            refine ⟨4364027640072906705329071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5818703520097208940438761 4364027640072906705329071)
            ·
              refine ⟨6546041460109360057993607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364027640072906705329071 6546041460109360057993607)
              ·
                refine ⟨9819062190164040086990411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546041460109360057993607 9819062190164040086990411)
                ·
                  refine ⟨14728593285246060130485617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9819062190164040086990411 14728593285246060130485617)
                  ·
                    refine ⟨11046444963934545097864213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14728593285246060130485617 11046444963934545097864213)
                    ·
                      refine ⟨517802107684431801462385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11046444963934545097864213 517802107684431801462385)
                      ·
                        rfl

theorem cell23_1008416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1008416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008416 prefixEnd_1008416 := by exact prefixLift 1008416
  have htrace : WordTrace (prefixWord ++ tailWord_1008416) baseStart_1008416 baseEnd_1008416 := by
    simpa [prefixWord, tailWord_1008416, baseEnd_1008416] using wordTrace_append hprefix tailTrace_1008416
  have hstable : (prefixWord ++ tailWord_1008416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008416).length < 2 ^ (prefixWord ++ tailWord_1008416).sum := by decide
  have hdescent : baseEnd_1008416 < baseStart_1008416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008433 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 3, 5, 2]
def baseStart_1008433 : Nat := 118140960795 + 1008433 * 2 ^ 59
def prefixEnd_1008433 : Nat := 4983230072969 + 3 ^ 40 * 1008433 * 2
def baseEnd_1008433 : Nat := 517810836855558234949807

theorem tailTrace_1008433 : CollatzResearch.WordTrace tailWord_1008433 prefixEnd_1008433 517810836855558234949807 := by
  unfold tailWord_1008433
  simp only [CollatzResearch.WordTrace]
  refine ⟨36780573155626942489845953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24520382103751294993230635 36780573155626942489845953)
  ·
    refine ⟨27585429866720206867384465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36780573155626942489845953 27585429866720206867384465)
    ·
      refine ⟨20689072400040155150538349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27585429866720206867384465 20689072400040155150538349)
      ·
        refine ⟨7758402150015058181451881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20689072400040155150538349 7758402150015058181451881)
        ·
          refine ⟨5818801612511293636088911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7758402150015058181451881 5818801612511293636088911)
          ·
            refine ⟨8728202418766940454133367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818801612511293636088911 8728202418766940454133367)
            ·
              refine ⟨13092303628150410681200051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728202418766940454133367 13092303628150410681200051)
              ·
                refine ⟨19638455442225616021800077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13092303628150410681200051 19638455442225616021800077)
                ·
                  refine ⟨7364420790834606008175029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19638455442225616021800077 7364420790834606008175029)
                  ·
                    refine ⟨690414449140744313266409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7364420790834606008175029 690414449140744313266409)
                    ·
                      refine ⟨517810836855558234949807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690414449140744313266409 517810836855558234949807)
                      ·
                        rfl

theorem cell23_1008433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_1008433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008433 prefixEnd_1008433 := by exact prefixLift 1008433
  have htrace : WordTrace (prefixWord ++ tailWord_1008433) baseStart_1008433 baseEnd_1008433 := by
    simpa [prefixWord, tailWord_1008433, baseEnd_1008433] using wordTrace_append hprefix tailTrace_1008433
  have hstable : (prefixWord ++ tailWord_1008433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008433).length < 2 ^ (prefixWord ++ tailWord_1008433).sum := by decide
  have hdescent : baseEnd_1008433 < baseStart_1008433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008456 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 3, 6]
def baseStart_1008456 : Nat := 118140960795 + 1008456 * 2 ^ 59
def prefixEnd_1008456 : Nat := 4983230072969 + 3 ^ 40 * 1008456 * 2
def baseEnd_1008456 : Nat := 172607548970203881654067

theorem tailTrace_1008456 : CollatzResearch.WordTrace tailWord_1008456 prefixEnd_1008456 172607548970203881654067 := by
  unfold tailWord_1008456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18390706017271808708966611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24520941356362411611955481 18390706017271808708966611)
  ·
    refine ⟨27586059025907713063449917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18390706017271808708966611 27586059025907713063449917)
    ·
      refine ⟨10344772134715392398793719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27586059025907713063449917 10344772134715392398793719)
      ·
        refine ⟨15517158202073088598190579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10344772134715392398793719 15517158202073088598190579)
        ·
          refine ⟨23275737303109632897285869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15517158202073088598190579 23275737303109632897285869)
          ·
            refine ⟨8728401488666112336482201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23275737303109632897285869 8728401488666112336482201)
            ·
              refine ⟨6546301116499584252361651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8728401488666112336482201 6546301116499584252361651)
              ·
                refine ⟨9819451674749376378542477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546301116499584252361651 9819451674749376378542477)
                ·
                  refine ⟨3682294378031016141953429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9819451674749376378542477 3682294378031016141953429)
                  ·
                    refine ⟨172607548970203881654067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3682294378031016141953429 172607548970203881654067)
                    ·
                      rfl

theorem cell23_1008456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_1008456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008456 prefixEnd_1008456 := by exact prefixLift 1008456
  have htrace : WordTrace (prefixWord ++ tailWord_1008456) baseStart_1008456 baseEnd_1008456 := by
    simpa [prefixWord, tailWord_1008456, baseEnd_1008456] using wordTrace_append hprefix tailTrace_1008456
  have hstable : (prefixWord ++ tailWord_1008456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008456).length < 2 ^ (prefixWord ++ tailWord_1008456).sum := by decide
  have hdescent : baseEnd_1008456 < baseStart_1008456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008457 : List Nat := [1, 2, 1, 1, 2, 5, 3, 3, 1, 1, 3]
def baseStart_1008457 : Nat := 118140960795 + 1008457 * 2 ^ 59
def prefixEnd_1008457 : Nat := 4983230072969 + 3 ^ 40 * 1008457 * 2
def baseEnd_1008457 : Nat := 517823160391266141049697

theorem tailTrace_1008457 : CollatzResearch.WordTrace tailWord_1008457 prefixEnd_1008457 517823160391266141049697 := by
  unfold tailWord_1008457
  simp only [CollatzResearch.WordTrace]
  refine ⟨36781448507539994588719625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24520965671693329725813083 36781448507539994588719625)
  ·
    refine ⟨27586086380654995941539719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36781448507539994588719625 27586086380654995941539719)
    ·
      refine ⟨41379129570982493912309579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27586086380654995941539719 41379129570982493912309579)
      ·
        refine ⟨62068694356473740868464369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41379129570982493912309579 62068694356473740868464369)
        ·
          refine ⟨46551520767355305651348277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62068694356473740868464369 46551520767355305651348277)
          ·
            refine ⟨4364205071939559904813901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46551520767355305651348277 4364205071939559904813901)
            ·
              refine ⟨1636576901977334964305213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4364205071939559904813901 1636576901977334964305213)
              ·
                refine ⟨613716338241500611614455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1636576901977334964305213 613716338241500611614455)
                ·
                  refine ⟨920574507362250917421683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613716338241500611614455 920574507362250917421683)
                  ·
                    refine ⟨1380861761043376376132525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 920574507362250917421683 1380861761043376376132525)
                    ·
                      refine ⟨517823160391266141049697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1380861761043376376132525 517823160391266141049697)
                      ·
                        rfl

theorem cell23_1008457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 1, 3].length) (baseStart_1008457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008457 prefixEnd_1008457 := by exact prefixLift 1008457
  have htrace : WordTrace (prefixWord ++ tailWord_1008457) baseStart_1008457 baseEnd_1008457 := by
    simpa [prefixWord, tailWord_1008457, baseEnd_1008457] using wordTrace_append hprefix tailTrace_1008457
  have hstable : (prefixWord ++ tailWord_1008457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008457).length < 2 ^ (prefixWord ++ tailWord_1008457).sum := by decide
  have hdescent : baseEnd_1008457 < baseStart_1008457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008473 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 4, 4]
def baseStart_1008473 : Nat := 118140960795 + 1008473 * 2 ^ 59
def prefixEnd_1008473 : Nat := 4983230072969 + 3 ^ 40 * 1008473 * 2
def baseEnd_1008473 : Nat := 172610458693912692816541

theorem tailTrace_1008473 : CollatzResearch.WordTrace tailWord_1008473 prefixEnd_1008473 172610458693912692816541 := by
  unfold tailWord_1008473
  simp only [CollatzResearch.WordTrace]
  refine ⟨36782032075482029321302073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24521354716988019547534715 36782032075482029321302073)
  ·
    refine ⟨27586524056611521990976555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36782032075482029321302073 27586524056611521990976555)
    ·
      refine ⟨41379786084917282986464833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27586524056611521990976555 41379786084917282986464833)
      ·
        refine ⟨31034839563687962239848625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41379786084917282986464833 31034839563687962239848625)
        ·
          refine ⟨23276129672765971679886469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31034839563687962239848625 23276129672765971679886469)
          ·
            refine ⟨4364274313643619689978713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23276129672765971679886469 4364274313643619689978713)
            ·
              refine ⟨3273205735232714767484035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364274313643619689978713 3273205735232714767484035)
              ·
                refine ⟨4909808602849072151226053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273205735232714767484035 4909808602849072151226053)
                ·
                  refine ⟨920589113034201028354885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4909808602849072151226053 920589113034201028354885)
                  ·
                    refine ⟨172610458693912692816541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 920589113034201028354885 172610458693912692816541)
                    ·
                      rfl

theorem cell23_1008473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 4].length) (baseStart_1008473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008473 prefixEnd_1008473 := by exact prefixLift 1008473
  have htrace : WordTrace (prefixWord ++ tailWord_1008473) baseStart_1008473 baseEnd_1008473 := by
    simpa [prefixWord, tailWord_1008473, baseEnd_1008473] using wordTrace_append hprefix tailTrace_1008473
  have hstable : (prefixWord ++ tailWord_1008473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008473).length < 2 ^ (prefixWord ++ tailWord_1008473).sum := by decide
  have hdescent : baseEnd_1008473 < baseStart_1008473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008474 : List Nat := [3, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3]
def baseStart_1008474 : Nat := 118140960795 + 1008474 * 2 ^ 59
def prefixEnd_1008474 : Nat := 4983230072969 + 3 ^ 40 * 1008474 * 2
def baseEnd_1008474 : Nat := 517831889562392574537119

theorem tailTrace_1008474 : CollatzResearch.WordTrace tailWord_1008474 prefixEnd_1008474 517831889562392574537119 := by
  unfold tailWord_1008474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195517137119601623022119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24521379032318937661392317 9195517137119601623022119)
  ·
    refine ⟨13793275705679402434533179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9195517137119601623022119 13793275705679402434533179)
    ·
      refine ⟨20689913558519103651799769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13793275705679402434533179 20689913558519103651799769)
      ·
        refine ⟨15517435168889327738849827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20689913558519103651799769 15517435168889327738849827)
        ·
          refine ⟨23276152753333991608274741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15517435168889327738849827 23276152753333991608274741)
          ·
            refine ⟨2182139320625061713275757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23276152753333991608274741 2182139320625061713275757)
            ·
              refine ⟨818302245234398142478409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2182139320625061713275757 818302245234398142478409)
              ·
                refine ⟨613726683925798606858807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818302245234398142478409 613726683925798606858807)
                ·
                  refine ⟨920590025888697910288211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613726683925798606858807 920590025888697910288211)
                  ·
                    refine ⟨1380885038833046865432317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 920590025888697910288211 1380885038833046865432317)
                    ·
                      refine ⟨517831889562392574537119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1380885038833046865432317 517831889562392574537119)
                      ·
                        rfl

theorem cell23_1008474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_1008474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008474 prefixEnd_1008474 := by exact prefixLift 1008474
  have htrace : WordTrace (prefixWord ++ tailWord_1008474) baseStart_1008474 baseEnd_1008474 := by
    simpa [prefixWord, tailWord_1008474, baseEnd_1008474] using wordTrace_append hprefix tailTrace_1008474
  have hstable : (prefixWord ++ tailWord_1008474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008474).length < 2 ^ (prefixWord ++ tailWord_1008474).sum := by decide
  have hdescent : baseEnd_1008474 < baseStart_1008474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008483 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1008483 : Nat := 118140960795 + 1008483 * 2 ^ 59
def prefixEnd_1008483 : Nat := 4983230072969 + 3 ^ 40 * 1008483 * 2
def baseEnd_1008483 : Nat := 517836510888283039324577

theorem tailTrace_1008483 : CollatzResearch.WordTrace tailWord_1008483 prefixEnd_1008483 517836510888283039324577 := by
  unfold tailWord_1008483
  simp only [CollatzResearch.WordTrace]
  refine ⟨36782396805445801029166103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24521597870297200686110735 36782396805445801029166103)
  ·
    refine ⟨55173595208168701543749155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36782396805445801029166103 55173595208168701543749155)
    ·
      refine ⟨82760392812253052315623733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55173595208168701543749155 82760392812253052315623733)
      ·
        refine ⟨7758786826148723654589725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82760392812253052315623733 7758786826148723654589725)
        ·
          refine ⟨2909545059805771370471147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7758786826148723654589725 2909545059805771370471147)
          ·
            refine ⟨4364317589708657055706721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909545059805771370471147 4364317589708657055706721)
            ·
              refine ⟨3273238192281492791780041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364317589708657055706721 3273238192281492791780041)
              ·
                refine ⟨2454928644211119593835031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273238192281492791780041 2454928644211119593835031)
                ·
                  refine ⟨3682392966316679390752547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454928644211119593835031 3682392966316679390752547)
                  ·
                    refine ⟨5523589449475019086128821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3682392966316679390752547 5523589449475019086128821)
                    ·
                      refine ⟨517836510888283039324577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5523589449475019086128821 517836510888283039324577)
                      ·
                        rfl

theorem cell23_1008483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1008483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008483 prefixEnd_1008483 := by exact prefixLift 1008483
  have htrace : WordTrace (prefixWord ++ tailWord_1008483) baseStart_1008483 baseEnd_1008483 := by
    simpa [prefixWord, tailWord_1008483, baseEnd_1008483] using wordTrace_append hprefix tailTrace_1008483
  have hstable : (prefixWord ++ tailWord_1008483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008483).length < 2 ^ (prefixWord ++ tailWord_1008483).sum := by decide
  have hdescent : baseEnd_1008483 < baseStart_1008483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008493 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1008493 : Nat := 118140960795 + 1008493 * 2 ^ 59
def prefixEnd_1008493 : Nat := 4983230072969 + 3 ^ 40 * 1008493 * 2
def baseEnd_1008493 : Nat := 517841645694828000199531

theorem tailTrace_1008493 : CollatzResearch.WordTrace tailWord_1008493 prefixEnd_1008493 517841645694828000199531 := by
  unfold tailWord_1008493
  simp only [CollatzResearch.WordTrace]
  refine ⟨36782761535409572737030133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24521841023606381824686755 36782761535409572737030133)
  ·
    refine ⟨3448383893944647444096575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36782761535409572737030133 3448383893944647444096575)
    ·
      refine ⟨5172575840916971166144863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448383893944647444096575 5172575840916971166144863)
      ·
        refine ⟨7758863761375456749217295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172575840916971166144863 7758863761375456749217295)
        ·
          refine ⟨11638295642063185123825943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758863761375456749217295 11638295642063185123825943)
          ·
            refine ⟨17457443463094777685738915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11638295642063185123825943 17457443463094777685738915)
            ·
              refine ⟨26186165194642166528608373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17457443463094777685738915 26186165194642166528608373)
              ·
                refine ⟨2454952986997703112057035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26186165194642166528608373 2454952986997703112057035)
                ·
                  refine ⟨3682429480496554668085553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454952986997703112057035 3682429480496554668085553)
                  ·
                    refine ⟨2761822110372416001064165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682429480496554668085553 2761822110372416001064165)
                    ·
                      refine ⟨517841645694828000199531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2761822110372416001064165 517841645694828000199531)
                      ·
                        rfl

theorem cell23_1008493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1008493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008493 prefixEnd_1008493 := by exact prefixLift 1008493
  have htrace : WordTrace (prefixWord ++ tailWord_1008493) baseStart_1008493 baseEnd_1008493 := by
    simpa [prefixWord, tailWord_1008493, baseEnd_1008493] using wordTrace_append hprefix tailTrace_1008493
  have hstable : (prefixWord ++ tailWord_1008493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008493).length < 2 ^ (prefixWord ++ tailWord_1008493).sum := by decide
  have hdescent : baseEnd_1008493 < baseStart_1008493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008494 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1008494 : Nat := 118140960795 + 1008494 * 2 ^ 59
def prefixEnd_1008494 : Nat := 4983230072969 + 3 ^ 40 * 1008494 * 2
def baseEnd_1008494 : Nat := 172614053058494165429009

theorem tailTrace_1008494 : CollatzResearch.WordTrace tailWord_1008494 prefixEnd_1008494 172614053058494165429009 := by
  unfold tailWord_1008494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597849751050743738477067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24521865338937299938544357 4597849751050743738477067)
  ·
    refine ⟨6896774626576115607715601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597849751050743738477067 6896774626576115607715601)
    ·
      refine ⟨5172580969932086705786701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6896774626576115607715601 5172580969932086705786701)
      ·
        refine ⟨1939717863724532514670013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5172580969932086705786701 1939717863724532514670013)
        ·
          refine ⟨727394198896699693001255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1939717863724532514670013 727394198896699693001255)
          ·
            refine ⟨1091091298345049539501883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727394198896699693001255 1091091298345049539501883)
            ·
              refine ⟨1636636947517574309252825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091091298345049539501883 1636636947517574309252825)
              ·
                refine ⟨1227477710638180731939619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636636947517574309252825 1227477710638180731939619)
                ·
                  refine ⟨1841216565957271097909429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227477710638180731939619 1841216565957271097909429)
                  ·
                    refine ⟨172614053058494165429009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1841216565957271097909429 172614053058494165429009)
                    ·
                      rfl

theorem cell23_1008494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1008494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008494 prefixEnd_1008494 := by exact prefixLift 1008494
  have htrace : WordTrace (prefixWord ++ tailWord_1008494) baseStart_1008494 baseEnd_1008494 := by
    simpa [prefixWord, tailWord_1008494, baseEnd_1008494] using wordTrace_append hprefix tailTrace_1008494
  have hstable : (prefixWord ++ tailWord_1008494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008494).length < 2 ^ (prefixWord ++ tailWord_1008494).sum := by decide
  have hdescent : baseEnd_1008494 < baseStart_1008494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008517 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 1, 2, 3]
def baseStart_1008517 : Nat := 118140960795 + 1008517 * 2 ^ 59
def prefixEnd_1008517 : Nat := 4983230072969 + 3 ^ 40 * 1008517 * 2
def baseEnd_1008517 : Nat := 517853969230535906299421

theorem tailTrace_1008517 : CollatzResearch.WordTrace tailWord_1008517 prefixEnd_1008517 517853969230535906299421 := by
  unfold tailWord_1008517
  simp only [CollatzResearch.WordTrace]
  refine ⟨36783636887322624835903805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24522424591548416557269203 36783636887322624835903805)
  ·
    refine ⟨13793863832745984313463927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36783636887322624835903805 13793863832745984313463927)
    ·
      refine ⟨20690795749118976470195891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13793863832745984313463927 20690795749118976470195891)
      ·
        refine ⟨31036193623678464705293837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20690795749118976470195891 31036193623678464705293837)
        ·
          refine ⟨11638572608879424264485189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31036193623678464705293837 11638572608879424264485189)
          ·
            refine ⟨2182232364164892049590973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11638572608879424264485189 2182232364164892049590973)
            ·
              refine ⟨818337136561834518596615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2182232364164892049590973 818337136561834518596615)
              ·
                refine ⟨1227505704842751777894923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818337136561834518596615 1227505704842751777894923)
                ·
                  refine ⟨1841258557264127666842385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227505704842751777894923 1841258557264127666842385)
                  ·
                    refine ⟨1380943917948095750131789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1841258557264127666842385 1380943917948095750131789)
                    ·
                      refine ⟨517853969230535906299421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1380943917948095750131789 517853969230535906299421)
                      ·
                        rfl

theorem cell23_1008517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_1008517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008517 prefixEnd_1008517 := by exact prefixLift 1008517
  have htrace : WordTrace (prefixWord ++ tailWord_1008517) baseStart_1008517 baseEnd_1008517 := by
    simpa [prefixWord, tailWord_1008517, baseEnd_1008517] using wordTrace_append hprefix tailTrace_1008517
  have hstable : (prefixWord ++ tailWord_1008517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008517).length < 2 ^ (prefixWord ++ tailWord_1008517).sum := by decide
  have hdescent : baseEnd_1008517 < baseStart_1008517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008534 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1008534 : Nat := 118140960795 + 1008534 * 2 ^ 59
def prefixEnd_1008534 : Nat := 4983230072969 + 3 ^ 40 * 1008534 * 2
def baseEnd_1008534 : Nat := 517862698401662339786843

theorem tailTrace_1008534 : CollatzResearch.WordTrace tailWord_1008534 prefixEnd_1008534 517862698401662339786843 := by
  unfold tailWord_1008534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299016058016314796204541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24522837952174024492848437 2299016058016314796204541)
  ·
    refine ⟨862131021756118048576703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2299016058016314796204541 862131021756118048576703)
    ·
      refine ⟨1293196532634177072865055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862131021756118048576703 1293196532634177072865055)
      ·
        refine ⟨1939794798951265609297583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293196532634177072865055 1939794798951265609297583)
        ·
          refine ⟨2909692198426898413946375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939794798951265609297583 2909692198426898413946375)
          ·
            refine ⟨4364538297640347620919563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909692198426898413946375 4364538297640347620919563)
            ·
              refine ⟨6546807446460521431379345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364538297640347620919563 6546807446460521431379345)
              ·
                refine ⟨4910105584845391073534509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6546807446460521431379345 4910105584845391073534509)
                ·
                  refine ⟨1841289594317021652575441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4910105584845391073534509 1841289594317021652575441)
                  ·
                    refine ⟨1380967195737766239431581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1841289594317021652575441 1380967195737766239431581)
                    ·
                      refine ⟨517862698401662339786843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1380967195737766239431581 517862698401662339786843)
                      ·
                        rfl

theorem cell23_1008534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1008534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008534 prefixEnd_1008534 := by exact prefixLift 1008534
  have htrace : WordTrace (prefixWord ++ tailWord_1008534) baseStart_1008534 baseEnd_1008534 := by
    simpa [prefixWord, tailWord_1008534, baseEnd_1008534] using wordTrace_append hprefix tailTrace_1008534
  have hstable : (prefixWord ++ tailWord_1008534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008534).length < 2 ^ (prefixWord ++ tailWord_1008534).sum := by decide
  have hdescent : baseEnd_1008534 < baseStart_1008534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008570 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2]
def baseStart_1008570 : Nat := 118140960795 + 1008570 * 2 ^ 59
def prefixEnd_1008570 : Nat := 4983230072969 + 3 ^ 40 * 1008570 * 2
def baseEnd_1008570 : Nat := 517881183705224198936677

theorem tailTrace_1008570 : CollatzResearch.WordTrace tailWord_1008570 prefixEnd_1008570 517881183705224198936677 := by
  unfold tailWord_1008570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196392489032653721895791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24523713304087076591722109 9196392489032653721895791)
  ·
    refine ⟨13794588733548980582843687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9196392489032653721895791 13794588733548980582843687)
    ·
      refine ⟨20691883100323470874265531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13794588733548980582843687 20691883100323470874265531)
      ·
        refine ⟨31037824650485206311398297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20691883100323470874265531 31037824650485206311398297)
        ·
          refine ⟨23278368487863904733548723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31037824650485206311398297 23278368487863904733548723)
          ·
            refine ⟨34917552731795857100323085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23278368487863904733548723 34917552731795857100323085)
            ·
              refine ⟨13094082274423446412621157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34917552731795857100323085 13094082274423446412621157)
              ·
                refine ⟨2455140426454396202366467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13094082274423446412621157 2455140426454396202366467)
                ·
                  refine ⟨3682710639681594303549701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455140426454396202366467 3682710639681594303549701)
                  ·
                    refine ⟨690508244940298931915569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3682710639681594303549701 690508244940298931915569)
                    ·
                      refine ⟨517881183705224198936677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690508244940298931915569 517881183705224198936677)
                      ·
                        rfl

theorem cell23_1008570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_1008570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008570 prefixEnd_1008570 := by exact prefixLift 1008570
  have htrace : WordTrace (prefixWord ++ tailWord_1008570) baseStart_1008570 baseEnd_1008570 := by
    simpa [prefixWord, tailWord_1008570, baseEnd_1008570] using wordTrace_append hprefix tailTrace_1008570
  have hstable : (prefixWord ++ tailWord_1008570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008570).length < 2 ^ (prefixWord ++ tailWord_1008570).sum := by decide
  have hdescent : baseEnd_1008570 < baseStart_1008570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008583 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1008583 : Nat := 118140960795 + 1008583 * 2 ^ 59
def prefixEnd_1008583 : Nat := 4983230072969 + 3 ^ 40 * 1008583 * 2
def baseEnd_1008583 : Nat := 517887858953732648074117

theorem tailTrace_1008583 : CollatzResearch.WordTrace tailWord_1008583 prefixEnd_1008583 517887858953732648074117 := by
  unfold tailWord_1008583
  simp only [CollatzResearch.WordTrace]
  refine ⟨36786044105083518107806403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24524029403389012071870935 36786044105083518107806403)
  ·
    refine ⟨55179066157625277161709605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36786044105083518107806403 55179066157625277161709605)
    ·
      refine ⟨10346074904554739467820551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55179066157625277161709605 10346074904554739467820551)
      ·
        refine ⟨15519112356832109201730827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10346074904554739467820551 15519112356832109201730827)
        ·
          refine ⟨23278668535248163802596241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15519112356832109201730827 23278668535248163802596241)
          ·
            refine ⟨17459001401436122851947181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23278668535248163802596241 17459001401436122851947181)
            ·
              refine ⟨6547125525538546069480193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17459001401436122851947181 6547125525538546069480193)
              ·
                refine ⟨4910344144153909552110145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6547125525538546069480193 4910344144153909552110145)
                ·
                  refine ⟨3682758108115432164082609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910344144153909552110145 3682758108115432164082609)
                  ·
                    refine ⟨2762068581086574123061957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682758108115432164082609 2762068581086574123061957)
                    ·
                      refine ⟨517887858953732648074117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2762068581086574123061957 517887858953732648074117)
                      ·
                        rfl

theorem cell23_1008583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1008583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008583 prefixEnd_1008583 := by exact prefixLift 1008583
  have htrace : WordTrace (prefixWord ++ tailWord_1008583) baseStart_1008583 baseEnd_1008583 := by
    simpa [prefixWord, tailWord_1008583, baseEnd_1008583] using wordTrace_append hprefix tailTrace_1008583
  have hstable : (prefixWord ++ tailWord_1008583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008583).length < 2 ^ (prefixWord ++ tailWord_1008583).sum := by decide
  have hdescent : baseEnd_1008583 < baseStart_1008583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008587 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 4, 2, 2]
def baseStart_1008587 : Nat := 118140960795 + 1008587 * 2 ^ 59
def prefixEnd_1008587 : Nat := 4983230072969 + 3 ^ 40 * 1008587 * 2
def baseEnd_1008587 : Nat := 517889912876350632424099

theorem tailTrace_1008587 : CollatzResearch.WordTrace tailWord_1008587 prefixEnd_1008587 517889912876350632424099 := by
  unfold tailWord_1008587
  simp only [CollatzResearch.WordTrace]
  refine ⟨36786189997069026790952015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24524126664712684527301343 36786189997069026790952015)
  ·
    refine ⟨55179284995603540186428023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36786189997069026790952015 55179284995603540186428023)
    ·
      refine ⟨82768927493405310279642035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55179284995603540186428023 82768927493405310279642035)
      ·
        refine ⟨124153391240107965419463053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82768927493405310279642035 124153391240107965419463053)
        ·
          refine ⟨46557521715040487032298645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124153391240107965419463053 46557521715040487032298645)
          ·
            refine ⟨2182383830392522829638999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46557521715040487032298645 2182383830392522829638999)
            ·
              refine ⟨3273575745588784244458499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182383830392522829638999 3273575745588784244458499)
              ·
                refine ⟨4910363618383176366687749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273575745588784244458499 4910363618383176366687749)
                ·
                  refine ⟨920693178446845568753953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4910363618383176366687749 920693178446845568753953)
                  ·
                    refine ⟨690519883835134176565465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 920693178446845568753953 690519883835134176565465)
                    ·
                      refine ⟨517889912876350632424099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690519883835134176565465 517889912876350632424099)
                      ·
                        rfl

theorem cell23_1008587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 2, 2].length) (baseStart_1008587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008587 prefixEnd_1008587 := by exact prefixLift 1008587
  have htrace : WordTrace (prefixWord ++ tailWord_1008587) baseStart_1008587 baseEnd_1008587 := by
    simpa [prefixWord, tailWord_1008587, baseEnd_1008587] using wordTrace_append hprefix tailTrace_1008587
  have hstable : (prefixWord ++ tailWord_1008587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008587).length < 2 ^ (prefixWord ++ tailWord_1008587).sum := by decide
  have hdescent : baseEnd_1008587 < baseStart_1008587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008593 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 7]
def baseStart_1008593 : Nat := 118140960795 + 1008593 * 2 ^ 59
def prefixEnd_1008593 : Nat := 4983230072969 + 3 ^ 40 * 1008593 * 2
def baseEnd_1008593 : Nat := 57543665973364178772119

theorem tailTrace_1008593 : CollatzResearch.WordTrace tailWord_1008593 prefixEnd_1008593 57543665973364178772119 := by
  unfold tailWord_1008593
  simp only [CollatzResearch.WordTrace]
  refine ⟨36786408835047289815670433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24524272556698193210446955 36786408835047289815670433)
  ·
    refine ⟨27589806626285467361752825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36786408835047289815670433 27589806626285467361752825)
    ·
      refine ⟨20692354969714100521314619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27589806626285467361752825 20692354969714100521314619)
      ·
        refine ⟨31038532454571150781971929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20692354969714100521314619 31038532454571150781971929)
        ·
          refine ⟨23278899340928363086478947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31038532454571150781971929 23278899340928363086478947)
          ·
            refine ⟨34918349011392544629718421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23278899340928363086478947 34918349011392544629718421)
            ·
              refine ⟨1636797609909025529518051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34918349011392544629718421 1636797609909025529518051)
              ·
                refine ⟨2455196414863538294277077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636797609909025529518051 2455196414863538294277077)
                ·
                  refine ⟨57543665973364178772119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2455196414863538294277077 57543665973364178772119)
                  ·
                    rfl

theorem cell23_1008593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 7].length) (baseStart_1008593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008593 prefixEnd_1008593 := by exact prefixLift 1008593
  have htrace : WordTrace (prefixWord ++ tailWord_1008593) baseStart_1008593 baseEnd_1008593 := by
    simpa [prefixWord, tailWord_1008593, baseEnd_1008593] using wordTrace_append hprefix tailTrace_1008593
  have hstable : (prefixWord ++ tailWord_1008593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008593).length < 2 ^ (prefixWord ++ tailWord_1008593).sum := by decide
  have hdescent : baseEnd_1008593 < baseStart_1008593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008623 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 1, 7]
def baseStart_1008623 : Nat := 118140960795 + 1008623 * 2 ^ 59
def prefixEnd_1008623 : Nat := 4983230072969 + 3 ^ 40 * 1008623 * 2
def baseEnd_1008623 : Nat := 172636132726637497191311

theorem tailTrace_1008623 : CollatzResearch.WordTrace tailWord_1008623 prefixEnd_1008623 172636132726637497191311 := by
  unfold tailWord_1008623
  simp only [CollatzResearch.WordTrace]
  refine ⟨36787503024938604939262523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24525002016625736626175015 36787503024938604939262523)
  ·
    refine ⟨55181254537407907408893785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36787503024938604939262523 55181254537407907408893785)
    ·
      refine ⟨41385940903055930556670339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55181254537407907408893785 41385940903055930556670339)
      ·
        refine ⟨62078911354583895835005509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41385940903055930556670339 62078911354583895835005509)
        ·
          refine ⟨11639795878984480469063533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62078911354583895835005509 11639795878984480469063533)
          ·
            refine ⟨4364923454619180175898825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11639795878984480469063533 4364923454619180175898825)
            ·
              refine ⟨3273692590964385131924119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364923454619180175898825 3273692590964385131924119)
              ·
                refine ⟨4910538886446577697886179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273692590964385131924119 4910538886446577697886179)
                ·
                  refine ⟨7365808329669866546829269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910538886446577697886179 7365808329669866546829269)
                  ·
                    refine ⟨172636132726637497191311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7365808329669866546829269 172636132726637497191311)
                    ·
                      rfl

theorem cell23_1008623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_1008623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008623 prefixEnd_1008623 := by exact prefixLift 1008623
  have htrace : WordTrace (prefixWord ++ tailWord_1008623) baseStart_1008623 baseEnd_1008623 := by
    simpa [prefixWord, tailWord_1008623, baseEnd_1008623] using wordTrace_append hprefix tailTrace_1008623
  have hstable : (prefixWord ++ tailWord_1008623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008623).length < 2 ^ (prefixWord ++ tailWord_1008623).sum := by decide
  have hdescent : baseEnd_1008623 < baseStart_1008623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008633 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_1008633 : Nat := 118140960795 + 1008633 * 2 ^ 59
def prefixEnd_1008633 : Nat := 4983230072969 + 3 ^ 40 * 1008633 * 2
def baseEnd_1008633 : Nat := 517913532986457452448887

theorem tailTrace_1008633 : CollatzResearch.WordTrace tailWord_1008633 prefixEnd_1008633 517913532986457452448887 := by
  unfold tailWord_1008633
  simp only [CollatzResearch.WordTrace]
  refine ⟨36787867754902376647126553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24525245169934917764751035 36787867754902376647126553)
  ·
    refine ⟨27590900816176782485344915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36787867754902376647126553 27590900816176782485344915)
    ·
      refine ⟨41386351224265173728017373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27590900816176782485344915 41386351224265173728017373)
      ·
        refine ⟨15519881709099440148006515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41386351224265173728017373 15519881709099440148006515)
        ·
          refine ⟨23279822563649160222009773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15519881709099440148006515 23279822563649160222009773)
          ·
            refine ⟨8729933461368435083253665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23279822563649160222009773 8729933461368435083253665)
            ·
              refine ⟨6547450096026326312440249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8729933461368435083253665 6547450096026326312440249)
              ·
                refine ⟨4910587572019744734330187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6547450096026326312440249 4910587572019744734330187)
                ·
                  refine ⟨7365881358029617101495281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910587572019744734330187 7365881358029617101495281)
                  ·
                    refine ⟨5524411018522212826121461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7365881358029617101495281 5524411018522212826121461)
                    ·
                      refine ⟨517913532986457452448887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5524411018522212826121461 517913532986457452448887)
                      ·
                        rfl

theorem cell23_1008633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_1008633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008633 prefixEnd_1008633 := by exact prefixLift 1008633
  have htrace : WordTrace (prefixWord ++ tailWord_1008633) baseStart_1008633 baseEnd_1008633 := by
    simpa [prefixWord, tailWord_1008633, baseEnd_1008633] using wordTrace_append hprefix tailTrace_1008633
  have hstable : (prefixWord ++ tailWord_1008633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008633).length < 2 ^ (prefixWord ++ tailWord_1008633).sum := by decide
  have hdescent : baseEnd_1008633 < baseStart_1008633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008650 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1008650 : Nat := 118140960795 + 1008650 * 2 ^ 59
def prefixEnd_1008650 : Nat := 4983230072969 + 3 ^ 40 * 1008650 * 2
def baseEnd_1008650 : Nat := 517922262157583885936309

theorem tailTrace_1008650 : CollatzResearch.WordTrace tailWord_1008650 prefixEnd_1008650 517922262157583885936309 := by
  unfold tailWord_1008650
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197121948960197137623851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24525658530560525700330269 9197121948960197137623851)
  ·
    refine ⟨13795682923440295706435777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9197121948960197137623851 13795682923440295706435777)
    ·
      refine ⟨10346762192580221779826833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13795682923440295706435777 10346762192580221779826833)
      ·
        refine ⟨7760071644435166334870125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10346762192580221779826833 7760071644435166334870125)
        ·
          refine ⟨2910026866663187375576297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7760071644435166334870125 2910026866663187375576297)
          ·
            refine ⟨2182520149997390531682223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2910026866663187375576297 2182520149997390531682223)
            ·
              refine ⟨3273780224996085797523335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182520149997390531682223 3273780224996085797523335)
              ·
                refine ⟨4910670337494128696285003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273780224996085797523335 4910670337494128696285003)
                ·
                  refine ⟨7366005506241193044427505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910670337494128696285003 7366005506241193044427505)
                  ·
                    refine ⟨5524504129680894783320629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7366005506241193044427505 5524504129680894783320629)
                    ·
                      refine ⟨517922262157583885936309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5524504129680894783320629 517922262157583885936309)
                      ·
                        rfl

theorem cell23_1008650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1008650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008650 prefixEnd_1008650 := by exact prefixLift 1008650
  have htrace : WordTrace (prefixWord ++ tailWord_1008650) baseStart_1008650 baseEnd_1008650 := by
    simpa [prefixWord, tailWord_1008650, baseEnd_1008650] using wordTrace_append hprefix tailTrace_1008650
  have hstable : (prefixWord ++ tailWord_1008650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008650).length < 2 ^ (prefixWord ++ tailWord_1008650).sum := by decide
  have hdescent : baseEnd_1008650 < baseStart_1008650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008697 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1008697 : Nat := 118140960795 + 1008697 * 2 ^ 59
def prefixEnd_1008697 : Nat := 4983230072969 + 3 ^ 40 * 1008697 * 2
def baseEnd_1008697 : Nat := 517946395748345202048593

theorem tailTrace_1008697 : CollatzResearch.WordTrace tailWord_1008697 prefixEnd_1008697 517946395748345202048593 := by
  unfold tailWord_1008697
  simp only [CollatzResearch.WordTrace]
  refine ⟨36790202026670515577456345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24526801351113677051637563 36790202026670515577456345)
  ·
    refine ⟨27592651520002886683092259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36790202026670515577456345 27592651520002886683092259)
    ·
      refine ⟨41388977280004330024638389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27592651520002886683092259 41388977280004330024638389)
      ·
        refine ⟨3880216620000405939809849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41388977280004330024638389 3880216620000405939809849)
        ·
          refine ⟨2910162465000304454857387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3880216620000405939809849 2910162465000304454857387)
          ·
            refine ⟨4365243697500456682286081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910162465000304454857387 4365243697500456682286081)
            ·
              refine ⟨3273932773125342511714561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365243697500456682286081 3273932773125342511714561)
              ·
                refine ⟨2455449579844006883785921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273932773125342511714561 2455449579844006883785921)
                ·
                  refine ⟨1841587184883005162839441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2455449579844006883785921 1841587184883005162839441)
                  ·
                    refine ⟨1381190388662253872129581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1841587184883005162839441 1381190388662253872129581)
                    ·
                      refine ⟨517946395748345202048593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1381190388662253872129581 517946395748345202048593)
                      ·
                        rfl

theorem cell23_1008697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1008697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008697 prefixEnd_1008697 := by exact prefixLift 1008697
  have htrace : WordTrace (prefixWord ++ tailWord_1008697) baseStart_1008697 baseEnd_1008697 := by
    simpa [prefixWord, tailWord_1008697, baseEnd_1008697] using wordTrace_append hprefix tailTrace_1008697
  have hstable : (prefixWord ++ tailWord_1008697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008697).length < 2 ^ (prefixWord ++ tailWord_1008697).sum := by decide
  have hdescent : baseEnd_1008697 < baseStart_1008697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008700 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 6]
def baseStart_1008700 : Nat := 118140960795 + 1008700 * 2 ^ 59
def prefixEnd_1008700 : Nat := 4983230072969 + 3 ^ 40 * 1008700 * 2
def baseEnd_1008700 : Nat := 57549770687812076701231

theorem tailTrace_1008700 : CollatzResearch.WordTrace tailWord_1008700 prefixEnd_1008700 57549770687812076701231 := by
  unfold tailWord_1008700
  simp only [CollatzResearch.WordTrace]
  refine ⟨18395155722829823544907777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24526874297106431393210369 18395155722829823544907777)
  ·
    refine ⟨13796366792122367658680833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18395155722829823544907777 13796366792122367658680833)
    ·
      refine ⟨10347275094091775744010625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13796366792122367658680833 10347275094091775744010625)
      ·
        refine ⟨7760456320568831808007969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10347275094091775744010625 7760456320568831808007969)
        ·
          refine ⟨5820342240426623856005977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760456320568831808007969 5820342240426623856005977)
          ·
            refine ⟨4365256680319967892004483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5820342240426623856005977 4365256680319967892004483)
            ·
              refine ⟨6547885020479951838006725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365256680319967892004483 6547885020479951838006725)
              ·
                refine ⟨1227728441339990969626261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6547885020479951838006725 1227728441339990969626261)
                ·
                  refine ⟨57549770687812076701231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1227728441339990969626261 57549770687812076701231)
                  ·
                    rfl

theorem cell23_1008700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_1008700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008700 prefixEnd_1008700 := by exact prefixLift 1008700
  have htrace : WordTrace (prefixWord ++ tailWord_1008700) baseStart_1008700 baseEnd_1008700 := by
    simpa [prefixWord, tailWord_1008700, baseEnd_1008700] using wordTrace_append hprefix tailTrace_1008700
  have hstable : (prefixWord ++ tailWord_1008700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008700).length < 2 ^ (prefixWord ++ tailWord_1008700).sum := by decide
  have hdescent : baseEnd_1008700 < baseStart_1008700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008703 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_1008703 : Nat := 118140960795 + 1008703 * 2 ^ 59
def prefixEnd_1008703 : Nat := 4983230072969 + 3 ^ 40 * 1008703 * 2
def baseEnd_1008703 : Nat := 517949476632272178573565

theorem tailTrace_1008703 : CollatzResearch.WordTrace tailWord_1008703 prefixEnd_1008703 517949476632272178573565 := by
  unfold tailWord_1008703
  simp only [CollatzResearch.WordTrace]
  refine ⟨36790420864648778602174763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24526947243099185734783175 36790420864648778602174763)
  ·
    refine ⟨55185631296973167903262145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36790420864648778602174763 55185631296973167903262145)
    ·
      refine ⟨41389223472729875927446609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55185631296973167903262145 41389223472729875927446609)
      ·
        refine ⟨31041917604547406945584957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41389223472729875927446609 31041917604547406945584957)
        ·
          refine ⟨11640719101705277604594359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31041917604547406945584957 11640719101705277604594359)
          ·
            refine ⟨17461078652557916406891539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11640719101705277604594359 17461078652557916406891539)
            ·
              refine ⟨26191617978836874610337309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17461078652557916406891539 26191617978836874610337309)
              ·
                refine ⟨9821856742063827978876491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26191617978836874610337309 9821856742063827978876491)
                ·
                  refine ⟨14732785113095741968314737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9821856742063827978876491 14732785113095741968314737)
                  ·
                    refine ⟨11049588834821806476236053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14732785113095741968314737 11049588834821806476236053)
                    ·
                      refine ⟨517949476632272178573565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11049588834821806476236053 517949476632272178573565)
                      ·
                        rfl

theorem cell23_1008703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_1008703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008703 prefixEnd_1008703 := by exact prefixLift 1008703
  have htrace : WordTrace (prefixWord ++ tailWord_1008703) baseStart_1008703 baseEnd_1008703 := by
    simpa [prefixWord, tailWord_1008703, baseEnd_1008703] using wordTrace_append hprefix tailTrace_1008703
  have hstable : (prefixWord ++ tailWord_1008703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008703).length < 2 ^ (prefixWord ++ tailWord_1008703).sum := by decide
  have hdescent : baseEnd_1008703 < baseStart_1008703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008717 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1008717 : Nat := 118140960795 + 1008717 * 2 ^ 59
def prefixEnd_1008717 : Nat := 4983230072969 + 3 ^ 40 * 1008717 * 2
def baseEnd_1008717 : Nat := 57550740595715013755389

theorem tailTrace_1008717 : CollatzResearch.WordTrace tailWord_1008717 prefixEnd_1008717 57550740595715013755389 := by
  unfold tailWord_1008717
  simp only [CollatzResearch.WordTrace]
  refine ⟨36790931486598058993184405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24527287657732039328789603 36790931486598058993184405)
  ·
    refine ⟨1724574913434284015305519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36790931486598058993184405 1724574913434284015305519)
    ·
      refine ⟨2586862370151426022958279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724574913434284015305519 2586862370151426022958279)
      ·
        refine ⟨3880293555227139034437419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586862370151426022958279 3880293555227139034437419)
        ·
          refine ⟨5820440332840708551656129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880293555227139034437419 5820440332840708551656129)
          ·
            refine ⟨4365330249630531413742097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5820440332840708551656129 4365330249630531413742097)
            ·
              refine ⟨3273997687222898560306573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365330249630531413742097 3273997687222898560306573)
              ·
                refine ⟨1227749132708586960114965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3273997687222898560306573 1227749132708586960114965)
                ·
                  refine ⟨57550740595715013755389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1227749132708586960114965 57550740595715013755389)
                  ·
                    rfl

theorem cell23_1008717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1008717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008717 prefixEnd_1008717 := by exact prefixLift 1008717
  have htrace : WordTrace (prefixWord ++ tailWord_1008717) baseStart_1008717 baseEnd_1008717 := by
    simpa [prefixWord, tailWord_1008717, baseEnd_1008717] using wordTrace_append hprefix tailTrace_1008717
  have hstable : (prefixWord ++ tailWord_1008717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008717).length < 2 ^ (prefixWord ++ tailWord_1008717).sum := by decide
  have hdescent : baseEnd_1008717 < baseStart_1008717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008777 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 1, 6]
def baseStart_1008777 : Nat := 118140960795 + 1008777 * 2 ^ 59
def prefixEnd_1008777 : Nat := 4983230072969 + 3 ^ 40 * 1008777 * 2
def baseEnd_1008777 : Nat := 172662491400234963016075

theorem tailTrace_1008777 : CollatzResearch.WordTrace tailWord_1008777 prefixEnd_1008777 172662491400234963016075 := by
  unfold tailWord_1008777
  simp only [CollatzResearch.WordTrace]
  refine ⟨36793119866380689240368585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24528746577587126160245723 36793119866380689240368585)
  ·
    refine ⟨27594839899785516930276439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36793119866380689240368585 27594839899785516930276439)
    ·
      refine ⟨41392259849678275395414659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27594839899785516930276439 41392259849678275395414659)
      ·
        refine ⟨62088389774517413093121989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41392259849678275395414659 62088389774517413093121989)
        ·
          refine ⟨11641573082722014954960373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62088389774517413093121989 11641573082722014954960373)
          ·
            refine ⟨1091397476505188902027535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11641573082722014954960373 1091397476505188902027535)
            ·
              refine ⟨1637096214757783353041303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091397476505188902027535 1637096214757783353041303)
              ·
                refine ⟨2455644322136675029561955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637096214757783353041303 2455644322136675029561955)
                ·
                  refine ⟨3683466483205012544342933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455644322136675029561955 3683466483205012544342933)
                  ·
                    refine ⟨172662491400234963016075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3683466483205012544342933 172662491400234963016075)
                    ·
                      rfl

theorem cell23_1008777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_1008777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008777 prefixEnd_1008777 := by exact prefixLift 1008777
  have htrace : WordTrace (prefixWord ++ tailWord_1008777) baseStart_1008777 baseEnd_1008777 := by
    simpa [prefixWord, tailWord_1008777, baseEnd_1008777] using wordTrace_append hprefix tailTrace_1008777
  have hstable : (prefixWord ++ tailWord_1008777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008777).length < 2 ^ (prefixWord ++ tailWord_1008777).sum := by decide
  have hdescent : baseEnd_1008777 < baseStart_1008777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008787 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 3]
def baseStart_1008787 : Nat := 118140960795 + 1008787 * 2 ^ 59
def prefixEnd_1008787 : Nat := 4983230072969 + 3 ^ 40 * 1008787 * 2
def baseEnd_1008787 : Nat := 517992609007249849923179

theorem tailTrace_1008787 : CollatzResearch.WordTrace tailWord_1008787 prefixEnd_1008787 517992609007249849923179 := by
  unfold tailWord_1008787
  simp only [CollatzResearch.WordTrace]
  refine ⟨36793484596344460948232615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24528989730896307298821743 36793484596344460948232615)
  ·
    refine ⟨55190226894516691422348923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36793484596344460948232615 55190226894516691422348923)
    ·
      refine ⟨82785340341775037133523385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55190226894516691422348923 82785340341775037133523385)
      ·
        refine ⟨62089005256331277850142539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82785340341775037133523385 62089005256331277850142539)
        ·
          refine ⟨93133507884496916775213809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62089005256331277850142539 93133507884496916775213809)
          ·
            refine ⟨69850130913372687581410357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93133507884496916775213809 69850130913372687581410357)
            ·
              refine ⟨6548449773128689460757221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69850130913372687581410357 6548449773128689460757221)
              ·
                refine ⟨1227834332461629273891979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6548449773128689460757221 1227834332461629273891979)
                ·
                  refine ⟨1841751498692443910837969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227834332461629273891979 1841751498692443910837969)
                  ·
                    refine ⟨1381313624019332933128477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1841751498692443910837969 1381313624019332933128477)
                    ·
                      refine ⟨517992609007249849923179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1381313624019332933128477 517992609007249849923179)
                      ·
                        rfl

theorem cell23_1008787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 2, 3].length) (baseStart_1008787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008787 prefixEnd_1008787 := by exact prefixLift 1008787
  have htrace : WordTrace (prefixWord ++ tailWord_1008787) baseStart_1008787 baseEnd_1008787 := by
    simpa [prefixWord, tailWord_1008787, baseEnd_1008787] using wordTrace_append hprefix tailTrace_1008787
  have hstable : (prefixWord ++ tailWord_1008787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008787).length < 2 ^ (prefixWord ++ tailWord_1008787).sum := by decide
  have hdescent : baseEnd_1008787 < baseStart_1008787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008804 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_1008804 : Nat := 118140960795 + 1008804 * 2 ^ 59
def prefixEnd_1008804 : Nat := 4983230072969 + 3 ^ 40 * 1008804 * 2
def baseEnd_1008804 : Nat := 518001338178376283410601

theorem tailTrace_1008804 : CollatzResearch.WordTrace tailWord_1008804 prefixEnd_1008804 518001338178376283410601 := by
  unfold tailWord_1008804
  simp only [CollatzResearch.WordTrace]
  refine ⟨18397052318641436425800733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24529403091521915234400977 18397052318641436425800733)
  ·
    refine ⟨6898894619490538659675275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18397052318641436425800733 6898894619490538659675275)
    ·
      refine ⟨10348341929235807989512913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6898894619490538659675275 10348341929235807989512913)
      ·
        refine ⟨7761256446926855992134685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10348341929235807989512913 7761256446926855992134685)
        ·
          refine ⟨2910471167597570997050507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7761256446926855992134685 2910471167597570997050507)
          ·
            refine ⟨4365706751396356495575761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910471167597570997050507 4365706751396356495575761)
            ·
              refine ⟨3274280063547267371681821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365706751396356495575761 3274280063547267371681821)
              ·
                refine ⟨1227855023830225264380683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3274280063547267371681821 1227855023830225264380683)
                ·
                  refine ⟨1841782535745337896571025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227855023830225264380683 1841782535745337896571025)
                  ·
                    refine ⟨1381336901809003422428269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1841782535745337896571025 1381336901809003422428269)
                    ·
                      refine ⟨518001338178376283410601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1381336901809003422428269 518001338178376283410601)
                      ·
                        rfl

theorem cell23_1008804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_1008804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008804 prefixEnd_1008804 := by exact prefixLift 1008804
  have htrace : WordTrace (prefixWord ++ tailWord_1008804) baseStart_1008804 baseEnd_1008804 := by
    simpa [prefixWord, tailWord_1008804, baseEnd_1008804] using wordTrace_append hprefix tailTrace_1008804
  have hstable : (prefixWord ++ tailWord_1008804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008804).length < 2 ^ (prefixWord ++ tailWord_1008804).sum := by decide
  have hdescent : baseEnd_1008804 < baseStart_1008804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008807 : List Nat := [1, 1, 6, 2, 1, 3, 9]
def baseStart_1008807 : Nat := 118140960795 + 1008807 * 2 ^ 59
def prefixEnd_1008807 : Nat := 4983230072969 + 3 ^ 40 * 1008807 * 2
def baseEnd_1008807 : Nat := 6395097266917774958927

theorem tailTrace_1008807 : CollatzResearch.WordTrace tailWord_1008807 prefixEnd_1008807 6395097266917774958927 := by
  unfold tailWord_1008807
  simp only [CollatzResearch.WordTrace]
  refine ⟨36794214056272004363960675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24529476037514669575973783 36794214056272004363960675)
  ·
    refine ⟨55191321084408006545941013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36794214056272004363960675 55191321084408006545941013)
    ·
      refine ⟨2587093175831625306840985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55191321084408006545941013 2587093175831625306840985)
      ·
        refine ⟨1940319881873718980130739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2587093175831625306840985 1940319881873718980130739)
        ·
          refine ⟨2910479822810578470196109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940319881873718980130739 2910479822810578470196109)
          ·
            refine ⟨1091429933553966926323541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2910479822810578470196109 1091429933553966926323541)
            ·
              refine ⟨6395097266917774958927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1091429933553966926323541 6395097266917774958927)
              ·
                rfl

theorem cell23_1008807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 9].length) (baseStart_1008807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008807 prefixEnd_1008807 := by exact prefixLift 1008807
  have htrace : WordTrace (prefixWord ++ tailWord_1008807) baseStart_1008807 baseEnd_1008807 := by
    simpa [prefixWord, tailWord_1008807, baseEnd_1008807] using wordTrace_append hprefix tailTrace_1008807
  have hstable : (prefixWord ++ tailWord_1008807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008807).length < 2 ^ (prefixWord ++ tailWord_1008807).sum := by decide
  have hdescent : baseEnd_1008807 < baseStart_1008807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008897 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 7]
def baseStart_1008897 : Nat := 118140960795 + 1008897 * 2 ^ 59
def prefixEnd_1008897 : Nat := 4983230072969 + 3 ^ 40 * 1008897 * 2
def baseEnd_1008897 : Nat := 57561010208804935505297

theorem tailTrace_1008897 : CollatzResearch.WordTrace tailWord_1008897 prefixEnd_1008897 57561010208804935505297 := by
  unfold tailWord_1008897
  simp only [CollatzResearch.WordTrace]
  refine ⟨36797496625945949734736945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24531664417297299823157963 36797496625945949734736945)
  ·
    refine ⟨27598122469459462301052709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36797496625945949734736945 27598122469459462301052709)
    ·
      refine ⟨5174647963023649181447383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27598122469459462301052709 5174647963023649181447383)
      ·
        refine ⟨7761971944535473772171075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5174647963023649181447383 7761971944535473772171075)
        ·
          refine ⟨11642957916803210658256613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7761971944535473772171075 11642957916803210658256613)
          ·
            refine ⟨2183054609400601998423115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11642957916803210658256613 2183054609400601998423115)
            ·
              refine ⟨3274581914100902997634673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183054609400601998423115 3274581914100902997634673)
              ·
                refine ⟨2455936435575677248226005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274581914100902997634673 2455936435575677248226005)
                ·
                  refine ⟨57561010208804935505297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2455936435575677248226005 57561010208804935505297)
                  ·
                    rfl

theorem cell23_1008897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 7].length) (baseStart_1008897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008897 prefixEnd_1008897 := by exact prefixLift 1008897
  have htrace : WordTrace (prefixWord ++ tailWord_1008897) baseStart_1008897 baseEnd_1008897 := by
    simpa [prefixWord, tailWord_1008897, baseEnd_1008897] using wordTrace_append hprefix tailTrace_1008897
  have hstable : (prefixWord ++ tailWord_1008897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008897).length < 2 ^ (prefixWord ++ tailWord_1008897).sum := by decide
  have hdescent : baseEnd_1008897 < baseStart_1008897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008925 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_1008925 : Nat := 118140960795 + 1008925 * 2 ^ 59
def prefixEnd_1008925 : Nat := 4983230072969 + 3 ^ 40 * 1008925 * 2
def baseEnd_1008925 : Nat := 518063469337570309997545

theorem tailTrace_1008925 : CollatzResearch.WordTrace tailWord_1008925 prefixEnd_1008925 518063469337570309997545 := by
  unfold tailWord_1008925
  simp only [CollatzResearch.WordTrace]
  refine ⟨36798517869844510516756229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24532345246563007011170819 36798517869844510516756229)
  ·
    refine ⟨6899722100595845721891793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36798517869844510516756229 6899722100595845721891793)
    ·
      refine ⟨5174791575446884291418845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6899722100595845721891793 5174791575446884291418845)
      ·
        refine ⟨1940546840792581609282067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5174791575446884291418845 1940546840792581609282067)
        ·
          refine ⟨2910820261188872413923101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940546840792581609282067 2910820261188872413923101)
          ·
            refine ⟨1091557597945827155221163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2910820261188872413923101 1091557597945827155221163)
            ·
              refine ⟨1637336396918740732831745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091557597945827155221163 1637336396918740732831745)
              ·
                refine ⟨1228002297689055549623809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637336396918740732831745 1228002297689055549623809)
                ·
                  refine ⟨921001723266791662217857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1228002297689055549623809 921001723266791662217857)
                  ·
                    refine ⟨690751292450093746663393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921001723266791662217857 690751292450093746663393)
                    ·
                      refine ⟨518063469337570309997545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690751292450093746663393 518063469337570309997545)
                      ·
                        rfl

theorem cell23_1008925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_1008925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008925 prefixEnd_1008925 := by exact prefixLift 1008925
  have htrace : WordTrace (prefixWord ++ tailWord_1008925) baseStart_1008925 baseEnd_1008925 := by
    simpa [prefixWord, tailWord_1008925, baseEnd_1008925] using wordTrace_append hprefix tailTrace_1008925
  have hstable : (prefixWord ++ tailWord_1008925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008925).length < 2 ^ (prefixWord ++ tailWord_1008925).sum := by decide
  have hdescent : baseEnd_1008925 < baseStart_1008925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008941 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1008941 : Nat := 118140960795 + 1008941 * 2 ^ 59
def prefixEnd_1008941 : Nat := 4983230072969 + 3 ^ 40 * 1008941 * 2
def baseEnd_1008941 : Nat := 518071685028042247397471

theorem tailTrace_1008941 : CollatzResearch.WordTrace tailWord_1008941 prefixEnd_1008941 518071685028042247397471 := by
  unfold tailWord_1008941
  simp only [CollatzResearch.WordTrace]
  refine ⟨36799101437786545249338677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24532734291857696832892451 36799101437786545249338677)
  ·
    refine ⟨3449915759792488617125501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36799101437786545249338677 3449915759792488617125501)
    ·
      refine ⟨1293718409922183231422063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3449915759792488617125501 1293718409922183231422063)
      ·
        refine ⟨1940577614883274847133095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293718409922183231422063 1940577614883274847133095)
        ·
          refine ⟨2910866422324912270699643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940577614883274847133095 2910866422324912270699643)
          ·
            refine ⟨4366299633487368406049465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910866422324912270699643 4366299633487368406049465)
            ·
              refine ⟨3274724725115526304537099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366299633487368406049465 3274724725115526304537099)
              ·
                refine ⟨4912087087673289456805649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274724725115526304537099 4912087087673289456805649)
                ·
                  refine ⟨3684065315754967092604237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4912087087673289456805649 3684065315754967092604237)
                  ·
                    refine ⟨1381524493408112659726589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684065315754967092604237 1381524493408112659726589)
                    ·
                      refine ⟨518071685028042247397471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1381524493408112659726589 518071685028042247397471)
                      ·
                        rfl

theorem cell23_1008941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1008941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008941 prefixEnd_1008941 := by exact prefixLift 1008941
  have htrace : WordTrace (prefixWord ++ tailWord_1008941) baseStart_1008941 baseEnd_1008941 := by
    simpa [prefixWord, tailWord_1008941, baseEnd_1008941] using wordTrace_append hprefix tailTrace_1008941
  have hstable : (prefixWord ++ tailWord_1008941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008941).length < 2 ^ (prefixWord ++ tailWord_1008941).sum := by decide
  have hdescent : baseEnd_1008941 < baseStart_1008941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008947 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 4]
def baseStart_1008947 : Nat := 118140960795 + 1008947 * 2 ^ 59
def prefixEnd_1008947 : Nat := 4983230072969 + 3 ^ 40 * 1008947 * 2
def baseEnd_1008947 : Nat := 518074765911969223922443

theorem tailTrace_1008947 : CollatzResearch.WordTrace tailWord_1008947 prefixEnd_1008947 518074765911969223922443 := by
  unfold tailWord_1008947
  simp only [CollatzResearch.WordTrace]
  refine ⟨36799320275764808274057095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24532880183843205516038063 36799320275764808274057095)
  ·
    refine ⟨55198980413647212411085643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36799320275764808274057095 55198980413647212411085643)
    ·
      refine ⟨82798470620470818616628465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55198980413647212411085643 82798470620470818616628465)
      ·
        refine ⟨62098852965353113962471349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82798470620470818616628465 62098852965353113962471349)
        ·
          refine ⟨5821767465501854433981689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62098852965353113962471349 5821767465501854433981689)
          ·
            refine ⟨4366325599126390825486267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821767465501854433981689 4366325599126390825486267)
            ·
              refine ⟨6549488398689586238229401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366325599126390825486267 6549488398689586238229401)
              ·
                refine ⟨4912116299017189678672051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6549488398689586238229401 4912116299017189678672051)
                ·
                  refine ⟨7368174448525784518008077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912116299017189678672051 7368174448525784518008077)
                  ·
                    refine ⟨2763065418197169194253029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7368174448525784518008077 2763065418197169194253029)
                    ·
                      refine ⟨518074765911969223922443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2763065418197169194253029 518074765911969223922443)
                      ·
                        rfl

theorem cell23_1008947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_1008947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008947 prefixEnd_1008947 := by exact prefixLift 1008947
  have htrace : WordTrace (prefixWord ++ tailWord_1008947) baseStart_1008947 baseEnd_1008947 := by
    simpa [prefixWord, tailWord_1008947, baseEnd_1008947] using wordTrace_append hprefix tailTrace_1008947
  have hstable : (prefixWord ++ tailWord_1008947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008947).length < 2 ^ (prefixWord ++ tailWord_1008947).sum := by decide
  have hdescent : baseEnd_1008947 < baseStart_1008947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008982 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1008982 : Nat := 118140960795 + 1008982 * 2 ^ 59
def prefixEnd_1008982 : Nat := 4983230072969 + 3 ^ 40 * 1008982 * 2
def baseEnd_1008982 : Nat := 57565859748319620776087

theorem tailTrace_1008982 : CollatzResearch.WordTrace tailWord_1008982 prefixEnd_1008982 57565859748319620776087 := by
  unfold tailWord_1008982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300037301914875578223825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24533731220425339501054133 2300037301914875578223825)
  ·
    refine ⟨1725027976436156683667869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2300037301914875578223825 1725027976436156683667869)
    ·
      refine ⟨646885491163558756375451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1725027976436156683667869 646885491163558756375451)
      ·
        refine ⟨970328236745338134563177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646885491163558756375451 970328236745338134563177)
        ·
          refine ⟨727746177559003600922383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970328236745338134563177 727746177559003600922383)
          ·
            refine ⟨1091619266338505401383575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727746177559003600922383 1091619266338505401383575)
            ·
              refine ⟨1637428899507758102075363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091619266338505401383575 1637428899507758102075363)
              ·
                refine ⟨2456143349261637153113045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637428899507758102075363 2456143349261637153113045)
                ·
                  refine ⟨57565859748319620776087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2456143349261637153113045 57565859748319620776087)
                  ·
                    rfl

theorem cell23_1008982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1008982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008982 prefixEnd_1008982 := by exact prefixLift 1008982
  have htrace : WordTrace (prefixWord ++ tailWord_1008982) baseStart_1008982 baseEnd_1008982 := by
    simpa [prefixWord, tailWord_1008982, baseEnd_1008982] using wordTrace_append hprefix tailTrace_1008982
  have hstable : (prefixWord ++ tailWord_1008982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008982).length < 2 ^ (prefixWord ++ tailWord_1008982).sum := by decide
  have hdescent : baseEnd_1008982 < baseStart_1008982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008984 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1008984 : Nat := 118140960795 + 1008984 * 2 ^ 59
def prefixEnd_1008984 : Nat := 4983230072969 + 3 ^ 40 * 1008984 * 2
def baseEnd_1008984 : Nat := 518093764696185579159773

theorem tailTrace_1008984 : CollatzResearch.WordTrace tailWord_1008984 prefixEnd_1008984 518093764696185579159773 := by
  unfold tailWord_1008984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400334888315381796577003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24533779851087175728769337 18400334888315381796577003)
  ·
    refine ⟨27600502332473072694865505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18400334888315381796577003 27600502332473072694865505)
    ·
      refine ⟨20700376749354804521149129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27600502332473072694865505 20700376749354804521149129)
      ·
        refine ⟨15525282562016103390861847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20700376749354804521149129 15525282562016103390861847)
        ·
          refine ⟨23287923843024155086292771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15525282562016103390861847 23287923843024155086292771)
          ·
            refine ⟨34931885764536232629439157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23287923843024155086292771 34931885764536232629439157)
            ·
              refine ⟨3274864290425271809009921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34931885764536232629439157 3274864290425271809009921)
              ·
                refine ⟨2456148217818953856757441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274864290425271809009921 2456148217818953856757441)
                ·
                  refine ⟨1842111163364215392568081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2456148217818953856757441 1842111163364215392568081)
                  ·
                    refine ⟨1381583372523161544426061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1842111163364215392568081 1381583372523161544426061)
                    ·
                      refine ⟨518093764696185579159773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1381583372523161544426061 518093764696185579159773)
                      ·
                        rfl

theorem cell23_1008984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1008984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1008984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1008984 prefixEnd_1008984 := by exact prefixLift 1008984
  have htrace : WordTrace (prefixWord ++ tailWord_1008984) baseStart_1008984 baseEnd_1008984 := by
    simpa [prefixWord, tailWord_1008984, baseEnd_1008984] using wordTrace_append hprefix tailTrace_1008984
  have hstable : (prefixWord ++ tailWord_1008984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008984).length < 2 ^ (prefixWord ++ tailWord_1008984).sum := by decide
  have hdescent : baseEnd_1008984 < baseStart_1008984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009004 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 6]
def baseStart_1009004 : Nat := 118140960795 + 1009004 * 2 ^ 59
def prefixEnd_1009004 : Nat := 4983230072969 + 3 ^ 40 * 1009004 * 2
def baseEnd_1009004 : Nat := 57567114923252833434409

theorem tailTrace_1009004 : CollatzResearch.WordTrace tailWord_1009004 prefixEnd_1009004 57567114923252833434409 := by
  unfold tailWord_1009004
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400699618279153504441033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24534266157705538005921377 18400699618279153504441033)
  ·
    refine ⟨13800524713709365128330775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18400699618279153504441033 13800524713709365128330775)
    ·
      refine ⟨20700787070564047692496163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13800524713709365128330775 20700787070564047692496163)
      ·
        refine ⟨31051180605846071538744245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20700787070564047692496163 31051180605846071538744245)
        ·
          refine ⟨2911048181798069206757273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31051180605846071538744245 2911048181798069206757273)
          ·
            refine ⟨2183286136348551905067955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911048181798069206757273 2183286136348551905067955)
            ·
              refine ⟨3274929204522827857601933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183286136348551905067955 3274929204522827857601933)
              ·
                refine ⟨1228098451696060446600725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3274929204522827857601933 1228098451696060446600725)
                ·
                  refine ⟨57567114923252833434409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1228098451696060446600725 57567114923252833434409)
                  ·
                    rfl

theorem cell23_1009004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_1009004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009004 prefixEnd_1009004 := by exact prefixLift 1009004
  have htrace : WordTrace (prefixWord ++ tailWord_1009004) baseStart_1009004 baseEnd_1009004 := by
    simpa [prefixWord, tailWord_1009004, baseEnd_1009004] using wordTrace_append hprefix tailTrace_1009004
  have hstable : (prefixWord ++ tailWord_1009004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009004).length < 2 ^ (prefixWord ++ tailWord_1009004).sum := by decide
  have hdescent : baseEnd_1009004 < baseStart_1009004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009024 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 1, 5, 2]
def baseStart_1009024 : Nat := 118140960795 + 1009024 * 2 ^ 59
def prefixEnd_1009024 : Nat := 4983230072969 + 3 ^ 40 * 1009024 * 2
def baseEnd_1009024 : Nat := 518114303922365422659589

theorem tailTrace_1009024 : CollatzResearch.WordTrace tailWord_1009024 prefixEnd_1009024 518114303922365422659589 := by
  unfold tailWord_1009024
  simp only [CollatzResearch.WordTrace]
  refine ⟨18401064348242925212305063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24534752464323900283073417 18401064348242925212305063)
  ·
    refine ⟨27601596522364387818457595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18401064348242925212305063 27601596522364387818457595)
    ·
      refine ⟨41402394783546581727686393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27601596522364387818457595 41402394783546581727686393)
      ·
        refine ⟨31051796087659936295764795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41402394783546581727686393 31051796087659936295764795)
        ·
          refine ⟨46577694131489904443647193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31051796087659936295764795 46577694131489904443647193)
          ·
            refine ⟨34933270598617428332735395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46577694131489904443647193 34933270598617428332735395)
            ·
              refine ⟨52399905897926142499103093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34933270598617428332735395 52399905897926142499103093)
              ·
                refine ⟨4912491177930575859290915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52399905897926142499103093 4912491177930575859290915)
                ·
                  refine ⟨7368736766895863788936373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912491177930575859290915 7368736766895863788936373)
                  ·
                    refine ⟨690819071896487230212785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7368736766895863788936373 690819071896487230212785)
                    ·
                      refine ⟨518114303922365422659589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690819071896487230212785 518114303922365422659589)
                      ·
                        rfl

theorem cell23_1009024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_1009024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009024 prefixEnd_1009024 := by exact prefixLift 1009024
  have htrace : WordTrace (prefixWord ++ tailWord_1009024) baseStart_1009024 baseEnd_1009024 := by
    simpa [prefixWord, tailWord_1009024, baseEnd_1009024] using wordTrace_append hprefix tailTrace_1009024
  have hstable : (prefixWord ++ tailWord_1009024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009024).length < 2 ^ (prefixWord ++ tailWord_1009024).sum := by decide
  have hdescent : baseEnd_1009024 < baseStart_1009024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009047 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 5, 6]
def baseStart_1009047 : Nat := 118140960795 + 1009047 * 2 ^ 59
def prefixEnd_1009047 : Nat := 4983230072969 + 3 ^ 40 * 1009047 * 2
def baseEnd_1009047 : Nat := 172708704659139610890661

theorem tailTrace_1009047 : CollatzResearch.WordTrace tailWord_1009047 prefixEnd_1009047 172708704659139610890661 := by
  unfold tailWord_1009047
  simp only [CollatzResearch.WordTrace]
  refine ⟨36802967575402525352697395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24535311716935016901798263 36802967575402525352697395)
  ·
    refine ⟨55204451363103788029046093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36802967575402525352697395 55204451363103788029046093)
    ·
      refine ⟨20701669261163920510892285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55204451363103788029046093 20701669261163920510892285)
      ·
        refine ⟨7763125972936470191584607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20701669261163920510892285 7763125972936470191584607)
        ·
          refine ⟨11644688959404705287376911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7763125972936470191584607 11644688959404705287376911)
          ·
            refine ⟨17467033439107057931065367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11644688959404705287376911 17467033439107057931065367)
            ·
              refine ⟨26200550158660586896598051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17467033439107057931065367 26200550158660586896598051)
              ·
                refine ⟨39300825237990880344897077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26200550158660586896598051 39300825237990880344897077)
                ·
                  refine ⟨3684452366061645032334101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39300825237990880344897077 3684452366061645032334101)
                  ·
                    refine ⟨172708704659139610890661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3684452366061645032334101 172708704659139610890661)
                    ·
                      rfl

theorem cell23_1009047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_1009047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009047 prefixEnd_1009047 := by exact prefixLift 1009047
  have htrace : WordTrace (prefixWord ++ tailWord_1009047) baseStart_1009047 baseEnd_1009047 := by
    simpa [prefixWord, tailWord_1009047, baseEnd_1009047] using wordTrace_append hprefix tailTrace_1009047
  have hstable : (prefixWord ++ tailWord_1009047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009047).length < 2 ^ (prefixWord ++ tailWord_1009047).sum := by decide
  have hdescent : baseEnd_1009047 < baseStart_1009047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009097 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_1009097 : Nat := 118140960795 + 1009097 * 2 ^ 59
def prefixEnd_1009097 : Nat := 4983230072969 + 3 ^ 40 * 1009097 * 2
def baseEnd_1009097 : Nat := 518151788010143637046753

theorem tailTrace_1009097 : CollatzResearch.WordTrace tailWord_1009097 prefixEnd_1009097 518151788010143637046753 := by
  unfold tailWord_1009097
  simp only [CollatzResearch.WordTrace]
  refine ⟨36804791225221383892017545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24536527483480922594678363 36804791225221383892017545)
  ·
    refine ⟨27603593418916037919013159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36804791225221383892017545 27603593418916037919013159)
    ·
      refine ⟨41405390128374056878519739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27603593418916037919013159 41405390128374056878519739)
      ·
        refine ⟨62108085192561085317779609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41405390128374056878519739 62108085192561085317779609)
        ·
          refine ⟨46581063894420813988334707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62108085192561085317779609 46581063894420813988334707)
          ·
            refine ⟨69871595841631220982502061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46581063894420813988334707 69871595841631220982502061)
            ·
              refine ⟨26201848440611707868438273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69871595841631220982502061 26201848440611707868438273)
              ·
                refine ⟨19651386330458780901328705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26201848440611707868438273 19651386330458780901328705)
                ·
                  refine ⟨14738539747844085675996529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19651386330458780901328705 14738539747844085675996529)
                  ·
                    refine ⟨11053904810883064256997397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14738539747844085675996529 11053904810883064256997397)
                    ·
                      refine ⟨518151788010143637046753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11053904810883064256997397 518151788010143637046753)
                      ·
                        rfl

theorem cell23_1009097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_1009097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009097 prefixEnd_1009097 := by exact prefixLift 1009097
  have htrace : WordTrace (prefixWord ++ tailWord_1009097) baseStart_1009097 baseEnd_1009097 := by
    simpa [prefixWord, tailWord_1009097, baseEnd_1009097] using wordTrace_append hprefix tailTrace_1009097
  have hstable : (prefixWord ++ tailWord_1009097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009097).length < 2 ^ (prefixWord ++ tailWord_1009097).sum := by decide
  have hdescent : baseEnd_1009097 < baseStart_1009097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009098 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_1009098 : Nat := 118140960795 + 1009098 * 2 ^ 59
def prefixEnd_1009098 : Nat := 4983230072969 + 3 ^ 40 * 1009098 * 2
def baseEnd_1009098 : Nat := 172717433830266044378083

theorem tailTrace_1009098 : CollatzResearch.WordTrace tailWord_1009098 prefixEnd_1009098 172717433830266044378083 := by
  unfold tailWord_1009098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9201206924554440265700987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24536551798811840708535965 9201206924554440265700987)
  ·
    refine ⟨13801810386831660398551481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9201206924554440265700987 13801810386831660398551481)
    ·
      refine ⟨10351357790123745298913611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13801810386831660398551481 10351357790123745298913611)
      ·
        refine ⟨15527036685185617948370417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351357790123745298913611 15527036685185617948370417)
        ·
          refine ⟨11645277513889213461277813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15527036685185617948370417 11645277513889213461277813)
          ·
            refine ⟨1091744766927113761994795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11645277513889213461277813 1091744766927113761994795)
            ·
              refine ⟨1637617150390670642992193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091744766927113761994795 1637617150390670642992193)
              ·
                refine ⟨1228212862793002982244145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637617150390670642992193 1228212862793002982244145)
                ·
                  refine ⟨921159647094752236683109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1228212862793002982244145 921159647094752236683109)
                  ·
                    refine ⟨172717433830266044378083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 921159647094752236683109 172717433830266044378083)
                    ·
                      rfl

theorem cell23_1009098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_1009098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009098 prefixEnd_1009098 := by exact prefixLift 1009098
  have htrace : WordTrace (prefixWord ++ tailWord_1009098) baseStart_1009098 baseEnd_1009098 := by
    simpa [prefixWord, tailWord_1009098, baseEnd_1009098] using wordTrace_append hprefix tailTrace_1009098
  have hstable : (prefixWord ++ tailWord_1009098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009098).length < 2 ^ (prefixWord ++ tailWord_1009098).sum := by decide
  have hdescent : baseEnd_1009098 < baseStart_1009098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009121 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_1009121 : Nat := 118140960795 + 1009121 * 2 ^ 59
def prefixEnd_1009121 : Nat := 4983230072969 + 3 ^ 40 * 1009121 * 2
def baseEnd_1009121 : Nat := 518164111545851543146643

theorem tailTrace_1009121 : CollatzResearch.WordTrace tailWord_1009121 prefixEnd_1009121 518164111545851543146643 := by
  unfold tailWord_1009121
  simp only [CollatzResearch.WordTrace]
  refine ⟨36805666577134435990891217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24537111051422957327260811 36805666577134435990891217)
  ·
    refine ⟨27604249932850826993168413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36805666577134435990891217 27604249932850826993168413)
    ·
      refine ⟨10351593724819060122438155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27604249932850826993168413 10351593724819060122438155)
      ·
        refine ⟨15527390587228590183657233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351593724819060122438155 15527390587228590183657233)
        ·
          refine ⟨11645542940421442637742925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15527390587228590183657233 11645542940421442637742925)
          ·
            refine ⟨4367078602658040989153597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11645542940421442637742925 4367078602658040989153597)
            ·
              refine ⟨1637654475996765370932599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4367078602658040989153597 1637654475996765370932599)
              ·
                refine ⟨2456481713995148056398899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637654475996765370932599 2456481713995148056398899)
                ·
                  refine ⟨3684722570992722084598349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456481713995148056398899 3684722570992722084598349)
                  ·
                    refine ⟨1381770964122270781724381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684722570992722084598349 1381770964122270781724381)
                    ·
                      refine ⟨518164111545851543146643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1381770964122270781724381 518164111545851543146643)
                      ·
                        rfl

theorem cell23_1009121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_1009121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009121 prefixEnd_1009121 := by exact prefixLift 1009121
  have htrace : WordTrace (prefixWord ++ tailWord_1009121) baseStart_1009121 baseEnd_1009121 := by
    simpa [prefixWord, tailWord_1009121, baseEnd_1009121] using wordTrace_append hprefix tailTrace_1009121
  have hstable : (prefixWord ++ tailWord_1009121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009121).length < 2 ^ (prefixWord ++ tailWord_1009121).sum := by decide
  have hdescent : baseEnd_1009121 < baseStart_1009121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009134 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1009134 : Nat := 118140960795 + 1009134 * 2 ^ 59
def prefixEnd_1009134 : Nat := 4983230072969 + 3 ^ 40 * 1009134 * 2
def baseEnd_1009134 : Nat := 518170786794359992284083

theorem tailTrace_1009134 : CollatzResearch.WordTrace tailWord_1009134 prefixEnd_1009134 518170786794359992284083 := by
  unfold tailWord_1009134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4600767590760917401389307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24537427150724892807409637 4600767590760917401389307)
  ·
    refine ⟨6901151386141376102083961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4600767590760917401389307 6901151386141376102083961)
    ·
      refine ⟨5175863539606032076562971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6901151386141376102083961 5175863539606032076562971)
      ·
        refine ⟨7763795309409048114844457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5175863539606032076562971 7763795309409048114844457)
        ·
          refine ⟨5822846482056786086133343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7763795309409048114844457 5822846482056786086133343)
          ·
            refine ⟨8734269723085179129200015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822846482056786086133343 8734269723085179129200015)
            ·
              refine ⟨13101404584627768693800023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8734269723085179129200015 13101404584627768693800023)
              ·
                refine ⟨19652106876941653040700035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13101404584627768693800023 19652106876941653040700035)
                ·
                  refine ⟨29478160315412479561050053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19652106876941653040700035 29478160315412479561050053)
                  ·
                    refine ⟨5527155059139839917696885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29478160315412479561050053 5527155059139839917696885)
                    ·
                      refine ⟨518170786794359992284083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5527155059139839917696885 518170786794359992284083)
                      ·
                        rfl

theorem cell23_1009134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1009134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009134 prefixEnd_1009134 := by exact prefixLift 1009134
  have htrace : WordTrace (prefixWord ++ tailWord_1009134) baseStart_1009134 baseEnd_1009134 := by
    simpa [prefixWord, tailWord_1009134, baseEnd_1009134] using wordTrace_append hprefix tailTrace_1009134
  have hstable : (prefixWord ++ tailWord_1009134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009134).length < 2 ^ (prefixWord ++ tailWord_1009134).sum := by decide
  have hdescent : baseEnd_1009134 < baseStart_1009134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009138 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1009138 : Nat := 118140960795 + 1009138 * 2 ^ 59
def prefixEnd_1009138 : Nat := 4983230072969 + 3 ^ 40 * 1009138 * 2
def baseEnd_1009138 : Nat := 518172840716977976634065

theorem tailTrace_1009138 : CollatzResearch.WordTrace tailWord_1009138 prefixEnd_1009138 518172840716977976634065 := by
  unfold tailWord_1009138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9201571654518211973565017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24537524412048565262840045 9201571654518211973565017)
  ·
    refine ⟨6901178740888658980173763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9201571654518211973565017 6901178740888658980173763)
    ·
      refine ⟨10351768111332988470260645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6901178740888658980173763 10351768111332988470260645)
      ·
        refine ⟨1940956520874935338173871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10351768111332988470260645 1940956520874935338173871)
        ·
          refine ⟨2911434781312403007260807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940956520874935338173871 2911434781312403007260807)
          ·
            refine ⟨4367152171968604510891211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911434781312403007260807 4367152171968604510891211)
            ·
              refine ⟨6550728257952906766336817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367152171968604510891211 6550728257952906766336817)
              ·
                refine ⟨4913046193464680074752613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6550728257952906766336817 4913046193464680074752613)
                ·
                  refine ⟨921196161274627514016115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4913046193464680074752613 921196161274627514016115)
                  ·
                    refine ⟨1381794241911941271024173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 921196161274627514016115 1381794241911941271024173)
                    ·
                      refine ⟨518172840716977976634065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1381794241911941271024173 518172840716977976634065)
                      ·
                        rfl

theorem cell23_1009138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1009138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009138 prefixEnd_1009138 := by exact prefixLift 1009138
  have htrace : WordTrace (prefixWord ++ tailWord_1009138) baseStart_1009138 baseEnd_1009138 := by
    simpa [prefixWord, tailWord_1009138, baseEnd_1009138] using wordTrace_append hprefix tailTrace_1009138
  have hstable : (prefixWord ++ tailWord_1009138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009138).length < 2 ^ (prefixWord ++ tailWord_1009138).sum := by decide
  have hdescent : baseEnd_1009138 < baseStart_1009138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009148 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_1009148 : Nat := 118140960795 + 1009148 * 2 ^ 59
def prefixEnd_1009148 : Nat := 4983230072969 + 3 ^ 40 * 1009148 * 2
def baseEnd_1009148 : Nat := 518177975523522937509019

theorem tailTrace_1009148 : CollatzResearch.WordTrace tailWord_1009148 prefixEnd_1009148 518177975523522937509019 := by
  unfold tailWord_1009148
  simp only [CollatzResearch.WordTrace]
  refine ⟨18403325674018309801062049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24537767565357746401416065 18403325674018309801062049)
  ·
    refine ⟨13802494255513732350796537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18403325674018309801062049 13802494255513732350796537)
    ·
      refine ⟨10351870691635299263097403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13802494255513732350796537 10351870691635299263097403)
      ·
        refine ⟨15527806037452948894646105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351870691635299263097403 15527806037452948894646105)
        ·
          refine ⟨11645854528089711670984579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15527806037452948894646105 11645854528089711670984579)
          ·
            refine ⟨17468781792134567506476869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11645854528089711670984579 17468781792134567506476869)
            ·
              refine ⟨3275396586025231407464413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17468781792134567506476869 3275396586025231407464413)
              ·
                refine ⟨1228273719759461777799155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3275396586025231407464413 1228273719759461777799155)
                ·
                  refine ⟨1842410579639192666698733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228273719759461777799155 1842410579639192666698733)
                  ·
                    refine ⟨690903967364697250012025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842410579639192666698733 690903967364697250012025)
                    ·
                      refine ⟨518177975523522937509019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690903967364697250012025 518177975523522937509019)
                      ·
                        rfl

theorem cell23_1009148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_1009148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009148 prefixEnd_1009148 := by exact prefixLift 1009148
  have htrace : WordTrace (prefixWord ++ tailWord_1009148) baseStart_1009148 baseEnd_1009148 := by
    simpa [prefixWord, tailWord_1009148, baseEnd_1009148] using wordTrace_append hprefix tailTrace_1009148
  have hstable : (prefixWord ++ tailWord_1009148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009148).length < 2 ^ (prefixWord ++ tailWord_1009148).sum := by decide
  have hdescent : baseEnd_1009148 < baseStart_1009148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009172 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1009172 : Nat := 118140960795 + 1009172 * 2 ^ 59
def prefixEnd_1009172 : Nat := 4983230072969 + 3 ^ 40 * 1009172 * 2
def baseEnd_1009172 : Nat := 518190299059230843608909

theorem tailTrace_1009172 : CollatzResearch.WordTrace tailWord_1009172 prefixEnd_1009172 518190299059230843608909 := by
  unfold tailWord_1009172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18403763349974835850498885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24538351133299781133998513 18403763349974835850498885)
  ·
    refine ⟨3450705628120281721968541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18403763349974835850498885 3450705628120281721968541)
    ·
      refine ⟨1294014610545105645738203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3450705628120281721968541 1294014610545105645738203)
      ·
        refine ⟨1941021915817658468607305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294014610545105645738203 1941021915817658468607305)
        ·
          refine ⟨1455766436863243851455479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1941021915817658468607305 1455766436863243851455479)
          ·
            refine ⟨2183649655294865777183219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455766436863243851455479 2183649655294865777183219)
            ·
              refine ⟨3275474482942298665774829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183649655294865777183219 3275474482942298665774829)
              ·
                refine ⟨1228302931103361999665561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3275474482942298665774829 1228302931103361999665561)
                ·
                  refine ⟨921227198327521499749171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1228302931103361999665561 921227198327521499749171)
                  ·
                    refine ⟨1381840797491282249623757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 921227198327521499749171 1381840797491282249623757)
                    ·
                      refine ⟨518190299059230843608909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1381840797491282249623757 518190299059230843608909)
                      ·
                        rfl

theorem cell23_1009172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1009172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009172 prefixEnd_1009172 := by exact prefixLift 1009172
  have htrace : WordTrace (prefixWord ++ tailWord_1009172) baseStart_1009172 baseEnd_1009172 := by
    simpa [prefixWord, tailWord_1009172, baseEnd_1009172] using wordTrace_append hprefix tailTrace_1009172
  have hstable : (prefixWord ++ tailWord_1009172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009172).length < 2 ^ (prefixWord ++ tailWord_1009172).sum := by decide
  have hdescent : baseEnd_1009172 < baseStart_1009172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009201 : List Nat := [1, 2, 2, 3, 1, 1, 1, 7, 5]
def baseStart_1009201 : Nat := 118140960795 + 1009201 * 2 ^ 59
def prefixEnd_1009201 : Nat := 4983230072969 + 3 ^ 40 * 1009201 * 2
def baseEnd_1009201 : Nat := 57578354444245692238475

theorem tailTrace_1009201 : CollatzResearch.WordTrace tailWord_1009201 prefixEnd_1009201 57578354444245692238475 := by
  unfold tailWord_1009201
  simp only [CollatzResearch.WordTrace]
  refine ⟨36808584416844609653803457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24539056277896406435868971 36808584416844609653803457)
  ·
    refine ⟨27606438312633457240352593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36808584416844609653803457 27606438312633457240352593)
    ·
      refine ⟨20704828734475092930264445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27606438312633457240352593 20704828734475092930264445)
      ·
        refine ⟨7764310775428159848849167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20704828734475092930264445 7764310775428159848849167)
        ·
          refine ⟨11646466163142239773273751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7764310775428159848849167 11646466163142239773273751)
          ·
            refine ⟨17469699244713359659910627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11646466163142239773273751 17469699244713359659910627)
            ·
              refine ⟨26204548867070039489865941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17469699244713359659910627 26204548867070039489865941)
              ·
                refine ⟨614169114071954050543733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26204548867070039489865941 614169114071954050543733)
                ·
                  refine ⟨57578354444245692238475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 614169114071954050543733 57578354444245692238475)
                  ·
                    rfl

theorem cell23_1009201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 5].length) (baseStart_1009201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009201 prefixEnd_1009201 := by exact prefixLift 1009201
  have htrace : WordTrace (prefixWord ++ tailWord_1009201) baseStart_1009201 baseEnd_1009201 := by
    simpa [prefixWord, tailWord_1009201, baseEnd_1009201] using wordTrace_append hprefix tailTrace_1009201
  have hstable : (prefixWord ++ tailWord_1009201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009201).length < 2 ^ (prefixWord ++ tailWord_1009201).sum := by decide
  have hdescent : baseEnd_1009201 < baseStart_1009201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009212 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_1009212 : Nat := 118140960795 + 1009212 * 2 ^ 59
def prefixEnd_1009212 : Nat := 4983230072969 + 3 ^ 40 * 1009212 * 2
def baseEnd_1009212 : Nat := 518210838285410687108725

theorem tailTrace_1009212 : CollatzResearch.WordTrace tailWord_1009212 prefixEnd_1009212 518210838285410687108725 := by
  unfold tailWord_1009212
  simp only [CollatzResearch.WordTrace]
  refine ⟨18404492809902379266226945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24539323746536505688302593 18404492809902379266226945)
  ·
    refine ⟨13803369607426784449670209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18404492809902379266226945 13803369607426784449670209)
    ·
      refine ⟨10352527205570088337252657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13803369607426784449670209 10352527205570088337252657)
      ·
        refine ⟨7764395404177566252939493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10352527205570088337252657 7764395404177566252939493)
        ·
          refine ⟨1455824138283293672426155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7764395404177566252939493 1455824138283293672426155)
          ·
            refine ⟨2183736207424940508639233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455824138283293672426155 2183736207424940508639233)
            ·
              refine ⟨1637802155568705381479425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183736207424940508639233 1637802155568705381479425)
              ·
                refine ⟨1228351616676529036109569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637802155568705381479425 1228351616676529036109569)
                ·
                  refine ⟨921263712507396777082177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1228351616676529036109569 921263712507396777082177)
                  ·
                    refine ⟨690947784380547582811633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921263712507396777082177 690947784380547582811633)
                    ·
                      refine ⟨518210838285410687108725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690947784380547582811633 518210838285410687108725)
                      ·
                        rfl

theorem cell23_1009212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_1009212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009212 prefixEnd_1009212 := by exact prefixLift 1009212
  have htrace : WordTrace (prefixWord ++ tailWord_1009212) baseStart_1009212 baseEnd_1009212 := by
    simpa [prefixWord, tailWord_1009212, baseEnd_1009212] using wordTrace_append hprefix tailTrace_1009212
  have hstable : (prefixWord ++ tailWord_1009212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009212).length < 2 ^ (prefixWord ++ tailWord_1009212).sum := by decide
  have hdescent : baseEnd_1009212 < baseStart_1009212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009221 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 1, 7, 2]
def baseStart_1009221 : Nat := 118140960795 + 1009221 * 2 ^ 59
def prefixEnd_1009221 : Nat := 4983230072969 + 3 ^ 40 * 1009221 * 2
def baseEnd_1009221 : Nat := 518215459611301151896183

theorem tailTrace_1009221 : CollatzResearch.WordTrace tailWord_1009221 prefixEnd_1009221 518215459611301151896183 := by
  unfold tailWord_1009221
  simp only [CollatzResearch.WordTrace]
  refine ⟨36809313876772153069531517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24539542584514768713021011 36809313876772153069531517)
  ·
    refine ⟨13803492703789557401074319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36809313876772153069531517 13803492703789557401074319)
    ·
      refine ⟨20705239055684336101611479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13803492703789557401074319 20705239055684336101611479)
      ·
        refine ⟨31057858583526504152417219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20705239055684336101611479 31057858583526504152417219)
        ·
          refine ⟨46586787875289756228625829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31057858583526504152417219 46586787875289756228625829)
          ·
            refine ⟨8735022726616829292867343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46586787875289756228625829 8735022726616829292867343)
            ·
              refine ⟨13102534089925243939301015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8735022726616829292867343 13102534089925243939301015)
              ·
                refine ⟨19653801134887865908951523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13102534089925243939301015 19653801134887865908951523)
                ·
                  refine ⟨29480701702331798863427285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19653801134887865908951523 29480701702331798863427285)
                  ·
                    refine ⟨690953946148401535861577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29480701702331798863427285 690953946148401535861577)
                    ·
                      refine ⟨518215459611301151896183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 690953946148401535861577 518215459611301151896183)
                      ·
                        rfl

theorem cell23_1009221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_1009221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009221 prefixEnd_1009221 := by exact prefixLift 1009221
  have htrace : WordTrace (prefixWord ++ tailWord_1009221) baseStart_1009221 baseEnd_1009221 := by
    simpa [prefixWord, tailWord_1009221, baseEnd_1009221] using wordTrace_append hprefix tailTrace_1009221
  have hstable : (prefixWord ++ tailWord_1009221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009221).length < 2 ^ (prefixWord ++ tailWord_1009221).sum := by decide
  have hdescent : baseEnd_1009221 < baseStart_1009221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009251 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1009251 : Nat := 118140960795 + 1009251 * 2 ^ 59
def prefixEnd_1009251 : Nat := 4983230072969 + 3 ^ 40 * 1009251 * 2
def baseEnd_1009251 : Nat := 518230864030936034521045

theorem tailTrace_1009251 : CollatzResearch.WordTrace tailWord_1009251 prefixEnd_1009251 518230864030936034521045 := by
  unfold tailWord_1009251
  simp only [CollatzResearch.WordTrace]
  refine ⟨36810408066663468193123607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24540272044442312128749071 36810408066663468193123607)
  ·
    refine ⟨55215612099995202289685411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36810408066663468193123607 55215612099995202289685411)
    ·
      refine ⟨82823418149992803434528117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55215612099995202289685411 82823418149992803434528117)
      ·
        refine ⟨7764695451561825321987011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82823418149992803434528117 7764695451561825321987011)
        ·
          refine ⟨11647043177342737982980517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7764695451561825321987011 11647043177342737982980517)
          ·
            refine ⟨2183820595751763371808847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11647043177342737982980517 2183820595751763371808847)
            ·
              refine ⟨3275730893627645057713271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183820595751763371808847 3275730893627645057713271)
              ·
                refine ⟨4913596340441467586569907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275730893627645057713271 4913596340441467586569907)
                ·
                  refine ⟨7370394510662201379854861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913596340441467586569907 7370394510662201379854861)
                  ·
                    refine ⟨2763897941498325517445573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7370394510662201379854861 2763897941498325517445573)
                    ·
                      refine ⟨518230864030936034521045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2763897941498325517445573 518230864030936034521045)
                      ·
                        rfl

theorem cell23_1009251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1009251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009251 prefixEnd_1009251 := by exact prefixLift 1009251
  have htrace : WordTrace (prefixWord ++ tailWord_1009251) baseStart_1009251 baseEnd_1009251 := by
    simpa [prefixWord, tailWord_1009251, baseEnd_1009251] using wordTrace_append hprefix tailTrace_1009251
  have hstable : (prefixWord ++ tailWord_1009251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009251).length < 2 ^ (prefixWord ++ tailWord_1009251).sum := by decide
  have hdescent : baseEnd_1009251 < baseStart_1009251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009271 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_1009271 : Nat := 118140960795 + 1009271 * 2 ^ 59
def prefixEnd_1009271 : Nat := 4983230072969 + 3 ^ 40 * 1009271 * 2
def baseEnd_1009271 : Nat := 518241133644025956270953

theorem tailTrace_1009271 : CollatzResearch.WordTrace tailWord_1009271 prefixEnd_1009271 518241133644025956270953 := by
  unfold tailWord_1009271
  simp only [CollatzResearch.WordTrace]
  refine ⟨36811137526591011608851667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24540758351060674405901111 36811137526591011608851667)
  ·
    refine ⟨55216706289886517413277501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36811137526591011608851667 55216706289886517413277501)
    ·
      refine ⟨20706264858707444029979063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55216706289886517413277501 20706264858707444029979063)
      ·
        refine ⟨31059397288061166044968595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20706264858707444029979063 31059397288061166044968595)
        ·
          refine ⟨46589095932091749067452893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31059397288061166044968595 46589095932091749067452893)
          ·
            refine ⟨17470910974534405900294835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46589095932091749067452893 17470910974534405900294835)
            ·
              refine ⟨26206366461801608850442253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17470910974534405900294835 26206366461801608850442253)
              ·
                refine ⟨9827387423175603318915845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26206366461801608850442253 9827387423175603318915845)
                ·
                  refine ⟨1842635141845425622296721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9827387423175603318915845 1842635141845425622296721)
                  ·
                    refine ⟨1381976356384069216722541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1842635141845425622296721 1381976356384069216722541)
                    ·
                      refine ⟨518241133644025956270953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1381976356384069216722541 518241133644025956270953)
                      ·
                        rfl

theorem cell23_1009271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_1009271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009271 prefixEnd_1009271 := by exact prefixLift 1009271
  have htrace : WordTrace (prefixWord ++ tailWord_1009271) baseStart_1009271 baseEnd_1009271 := by
    simpa [prefixWord, tailWord_1009271, baseEnd_1009271] using wordTrace_append hprefix tailTrace_1009271
  have hstable : (prefixWord ++ tailWord_1009271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009271).length < 2 ^ (prefixWord ++ tailWord_1009271).sum := by decide
  have hdescent : baseEnd_1009271 < baseStart_1009271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009312 : List Nat := [2, 1, 1, 4, 3, 3, 1, 3, 1, 4]
def baseStart_1009312 : Nat := 118140960795 + 1009312 * 2 ^ 59
def prefixEnd_1009312 : Nat := 4983230072969 + 3 ^ 40 * 1009312 * 2
def baseEnd_1009312 : Nat := 172754062116953431952755

theorem tailTrace_1009312 : CollatzResearch.WordTrace tailWord_1009312 prefixEnd_1009312 172754062116953431952755 := by
  unfold tailWord_1009312
  simp only [CollatzResearch.WordTrace]
  refine ⟨18406316459721237805547095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24541755279628317074062793 18406316459721237805547095)
  ·
    refine ⟨27609474689581856708320643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18406316459721237805547095 27609474689581856708320643)
    ·
      refine ⟨41414212034372785062480965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27609474689581856708320643 41414212034372785062480965)
      ·
        refine ⟨7765164756444897199215181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41414212034372785062480965 7765164756444897199215181)
        ·
          refine ⟨2911936783666836449705693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7765164756444897199215181 2911936783666836449705693)
          ·
            refine ⟨1091976293875063668639635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2911936783666836449705693 1091976293875063668639635)
            ·
              refine ⟨1637964440812595502959453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091976293875063668639635 1637964440812595502959453)
              ·
                refine ⟨614236665304723313609795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1637964440812595502959453 614236665304723313609795)
                ·
                  refine ⟨921354997957084970414693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614236665304723313609795 921354997957084970414693)
                  ·
                    refine ⟨172754062116953431952755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 921354997957084970414693 172754062116953431952755)
                    ·
                      rfl

theorem cell23_1009312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 4].length) (baseStart_1009312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009312 prefixEnd_1009312 := by exact prefixLift 1009312
  have htrace : WordTrace (prefixWord ++ tailWord_1009312) baseStart_1009312 baseEnd_1009312 := by
    simpa [prefixWord, tailWord_1009312, baseEnd_1009312] using wordTrace_append hprefix tailTrace_1009312
  have hstable : (prefixWord ++ tailWord_1009312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009312).length < 2 ^ (prefixWord ++ tailWord_1009312).sum := by decide
  have hdescent : baseEnd_1009312 < baseStart_1009312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009328 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 4, 3, 2]
def baseStart_1009328 : Nat := 118140960795 + 1009328 * 2 ^ 59
def prefixEnd_1009328 : Nat := 4983230072969 + 3 ^ 40 * 1009328 * 2
def baseEnd_1009328 : Nat := 518270402041332233258191

theorem tailTrace_1009328 : CollatzResearch.WordTrace tailWord_1009328 prefixEnd_1009328 518270402041332233258191 := by
  unfold tailWord_1009328
  simp only [CollatzResearch.WordTrace]
  refine ⟨18406608243692255171838319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24542144324923006895784425 18406608243692255171838319)
  ·
    refine ⟨27609912365538382757757479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18406608243692255171838319 27609912365538382757757479)
    ·
      refine ⟨41414868548307574136636219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27609912365538382757757479 41414868548307574136636219)
      ·
        refine ⟨62122302822461361204954329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41414868548307574136636219 62122302822461361204954329)
        ·
          refine ⟨46591727116846020903715747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62122302822461361204954329 46591727116846020903715747)
          ·
            refine ⟨69887590675269031355573621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46591727116846020903715747 69887590675269031355573621)
            ·
              refine ⟨6551961625806471689585027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69887590675269031355573621 6551961625806471689585027)
              ·
                refine ⟨9827942438709707534377541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551961625806471689585027 9827942438709707534377541)
                ·
                  refine ⟨1842739207258070162695789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9827942438709707534377541 1842739207258070162695789)
                  ·
                    refine ⟨691027202721776311010921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842739207258070162695789 691027202721776311010921)
                    ·
                      refine ⟨518270402041332233258191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691027202721776311010921 518270402041332233258191)
                      ·
                        rfl

theorem cell23_1009328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 4, 3, 2].length) (baseStart_1009328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009328 prefixEnd_1009328 := by exact prefixLift 1009328
  have htrace : WordTrace (prefixWord ++ tailWord_1009328) baseStart_1009328 baseEnd_1009328 := by
    simpa [prefixWord, tailWord_1009328, baseEnd_1009328] using wordTrace_append hprefix tailTrace_1009328
  have hstable : (prefixWord ++ tailWord_1009328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009328).length < 2 ^ (prefixWord ++ tailWord_1009328).sum := by decide
  have hdescent : baseEnd_1009328 < baseStart_1009328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009335 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_1009335 : Nat := 118140960795 + 1009335 * 2 ^ 59
def prefixEnd_1009335 : Nat := 4983230072969 + 3 ^ 40 * 1009335 * 2
def baseEnd_1009335 : Nat := 518273996405913705870659

theorem tailTrace_1009335 : CollatzResearch.WordTrace tailWord_1009335 prefixEnd_1009335 518273996405913705870659 := by
  unfold tailWord_1009335
  simp only [CollatzResearch.WordTrace]
  refine ⟨36813471798359150539181459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24542314532239433692787639 36813471798359150539181459)
  ·
    refine ⟨55220207697538725808772189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36813471798359150539181459 55220207697538725808772189)
    ·
      refine ⟨20707577886577022178289571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55220207697538725808772189 20707577886577022178289571)
      ·
        refine ⟨31061366829865533267434357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20707577886577022178289571 31061366829865533267434357)
        ·
          refine ⟨2912003140299893743821971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31061366829865533267434357 2912003140299893743821971)
          ·
            refine ⟨4368004710449840615732957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912003140299893743821971 4368004710449840615732957)
            ·
              refine ⟨1638001766418690230899859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4368004710449840615732957 1638001766418690230899859)
              ·
                refine ⟨2457002649628035346349789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638001766418690230899859 2457002649628035346349789)
                ·
                  refine ⟨921375993610513254881171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2457002649628035346349789 921375993610513254881171)
                  ·
                    refine ⟨1382063990415769882321757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 921375993610513254881171 1382063990415769882321757)
                    ·
                      refine ⟨518273996405913705870659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1382063990415769882321757 518273996405913705870659)
                      ·
                        rfl

theorem cell23_1009335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_1009335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009335 prefixEnd_1009335 := by exact prefixLift 1009335
  have htrace : WordTrace (prefixWord ++ tailWord_1009335) baseStart_1009335 baseEnd_1009335 := by
    simpa [prefixWord, tailWord_1009335, baseEnd_1009335] using wordTrace_append hprefix tailTrace_1009335
  have hstable : (prefixWord ++ tailWord_1009335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009335).length < 2 ^ (prefixWord ++ tailWord_1009335).sum := by decide
  have hdescent : baseEnd_1009335 < baseStart_1009335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009351 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 1, 6]
def baseStart_1009351 : Nat := 118140960795 + 1009351 * 2 ^ 59
def prefixEnd_1009351 : Nat := 4983230072969 + 3 ^ 40 * 1009351 * 2
def baseEnd_1009351 : Nat := 172760737365461881090195

theorem tailTrace_1009351 : CollatzResearch.WordTrace tailWord_1009351 prefixEnd_1009351 172760737365461881090195 := by
  unfold tailWord_1009351
  simp only [CollatzResearch.WordTrace]
  refine ⟨36814055366301185271763907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24542703577534123514509271 36814055366301185271763907)
  ·
    refine ⟨55221083049451777907645861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36814055366301185271763907 55221083049451777907645861)
    ·
      refine ⟨10353953071772208357683599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55221083049451777907645861 10353953071772208357683599)
      ·
        refine ⟨15530929607658312536525399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10353953071772208357683599 15530929607658312536525399)
        ·
          refine ⟨23296394411487468804788099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15530929607658312536525399 23296394411487468804788099)
          ·
            refine ⟨34944591617231203207182149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23296394411487468804788099 34944591617231203207182149)
            ·
              refine ⟨6552110928230850601346653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34944591617231203207182149 6552110928230850601346653)
              ·
                refine ⟨2457041598086568975504995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6552110928230850601346653 2457041598086568975504995)
                ·
                  refine ⟨3685562397129853463257493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457041598086568975504995 3685562397129853463257493)
                  ·
                    refine ⟨172760737365461881090195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3685562397129853463257493 172760737365461881090195)
                    ·
                      rfl

theorem cell23_1009351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_1009351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009351 prefixEnd_1009351 := by exact prefixLift 1009351
  have htrace : WordTrace (prefixWord ++ tailWord_1009351) baseStart_1009351 baseEnd_1009351 := by
    simpa [prefixWord, tailWord_1009351, baseEnd_1009351] using wordTrace_append hprefix tailTrace_1009351
  have hstable : (prefixWord ++ tailWord_1009351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009351).length < 2 ^ (prefixWord ++ tailWord_1009351).sum := by decide
  have hdescent : baseEnd_1009351 < baseStart_1009351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009358 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_1009358 : Nat := 118140960795 + 1009358 * 2 ^ 59
def prefixEnd_1009358 : Nat := 4983230072969 + 3 ^ 40 * 1009358 * 2
def baseEnd_1009358 : Nat := 518285806460967115883053

theorem tailTrace_1009358 : CollatzResearch.WordTrace tailWord_1009358 prefixEnd_1009358 518285806460967115883053 := by
  unfold tailWord_1009358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4601788834659478183408591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24542873784850550311512485 4601788834659478183408591)
  ·
    refine ⟨6902683251989217275112887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4601788834659478183408591 6902683251989217275112887)
    ·
      refine ⟨10354024877983825912669331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6902683251989217275112887 10354024877983825912669331)
      ·
        refine ⟨15531037316975738869003997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10354024877983825912669331 15531037316975738869003997)
        ·
          refine ⟨5824138993865902075876499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15531037316975738869003997 5824138993865902075876499)
          ·
            refine ⟨8736208490798853113814749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824138993865902075876499 8736208490798853113814749)
            ·
              refine ⟨3276078184049569917680531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8736208490798853113814749 3276078184049569917680531)
              ·
                refine ⟨4914117276074354876520797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276078184049569917680531 4914117276074354876520797)
                ·
                  refine ⟨1842793978527883078695299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4914117276074354876520797 1842793978527883078695299)
                  ·
                    refine ⟨2764190967791824618042949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1842793978527883078695299 2764190967791824618042949)
                    ·
                      refine ⟨518285806460967115883053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2764190967791824618042949 518285806460967115883053)
                      ·
                        rfl

theorem cell23_1009358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_1009358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009358 prefixEnd_1009358 := by exact prefixLift 1009358
  have htrace : WordTrace (prefixWord ++ tailWord_1009358) baseStart_1009358 baseEnd_1009358 := by
    simpa [prefixWord, tailWord_1009358, baseEnd_1009358] using wordTrace_append hprefix tailTrace_1009358
  have hstable : (prefixWord ++ tailWord_1009358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009358).length < 2 ^ (prefixWord ++ tailWord_1009358).sum := by decide
  have hdescent : baseEnd_1009358 < baseStart_1009358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009362 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_1009362 : Nat := 118140960795 + 1009362 * 2 ^ 59
def prefixEnd_1009362 : Nat := 4983230072969 + 3 ^ 40 * 1009362 * 2
def baseEnd_1009362 : Nat := 518287860383585100233035

theorem tailTrace_1009362 : CollatzResearch.WordTrace tailWord_1009362 prefixEnd_1009362 518287860383585100233035 := by
  unfold tailWord_1009362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9203614142315333537603585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24542971046174222766942893 9203614142315333537603585)
  ·
    refine ⟨6902710606736500153202689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9203614142315333537603585 6902710606736500153202689)
    ·
      refine ⟨5177032955052375114902017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6902710606736500153202689 5177032955052375114902017)
      ·
        refine ⟨3882774716289281336176513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5177032955052375114902017 3882774716289281336176513)
        ·
          refine ⟨2912081037216961002132385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3882774716289281336176513 2912081037216961002132385)
          ·
            refine ⟨2184060777912720751599289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2912081037216961002132385 2184060777912720751599289)
            ·
              refine ⟨1638045583434540563699467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184060777912720751599289 1638045583434540563699467)
              ·
                refine ⟨2457068375151810845549201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638045583434540563699467 2457068375151810845549201)
                ·
                  refine ⟨1842801281363858134161901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2457068375151810845549201 1842801281363858134161901)
                  ·
                    refine ⟨691050480511446800310713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842801281363858134161901 691050480511446800310713)
                    ·
                      refine ⟨518287860383585100233035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691050480511446800310713 518287860383585100233035)
                      ·
                        rfl

theorem cell23_1009362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_1009362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009362 prefixEnd_1009362 := by exact prefixLift 1009362
  have htrace : WordTrace (prefixWord ++ tailWord_1009362) baseStart_1009362 baseEnd_1009362 := by
    simpa [prefixWord, tailWord_1009362, baseEnd_1009362] using wordTrace_append hprefix tailTrace_1009362
  have hstable : (prefixWord ++ tailWord_1009362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009362).length < 2 ^ (prefixWord ++ tailWord_1009362).sum := by decide
  have hdescent : baseEnd_1009362 < baseStart_1009362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009375 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 1, 1, 4]
def baseStart_1009375 : Nat := 118140960795 + 1009375 * 2 ^ 59
def prefixEnd_1009375 : Nat := 4983230072969 + 3 ^ 40 * 1009375 * 2
def baseEnd_1009375 : Nat := 518294535632093549370475

theorem tailTrace_1009375 : CollatzResearch.WordTrace tailWord_1009375 prefixEnd_1009375 518294535632093549370475 := by
  unfold tailWord_1009375
  simp only [CollatzResearch.WordTrace]
  refine ⟨36814930718214237370637579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24543287145476158247091719 36814930718214237370637579)
  ·
    refine ⟨55222396077321356055956369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36814930718214237370637579 55222396077321356055956369)
    ·
      refine ⟨41416797057991017041967277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55222396077321356055956369 41416797057991017041967277)
      ·
        refine ⟨15531298896746631390737729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41416797057991017041967277 15531298896746631390737729)
        ·
          refine ⟨11648474172559973543053297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15531298896746631390737729 11648474172559973543053297)
          ·
            refine ⟨8736355629419980157289973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11648474172559973543053297 8736355629419980157289973)
            ·
              refine ⟨819033340258123139745935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8736355629419980157289973 819033340258123139745935)
              ·
                refine ⟨1228550010387184709618903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819033340258123139745935 1228550010387184709618903)
                ·
                  refine ⟨1842825015580777064428355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228550010387184709618903 1842825015580777064428355)
                  ·
                    refine ⟨2764237523371165596642533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1842825015580777064428355 2764237523371165596642533)
                    ·
                      refine ⟨518294535632093549370475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2764237523371165596642533 518294535632093549370475)
                      ·
                        rfl

theorem cell23_1009375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_1009375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009375 prefixEnd_1009375 := by exact prefixLift 1009375
  have htrace : WordTrace (prefixWord ++ tailWord_1009375) baseStart_1009375 baseEnd_1009375 := by
    simpa [prefixWord, tailWord_1009375, baseEnd_1009375] using wordTrace_append hprefix tailTrace_1009375
  have hstable : (prefixWord ++ tailWord_1009375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009375).length < 2 ^ (prefixWord ++ tailWord_1009375).sum := by decide
  have hdescent : baseEnd_1009375 < baseStart_1009375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009398 : List Nat := [5, 1, 1, 1, 1, 3, 3, 8]
def baseStart_1009398 : Nat := 118140960795 + 1009398 * 2 ^ 59
def prefixEnd_1009398 : Nat := 4983230072969 + 3 ^ 40 * 1009398 * 2
def baseEnd_1009398 : Nat := 19196531321746183680847

theorem tailTrace_1009398 : CollatzResearch.WordTrace tailWord_1009398 prefixEnd_1009398 19196531321746183680847 := by
  unfold tailWord_1009398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300985599820682018670303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24543846398087274865816565 2300985599820682018670303)
  ·
    refine ⟨3451478399731023028005455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2300985599820682018670303 3451478399731023028005455)
    ·
      refine ⟨5177217599596534542008183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3451478399731023028005455 5177217599596534542008183)
      ·
        refine ⟨7765826399394801813012275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177217599596534542008183 7765826399394801813012275)
        ·
          refine ⟨11648739599092202719518413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765826399394801813012275 11648739599092202719518413)
          ·
            refine ⟨4368277349659576019819405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11648739599092202719518413 4368277349659576019819405)
            ·
              refine ⟨1638104006122341007432277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4368277349659576019819405 1638104006122341007432277)
              ·
                refine ⟨19196531321746183680847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1638104006122341007432277 19196531321746183680847)
                ·
                  rfl

theorem cell23_1009398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_1009398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009398 prefixEnd_1009398 := by exact prefixLift 1009398
  have htrace : WordTrace (prefixWord ++ tailWord_1009398) baseStart_1009398 baseEnd_1009398 := by
    simpa [prefixWord, tailWord_1009398, baseEnd_1009398] using wordTrace_append hprefix tailTrace_1009398
  have hstable : (prefixWord ++ tailWord_1009398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009398).length < 2 ^ (prefixWord ++ tailWord_1009398).sum := by decide
  have hdescent : baseEnd_1009398 < baseStart_1009398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009415 : List Nat := [1, 1, 4, 4, 2, 1, 3, 7]
def baseStart_1009415 : Nat := 118140960795 + 1009415 * 2 ^ 59
def prefixEnd_1009415 : Nat := 4983230072969 + 3 ^ 40 * 1009415 * 2
def baseEnd_1009415 : Nat := 19196854624380496032233

theorem tailTrace_1009415 : CollatzResearch.WordTrace tailWord_1009415 prefixEnd_1009415 19196854624380496032233 := by
  unfold tailWord_1009415
  simp only [CollatzResearch.WordTrace]
  refine ⟨36816389638069324202093699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24544259758712882801395799 36816389638069324202093699)
  ·
    refine ⟨55224584457103986303140549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36816389638069324202093699 55224584457103986303140549)
    ·
      refine ⟨10354609585706997431838853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55224584457103986303140549 10354609585706997431838853)
      ·
        refine ⟨1941489297320062018469785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10354609585706997431838853 1941489297320062018469785)
        ·
          refine ⟨1456116972990046513852339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1941489297320062018469785 1456116972990046513852339)
          ·
            refine ⟨2184175459485069770778509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456116972990046513852339 2184175459485069770778509)
            ·
              refine ⟨819065797306901164041941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2184175459485069770778509 819065797306901164041941)
              ·
                refine ⟨19196854624380496032233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 819065797306901164041941 19196854624380496032233)
                ·
                  rfl

theorem cell23_1009415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 7].length) (baseStart_1009415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009415 prefixEnd_1009415 := by exact prefixLift 1009415
  have htrace : WordTrace (prefixWord ++ tailWord_1009415) baseStart_1009415 baseEnd_1009415 := by
    simpa [prefixWord, tailWord_1009415, baseEnd_1009415] using wordTrace_append hprefix tailTrace_1009415
  have hstable : (prefixWord ++ tailWord_1009415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009415).length < 2 ^ (prefixWord ++ tailWord_1009415).sum := by decide
  have hdescent : baseEnd_1009415 < baseStart_1009415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009426 : List Nat := [3, 2, 4, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1009426 : Nat := 118140960795 + 1009426 * 2 ^ 59
def prefixEnd_1009426 : Nat := 4983230072969 + 3 ^ 40 * 1009426 * 2
def baseEnd_1009426 : Nat := 518320723145472849832741

theorem tailTrace_1009426 : CollatzResearch.WordTrace tailWord_1009426 prefixEnd_1009426 518320723145472849832741 := by
  unfold tailWord_1009426
  simp only [CollatzResearch.WordTrace]
  refine ⟨9204197710257368270186033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24544527227352982053829421 9204197710257368270186033)
  ·
    refine ⟨6903148282693026202639525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9204197710257368270186033 6903148282693026202639525)
    ·
      refine ⟨1294340303004942412994911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6903148282693026202639525 1294340303004942412994911)
      ·
        refine ⟨1941510454507413619492367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294340303004942412994911 1941510454507413619492367)
        ·
          refine ⟨2912265681761120429238551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941510454507413619492367 2912265681761120429238551)
          ·
            refine ⟨4368398522641680643857827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912265681761120429238551 4368398522641680643857827)
            ·
              refine ⟨6552597783962520965786741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368398522641680643857827 6552597783962520965786741)
              ·
                refine ⟨614306042246486340542507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6552597783962520965786741 614306042246486340542507)
                ·
                  refine ⟨921459063369729510813761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614306042246486340542507 921459063369729510813761)
                  ·
                    refine ⟨691094297527297133110321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921459063369729510813761 691094297527297133110321)
                    ·
                      refine ⟨518320723145472849832741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691094297527297133110321 518320723145472849832741)
                      ·
                        rfl

theorem cell23_1009426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1009426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009426 prefixEnd_1009426 := by exact prefixLift 1009426
  have htrace : WordTrace (prefixWord ++ tailWord_1009426) baseStart_1009426 baseEnd_1009426 := by
    simpa [prefixWord, tailWord_1009426, baseEnd_1009426] using wordTrace_append hprefix tailTrace_1009426
  have hstable : (prefixWord ++ tailWord_1009426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009426).length < 2 ^ (prefixWord ++ tailWord_1009426).sum := by decide
  have hdescent : baseEnd_1009426 < baseStart_1009426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009435 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 1, 3, 2]
def baseStart_1009435 : Nat := 118140960795 + 1009435 * 2 ^ 59
def prefixEnd_1009435 : Nat := 4983230072969 + 3 ^ 40 * 1009435 * 2
def baseEnd_1009435 : Nat := 518325344471363314620199

theorem tailTrace_1009435 : CollatzResearch.WordTrace tailWord_1009435 prefixEnd_1009435 518325344471363314620199 := by
  unfold tailWord_1009435
  simp only [CollatzResearch.WordTrace]
  refine ⟨36817119097996867617821759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24544746065331245078547839 36817119097996867617821759)
  ·
    refine ⟨55225678646995301426732639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36817119097996867617821759 55225678646995301426732639)
    ·
      refine ⟨82838517970492952140098959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55225678646995301426732639 82838517970492952140098959)
      ·
        refine ⟨124257776955739428210148439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82838517970492952140098959 124257776955739428210148439)
        ·
          refine ⟨186386665433609142315222659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124257776955739428210148439 186386665433609142315222659)
          ·
            refine ⟨279579998150413713472833989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186386665433609142315222659 279579998150413713472833989)
            ·
              refine ⟨52421249653202571276156373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279579998150413713472833989 52421249653202571276156373)
              ·
                refine ⟨1228623038746935264284915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52421249653202571276156373 1228623038746935264284915)
                ·
                  refine ⟨1842934558120402896427373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228623038746935264284915 1842934558120402896427373)
                  ·
                    refine ⟨691100459295151086160265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842934558120402896427373 691100459295151086160265)
                    ·
                      refine ⟨518325344471363314620199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691100459295151086160265 518325344471363314620199)
                      ·
                        rfl

theorem cell23_1009435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 3, 2].length) (baseStart_1009435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009435 prefixEnd_1009435 := by exact prefixLift 1009435
  have htrace : WordTrace (prefixWord ++ tailWord_1009435) baseStart_1009435 baseEnd_1009435 := by
    simpa [prefixWord, tailWord_1009435, baseEnd_1009435] using wordTrace_append hprefix tailTrace_1009435
  have hstable : (prefixWord ++ tailWord_1009435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009435).length < 2 ^ (prefixWord ++ tailWord_1009435).sum := by decide
  have hdescent : baseEnd_1009435 < baseStart_1009435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009458 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_1009458 : Nat := 118140960795 + 1009458 * 2 ^ 59
def prefixEnd_1009458 : Nat := 4983230072969 + 3 ^ 40 * 1009458 * 2
def baseEnd_1009458 : Nat := 172779051508805574877531

theorem tailTrace_1009458 : CollatzResearch.WordTrace tailWord_1009458 prefixEnd_1009458 172779051508805574877531 := by
  unfold tailWord_1009458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9204489494228385636477257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24545305317942361697272685 9204489494228385636477257)
  ·
    refine ⟨6903367120671289227357943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9204489494228385636477257 6903367120671289227357943)
    ·
      refine ⟨10355050681006933841036915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6903367120671289227357943 10355050681006933841036915)
      ·
        refine ⟨15532576021510400761555373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10355050681006933841036915 15532576021510400761555373)
        ·
          refine ⟨5824716008066400285583265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15532576021510400761555373 5824716008066400285583265)
          ·
            refine ⟨4368537006049800214187449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5824716008066400285583265 4368537006049800214187449)
            ·
              refine ⟨3276402754537350160640587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4368537006049800214187449 3276402754537350160640587)
              ·
                refine ⟨4914604131806025240960881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276402754537350160640587 4914604131806025240960881)
                ·
                  refine ⟨3685953098854518930720661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4914604131806025240960881 3685953098854518930720661)
                  ·
                    refine ⟨172779051508805574877531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3685953098854518930720661 172779051508805574877531)
                    ·
                      rfl

theorem cell23_1009458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_1009458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009458 prefixEnd_1009458 := by exact prefixLift 1009458
  have htrace : WordTrace (prefixWord ++ tailWord_1009458) baseStart_1009458 baseEnd_1009458 := by
    simpa [prefixWord, tailWord_1009458, baseEnd_1009458] using wordTrace_append hprefix tailTrace_1009458
  have hstable : (prefixWord ++ tailWord_1009458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009458).length < 2 ^ (prefixWord ++ tailWord_1009458).sum := by decide
  have hdescent : baseEnd_1009458 < baseStart_1009458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009459 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 2, 1, 3]
def baseStart_1009459 : Nat := 118140960795 + 1009459 * 2 ^ 59
def prefixEnd_1009459 : Nat := 4983230072969 + 3 ^ 40 * 1009459 * 2
def baseEnd_1009459 : Nat := 518337668007071220720089

theorem tailTrace_1009459 : CollatzResearch.WordTrace tailWord_1009459 prefixEnd_1009459 518337668007071220720089 := by
  unfold tailWord_1009459
  simp only [CollatzResearch.WordTrace]
  refine ⟨36817994449909919716695431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24545329633273279811130287 36817994449909919716695431)
  ·
    refine ⟨55226991674864879575043147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36817994449909919716695431 55226991674864879575043147)
    ·
      refine ⟨82840487512297319362564721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55226991674864879575043147 82840487512297319362564721)
      ·
        refine ⟨62130365634222989521923541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82840487512297319362564721 62130365634222989521923541)
        ·
          refine ⟨1456180444552101316920083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62130365634222989521923541 1456180444552101316920083)
          ·
            refine ⟨2184270666828151975380125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456180444552101316920083 2184270666828151975380125)
            ·
              refine ⟨819101500060556990767547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2184270666828151975380125 819101500060556990767547)
              ·
                refine ⟨1228652250090835486151321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819101500060556990767547 1228652250090835486151321)
                ·
                  refine ⟨921489187568126614613491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1228652250090835486151321 921489187568126614613491)
                  ·
                    refine ⟨1382233781352189921920237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 921489187568126614613491 1382233781352189921920237)
                    ·
                      refine ⟨518337668007071220720089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1382233781352189921920237 518337668007071220720089)
                      ·
                        rfl

theorem cell23_1009459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 1, 3].length) (baseStart_1009459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009459 prefixEnd_1009459 := by exact prefixLift 1009459
  have htrace : WordTrace (prefixWord ++ tailWord_1009459) baseStart_1009459 baseEnd_1009459 := by
    simpa [prefixWord, tailWord_1009459, baseEnd_1009459] using wordTrace_append hprefix tailTrace_1009459
  have hstable : (prefixWord ++ tailWord_1009459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009459).length < 2 ^ (prefixWord ++ tailWord_1009459).sum := by decide
  have hdescent : baseEnd_1009459 < baseStart_1009459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009468 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_1009468 : Nat := 118140960795 + 1009468 * 2 ^ 59
def prefixEnd_1009468 : Nat := 4983230072969 + 3 ^ 40 * 1009468 * 2
def baseEnd_1009468 : Nat := 518342289332961685507547

theorem tailTrace_1009468 : CollatzResearch.WordTrace tailWord_1009468 prefixEnd_1009468 518342289332961685507547 := by
  unfold tailWord_1009468
  simp only [CollatzResearch.WordTrace]
  refine ⟨18409161353438657126886529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24545548471251542835848705 18409161353438657126886529)
  ·
    refine ⟨13806871015078992845164897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18409161353438657126886529 13806871015078992845164897)
    ·
      refine ⟨10355153261309244633873673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13806871015078992845164897 10355153261309244633873673)
      ·
        refine ⟨7766364945981933475405255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10355153261309244633873673 7766364945981933475405255)
        ·
          refine ⟨11649547418972900213107883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7766364945981933475405255 11649547418972900213107883)
          ·
            refine ⟨17474321128459350319661825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11649547418972900213107883 17474321128459350319661825)
            ·
              refine ⟨13105740846344512739746369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17474321128459350319661825 13105740846344512739746369)
              ·
                refine ⟨9829305634758384554809777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13105740846344512739746369 9829305634758384554809777)
                ·
                  refine ⟨7371979226068788416107333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9829305634758384554809777 7371979226068788416107333)
                  ·
                    refine ⟨1382246104887897828020125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7371979226068788416107333 1382246104887897828020125)
                    ·
                      refine ⟨518342289332961685507547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1382246104887897828020125 518342289332961685507547)
                      ·
                        rfl

theorem cell23_1009468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_1009468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009468 prefixEnd_1009468 := by exact prefixLift 1009468
  have htrace : WordTrace (prefixWord ++ tailWord_1009468) baseStart_1009468 baseEnd_1009468 := by
    simpa [prefixWord, tailWord_1009468, baseEnd_1009468] using wordTrace_append hprefix tailTrace_1009468
  have hstable : (prefixWord ++ tailWord_1009468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009468).length < 2 ^ (prefixWord ++ tailWord_1009468).sum := by decide
  have hdescent : baseEnd_1009468 < baseStart_1009468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009469 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1009469 : Nat := 118140960795 + 1009469 * 2 ^ 59
def prefixEnd_1009469 : Nat := 4983230072969 + 3 ^ 40 * 1009469 * 2
def baseEnd_1009469 : Nat := 518342802813616181595043

theorem tailTrace_1009469 : CollatzResearch.WordTrace tailWord_1009469 prefixEnd_1009469 518342802813616181595043 := by
  unfold tailWord_1009469
  simp only [CollatzResearch.WordTrace]
  refine ⟨36818359179873691424559461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24545572786582460949706307 36818359179873691424559461)
  ·
    refine ⟨6903442346226317142104899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36818359179873691424559461 6903442346226317142104899)
    ·
      refine ⟨10355163519339475713157349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6903442346226317142104899 10355163519339475713157349)
      ·
        refine ⟨1941593159876151696217003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10355163519339475713157349 1941593159876151696217003)
        ·
          refine ⟨2912389739814227544325505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941593159876151696217003 2912389739814227544325505)
          ·
            refine ⟨2184292304860670658244129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2912389739814227544325505 2184292304860670658244129)
            ·
              refine ⟨1638219228645502993683097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184292304860670658244129 1638219228645502993683097)
              ·
                refine ⟨1228664421484127245262323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638219228645502993683097 1228664421484127245262323)
                ·
                  refine ⟨1842996632226190867893485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228664421484127245262323 1842996632226190867893485)
                  ·
                    refine ⟨691123737084821575460057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842996632226190867893485 691123737084821575460057)
                    ·
                      refine ⟨518342802813616181595043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691123737084821575460057 518342802813616181595043)
                      ·
                        rfl

theorem cell23_1009469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1009469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009469 prefixEnd_1009469 := by exact prefixLift 1009469
  have htrace : WordTrace (prefixWord ++ tailWord_1009469) baseStart_1009469 baseEnd_1009469 := by
    simpa [prefixWord, tailWord_1009469, baseEnd_1009469] using wordTrace_append hprefix tailTrace_1009469
  have hstable : (prefixWord ++ tailWord_1009469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009469).length < 2 ^ (prefixWord ++ tailWord_1009469).sum := by decide
  have hdescent : baseEnd_1009469 < baseStart_1009469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009485 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1009485 : Nat := 118140960795 + 1009485 * 2 ^ 59
def prefixEnd_1009485 : Nat := 4983230072969 + 3 ^ 40 * 1009485 * 2
def baseEnd_1009485 : Nat := 518351018504088118994969

theorem tailTrace_1009485 : CollatzResearch.WordTrace tailWord_1009485 prefixEnd_1009485 518351018504088118994969 := by
  unfold tailWord_1009485
  simp only [CollatzResearch.WordTrace]
  refine ⟨36818942747815726157141909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24545961831877150771427939 36818942747815726157141909)
  ·
    refine ⟨1725887941303862163616027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36818942747815726157141909 1725887941303862163616027)
    ·
      refine ⟨2588831911955793245424041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725887941303862163616027 2588831911955793245424041)
      ·
        refine ⟨1941623933966844934068031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2588831911955793245424041 1941623933966844934068031)
        ·
          refine ⟨2912435900950267401102047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941623933966844934068031 2912435900950267401102047)
          ·
            refine ⟨4368653851425401101653071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912435900950267401102047 4368653851425401101653071)
            ·
              refine ⟨6552980777138101652479607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368653851425401101653071 6552980777138101652479607)
              ·
                refine ⟨9829471165707152478719411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6552980777138101652479607 9829471165707152478719411)
                ·
                  refine ⟨14744206748560728718079117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9829471165707152478719411 14744206748560728718079117)
                  ·
                    refine ⟨5529077530710273269279669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14744206748560728718079117 5529077530710273269279669)
                    ·
                      refine ⟨518351018504088118994969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5529077530710273269279669 518351018504088118994969)
                      ·
                        rfl

theorem cell23_1009485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1009485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009485 prefixEnd_1009485 := by exact prefixLift 1009485
  have htrace : WordTrace (prefixWord ++ tailWord_1009485) baseStart_1009485 baseEnd_1009485 := by
    simpa [prefixWord, tailWord_1009485, baseEnd_1009485] using wordTrace_append hprefix tailTrace_1009485
  have hstable : (prefixWord ++ tailWord_1009485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009485).length < 2 ^ (prefixWord ++ tailWord_1009485).sum := by decide
  have hdescent : baseEnd_1009485 < baseStart_1009485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009491 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 6]
def baseStart_1009491 : Nat := 118140960795 + 1009491 * 2 ^ 59
def prefixEnd_1009491 : Nat := 4983230072969 + 3 ^ 40 * 1009491 * 2
def baseEnd_1009491 : Nat := 518354099388015095519941

theorem tailTrace_1009491 : CollatzResearch.WordTrace tailWord_1009491 prefixEnd_1009491 518354099388015095519941 := by
  unfold tailWord_1009491
  simp only [CollatzResearch.WordTrace]
  refine ⟨36819161585793989181860327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24546107723862659454573551 36819161585793989181860327)
  ·
    refine ⟨55228742378690983772790491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36819161585793989181860327 55228742378690983772790491)
    ·
      refine ⟨82843113568036475659185737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55228742378690983772790491 82843113568036475659185737)
      ·
        refine ⟨62132335176027356744389303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82843113568036475659185737 62132335176027356744389303)
        ·
          refine ⟨93198502764041035116583955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62132335176027356744389303 93198502764041035116583955)
          ·
            refine ⟨139797754146061552674875933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93198502764041035116583955 139797754146061552674875933)
            ·
              refine ⟨52424157804773082253078475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139797754146061552674875933 52424157804773082253078475)
              ·
                refine ⟨78636236707159623379617713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52424157804773082253078475 78636236707159623379617713)
                ·
                  refine ⟨58977177530369717534713285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78636236707159623379617713 58977177530369717534713285)
                  ·
                    refine ⟨11058220786944322037758741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58977177530369717534713285 11058220786944322037758741)
                    ·
                      refine ⟨518354099388015095519941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11058220786944322037758741 518354099388015095519941)
                      ·
                        rfl

theorem cell23_1009491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_1009491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009491 prefixEnd_1009491 := by exact prefixLift 1009491
  have htrace : WordTrace (prefixWord ++ tailWord_1009491) baseStart_1009491 baseEnd_1009491 := by
    simpa [prefixWord, tailWord_1009491, baseEnd_1009491] using wordTrace_append hprefix tailTrace_1009491
  have hstable : (prefixWord ++ tailWord_1009491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009491).length < 2 ^ (prefixWord ++ tailWord_1009491).sum := by decide
  have hdescent : baseEnd_1009491 < baseStart_1009491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009516 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 2, 2, 2]
def baseStart_1009516 : Nat := 118140960795 + 1009516 * 2 ^ 59
def prefixEnd_1009516 : Nat := 4983230072969 + 3 ^ 40 * 1009516 * 2
def baseEnd_1009516 : Nat := 518366936404377497707327

theorem tailTrace_1009516 : CollatzResearch.WordTrace tailWord_1009516 prefixEnd_1009516 518366936404377497707327 := by
  unfold tailWord_1009516
  simp only [CollatzResearch.WordTrace]
  refine ⟨18410036705351709225760201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24546715607135612301013601 18410036705351709225760201)
  ·
    refine ⟨13807527529013781919320151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18410036705351709225760201 13807527529013781919320151)
    ·
      refine ⟨20711291293520672878980227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13807527529013781919320151 20711291293520672878980227)
      ·
        refine ⟨31066936940281009318470341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20711291293520672878980227 31066936940281009318470341)
        ·
          refine ⟨5825050676302689247213189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31066936940281009318470341 5825050676302689247213189)
          ·
            refine ⟨1092197001806754233852473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5825050676302689247213189 1092197001806754233852473)
            ·
              refine ⟨819147751355065675389355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092197001806754233852473 819147751355065675389355)
              ·
                refine ⟨1228721627032598513084033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819147751355065675389355 1228721627032598513084033)
                ·
                  refine ⟨921541220274448884813025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1228721627032598513084033 921541220274448884813025)
                  ·
                    refine ⟨691155915205836663609769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921541220274448884813025 691155915205836663609769)
                    ·
                      refine ⟨518366936404377497707327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691155915205836663609769 518366936404377497707327)
                      ·
                        rfl

theorem cell23_1009516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_1009516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009516 prefixEnd_1009516 := by exact prefixLift 1009516
  have htrace : WordTrace (prefixWord ++ tailWord_1009516) baseStart_1009516 baseEnd_1009516 := by
    simpa [prefixWord, tailWord_1009516, baseEnd_1009516] using wordTrace_append hprefix tailTrace_1009516
  have hstable : (prefixWord ++ tailWord_1009516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009516).length < 2 ^ (prefixWord ++ tailWord_1009516).sum := by decide
  have hdescent : baseEnd_1009516 < baseStart_1009516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009568 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1009568 : Nat := 118140960795 + 1009568 * 2 ^ 59
def prefixEnd_1009568 : Nat := 4983230072969 + 3 ^ 40 * 1009568 * 2
def baseEnd_1009568 : Nat := 518393637398411294257087

theorem tailTrace_1009568 : CollatzResearch.WordTrace tailWord_1009568 prefixEnd_1009568 518393637398411294257087 := by
  unfold tailWord_1009568
  simp only [CollatzResearch.WordTrace]
  refine ⟨18410985003257515666206679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24547980004343354221608905 18410985003257515666206679)
  ·
    refine ⟨27616477504886273499310019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18410985003257515666206679 27616477504886273499310019)
    ·
      refine ⟨41424716257329410248965029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27616477504886273499310019 41424716257329410248965029)
      ·
        refine ⟨7767134298249264421680943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41424716257329410248965029 7767134298249264421680943)
        ·
          refine ⟨11650701447373896632521415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767134298249264421680943 11650701447373896632521415)
          ·
            refine ⟨17476052171060844948782123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650701447373896632521415 17476052171060844948782123)
            ·
              refine ⟨26214078256591267423173185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17476052171060844948782123 26214078256591267423173185)
              ·
                refine ⟨19660558692443450567379889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26214078256591267423173185 19660558692443450567379889)
                ·
                  refine ⟨14745419019332587925534917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19660558692443450567379889 14745419019332587925534917)
                  ·
                    refine ⟨2764766066124860236037797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14745419019332587925534917 2764766066124860236037797)
                    ·
                      refine ⟨518393637398411294257087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2764766066124860236037797 518393637398411294257087)
                      ·
                        rfl

theorem cell23_1009568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1009568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009568 prefixEnd_1009568 := by exact prefixLift 1009568
  have htrace : WordTrace (prefixWord ++ tailWord_1009568) baseStart_1009568 baseEnd_1009568 := by
    simpa [prefixWord, tailWord_1009568, baseEnd_1009568] using wordTrace_append hprefix tailTrace_1009568
  have hstable : (prefixWord ++ tailWord_1009568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009568).length < 2 ^ (prefixWord ++ tailWord_1009568).sum := by decide
  have hdescent : baseEnd_1009568 < baseStart_1009568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009572 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_1009572 : Nat := 118140960795 + 1009572 * 2 ^ 59
def prefixEnd_1009572 : Nat := 4983230072969 + 3 ^ 40 * 1009572 * 2
def baseEnd_1009572 : Nat := 518395691321029278607069

theorem tailTrace_1009572 : CollatzResearch.WordTrace tailWord_1009572 prefixEnd_1009572 518395691321029278607069 := by
  unfold tailWord_1009572
  simp only [CollatzResearch.WordTrace]
  refine ⟨18411057949250270007779485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24548077265667026677039313 18411057949250270007779485)
  ·
    refine ⟨6904146730968851252917307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18411057949250270007779485 6904146730968851252917307)
    ·
      refine ⟨10356220096453276879375961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6904146730968851252917307 10356220096453276879375961)
      ·
        refine ⟨7767165072339957659531971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10356220096453276879375961 7767165072339957659531971)
        ·
          refine ⟨11650747608509936489297957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767165072339957659531971 11650747608509936489297957)
          ·
            refine ⟨2184515176595613091743367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11650747608509936489297957 2184515176595613091743367)
            ·
              refine ⟨3276772764893419637615051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184515176595613091743367 3276772764893419637615051)
              ·
                refine ⟨4915159147340129456422577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276772764893419637615051 4915159147340129456422577)
                ·
                  refine ⟨3686369360505097092316933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4915159147340129456422577 3686369360505097092316933)
                  ·
                    refine ⟨691194255094705704809425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3686369360505097092316933 691194255094705704809425)
                    ·
                      refine ⟨518395691321029278607069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691194255094705704809425 518395691321029278607069)
                      ·
                        rfl

theorem cell23_1009572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_1009572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009572 prefixEnd_1009572 := by exact prefixLift 1009572
  have htrace : WordTrace (prefixWord ++ tailWord_1009572) baseStart_1009572 baseEnd_1009572 := by
    simpa [prefixWord, tailWord_1009572, baseEnd_1009572] using wordTrace_append hprefix tailTrace_1009572
  have hstable : (prefixWord ++ tailWord_1009572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009572).length < 2 ^ (prefixWord ++ tailWord_1009572).sum := by decide
  have hdescent : baseEnd_1009572 < baseStart_1009572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009612 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 6]
def baseStart_1009612 : Nat := 118140960795 + 1009612 * 2 ^ 59
def prefixEnd_1009612 : Nat := 4983230072969 + 3 ^ 40 * 1009612 * 2
def baseEnd_1009612 : Nat := 57601803394134346900765

theorem tailTrace_1009612 : CollatzResearch.WordTrace tailWord_1009612 prefixEnd_1009612 57601803394134346900765 := by
  unfold tailWord_1009612
  simp only [CollatzResearch.WordTrace]
  refine ⟨18411787409177813423507545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24549049878903751231343393 18411787409177813423507545)
  ·
    refine ⟨13808840556883360067630659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18411787409177813423507545 13808840556883360067630659)
    ·
      refine ⟨20713260835325040101445989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13808840556883360067630659 20713260835325040101445989)
      ·
        refine ⟨3883736406623445019021123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20713260835325040101445989 3883736406623445019021123)
        ·
          refine ⟨5825604609935167528531685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883736406623445019021123 5825604609935167528531685)
          ·
            refine ⟨1092300864362843911599691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5825604609935167528531685 1092300864362843911599691)
            ·
              refine ⟨1638451296544265867399537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092300864362843911599691 1638451296544265867399537)
              ·
                refine ⟨1228838472408199400549653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638451296544265867399537 1228838472408199400549653)
                ·
                  refine ⟨57601803394134346900765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1228838472408199400549653 57601803394134346900765)
                  ·
                    rfl

theorem cell23_1009612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_1009612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009612 prefixEnd_1009612 := by exact prefixLift 1009612
  have htrace : WordTrace (prefixWord ++ tailWord_1009612) baseStart_1009612 baseEnd_1009612 := by
    simpa [prefixWord, tailWord_1009612, baseEnd_1009612] using wordTrace_append hprefix tailTrace_1009612
  have hstable : (prefixWord ++ tailWord_1009612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009612).length < 2 ^ (prefixWord ++ tailWord_1009612).sum := by decide
  have hdescent : baseEnd_1009612 < baseStart_1009612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009629 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 6]
def baseStart_1009629 : Nat := 118140960795 + 1009629 * 2 ^ 59
def prefixEnd_1009629 : Nat := 4983230072969 + 3 ^ 40 * 1009629 * 2
def baseEnd_1009629 : Nat := 57602773302037283954923

theorem tailTrace_1009629 : CollatzResearch.WordTrace tailWord_1009629 prefixEnd_1009629 57602773302037283954923 := by
  unfold tailWord_1009629
  simp only [CollatzResearch.WordTrace]
  refine ⟨36824194859294038750383941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24549463239529359166922627 36824194859294038750383941)
  ·
    refine ⟨6904536536117632265696989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36824194859294038750383941 6904536536117632265696989)
    ·
      refine ⟨2589201201044112099636371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6904536536117632265696989 2589201201044112099636371)
      ·
        refine ⟨3883801801566168149454557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589201201044112099636371 3883801801566168149454557)
        ·
          refine ⟨1456425675587313056045459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3883801801566168149454557 1456425675587313056045459)
          ·
            refine ⟨2184638513380969584068189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456425675587313056045459 2184638513380969584068189)
            ·
              refine ⟨819239442517863594025571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2184638513380969584068189 819239442517863594025571)
              ·
                refine ⟨1228859163776795391038357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819239442517863594025571 1228859163776795391038357)
                ·
                  refine ⟨57602773302037283954923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1228859163776795391038357 57602773302037283954923)
                  ·
                    rfl

theorem cell23_1009629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_1009629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009629 prefixEnd_1009629 := by exact prefixLift 1009629
  have htrace : WordTrace (prefixWord ++ tailWord_1009629) baseStart_1009629 baseEnd_1009629 := by
    simpa [prefixWord, tailWord_1009629, baseEnd_1009629] using wordTrace_append hprefix tailTrace_1009629
  have hstable : (prefixWord ++ tailWord_1009629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009629).length < 2 ^ (prefixWord ++ tailWord_1009629).sum := by decide
  have hdescent : baseEnd_1009629 < baseStart_1009629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009642 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_1009642 : Nat := 118140960795 + 1009642 * 2 ^ 59
def prefixEnd_1009642 : Nat := 4983230072969 + 3 ^ 40 * 1009642 * 2
def baseEnd_1009642 : Nat := 172810544988948001577249

theorem tailTrace_1009642 : CollatzResearch.WordTrace tailWord_1009642 prefixEnd_1009642 172810544988948001577249 := by
  unfold tailWord_1009642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206167252061735492651795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24549779338831294647071453 9206167252061735492651795)
  ·
    refine ⟨13809250878092603238977693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9206167252061735492651795 13809250878092603238977693)
    ·
      refine ⟨5178469079284726214616635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13809250878092603238977693 5178469079284726214616635)
      ·
        refine ⟨7767703618927089321924953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178469079284726214616635 7767703618927089321924953)
        ·
          refine ⟨5825777714195316991443715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7767703618927089321924953 5825777714195316991443715)
          ·
            refine ⟨8738666571292975487165573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825777714195316991443715 8738666571292975487165573)
            ·
              refine ⟨1638499982117432903843545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8738666571292975487165573 1638499982117432903843545)
              ·
                refine ⟨1228874986588074677882659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638499982117432903843545 1228874986588074677882659)
                ·
                  refine ⟨1843312479882112016823989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228874986588074677882659 1843312479882112016823989)
                  ·
                    refine ⟨172810544988948001577249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1843312479882112016823989 172810544988948001577249)
                    ·
                      rfl

theorem cell23_1009642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_1009642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009642 prefixEnd_1009642 := by exact prefixLift 1009642
  have htrace : WordTrace (prefixWord ++ tailWord_1009642) baseStart_1009642 baseEnd_1009642 := by
    simpa [prefixWord, tailWord_1009642, baseEnd_1009642] using wordTrace_append hprefix tailTrace_1009642
  have hstable : (prefixWord ++ tailWord_1009642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009642).length < 2 ^ (prefixWord ++ tailWord_1009642).sum := by decide
  have hdescent : baseEnd_1009642 < baseStart_1009642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009672 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1009672 : Nat := 118140960795 + 1009672 * 2 ^ 59
def prefixEnd_1009672 : Nat := 4983230072969 + 3 ^ 40 * 1009672 * 2
def baseEnd_1009672 : Nat := 172815679795492962452203

theorem tailTrace_1009672 : CollatzResearch.WordTrace tailWord_1009672 prefixEnd_1009672 172815679795492962452203 := by
  unfold tailWord_1009672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18412881599069128547099635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24550508798758838062799513 18412881599069128547099635)
  ·
    refine ⟨27619322398603692820649453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18412881599069128547099635 27619322398603692820649453)
    ·
      refine ⟨10357245899476384807743545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27619322398603692820649453 10357245899476384807743545)
      ·
        refine ⟨7767934424607288605807659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10357245899476384807743545 7767934424607288605807659)
        ·
          refine ⟨11651901636910932908711489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767934424607288605807659 11651901636910932908711489)
          ·
            refine ⟨8738926227683199681533617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11651901636910932908711489 8738926227683199681533617)
            ·
              refine ⟨6554194670762399761150213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8738926227683199681533617 6554194670762399761150213)
              ·
                refine ⟨1228911500767949955215665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6554194670762399761150213 1228911500767949955215665)
                ·
                  refine ⟨921683625575962466411749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1228911500767949955215665 921683625575962466411749)
                  ·
                    refine ⟨172815679795492962452203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 921683625575962466411749 172815679795492962452203)
                    ·
                      rfl

theorem cell23_1009672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1009672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009672 prefixEnd_1009672 := by exact prefixLift 1009672
  have htrace : WordTrace (prefixWord ++ tailWord_1009672) baseStart_1009672 baseEnd_1009672 := by
    simpa [prefixWord, tailWord_1009672, baseEnd_1009672] using wordTrace_append hprefix tailTrace_1009672
  have hstable : (prefixWord ++ tailWord_1009672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009672).length < 2 ^ (prefixWord ++ tailWord_1009672).sum := by decide
  have hdescent : baseEnd_1009672 < baseStart_1009672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009712 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 3]
def baseStart_1009712 : Nat := 118140960795 + 1009712 * 2 ^ 59
def prefixEnd_1009712 : Nat := 4983230072969 + 3 ^ 40 * 1009712 * 2
def baseEnd_1009712 : Nat := 518467578612658730856425

theorem tailTrace_1009712 : CollatzResearch.WordTrace tailWord_1009712 prefixEnd_1009712 518467578612658730856425 := by
  unfold tailWord_1009712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413611058996671962827695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24551481411995562617103593 18413611058996671962827695)
  ·
    refine ⟨27620416588495007944241543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18413611058996671962827695 27620416588495007944241543)
    ·
      refine ⟨41430624882742511916362315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27620416588495007944241543 41430624882742511916362315)
      ·
        refine ⟨62145937324113767874543473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41430624882742511916362315 62145937324113767874543473)
        ·
          refine ⟨46609452993085325905907605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62145937324113767874543473 46609452993085325905907605)
          ·
            refine ⟨2184818109050874651839419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46609452993085325905907605 2184818109050874651839419)
            ·
              refine ⟨3277227163576311977759129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184818109050874651839419 3277227163576311977759129)
              ·
                refine ⟨2457920372682233983319347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277227163576311977759129 2457920372682233983319347)
                ·
                  refine ⟨3686880559023350974979021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457920372682233983319347 3686880559023350974979021)
                  ·
                    refine ⟨1382580209633756615617133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3686880559023350974979021 1382580209633756615617133)
                    ·
                      refine ⟨518467578612658730856425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1382580209633756615617133 518467578612658730856425)
                      ·
                        rfl

theorem cell23_1009712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_1009712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009712 prefixEnd_1009712 := by exact prefixLift 1009712
  have htrace : WordTrace (prefixWord ++ tailWord_1009712) baseStart_1009712 baseEnd_1009712 := by
    simpa [prefixWord, tailWord_1009712, baseEnd_1009712] using wordTrace_append hprefix tailTrace_1009712
  have hstable : (prefixWord ++ tailWord_1009712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009712).length < 2 ^ (prefixWord ++ tailWord_1009712).sum := by decide
  have hdescent : baseEnd_1009712 < baseStart_1009712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009716 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1009716 : Nat := 118140960795 + 1009716 * 2 ^ 59
def prefixEnd_1009716 : Nat := 4983230072969 + 3 ^ 40 * 1009716 * 2
def baseEnd_1009716 : Nat := 518469632535276715206407

theorem tailTrace_1009716 : CollatzResearch.WordTrace tailWord_1009716 prefixEnd_1009716 518469632535276715206407 := by
  unfold tailWord_1009716
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413684004989426304400501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24551578673319235072534001 18413684004989426304400501)
  ·
    refine ⟨1726282875467758716037547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18413684004989426304400501 1726282875467758716037547)
    ·
      refine ⟨2589424313201638074056321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726282875467758716037547 2589424313201638074056321)
      ·
        refine ⟨1942068234901228555542241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2589424313201638074056321 1942068234901228555542241)
        ·
          refine ⟨1456551176175921416656681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1942068234901228555542241 1456551176175921416656681)
          ·
            refine ⟨1092413382131941062492511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456551176175921416656681 1092413382131941062492511)
            ·
              refine ⟨1638620073197911593738767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092413382131941062492511 1638620073197911593738767)
              ·
                refine ⟨2457930109796867390608151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638620073197911593738767 2457930109796867390608151)
                ·
                  refine ⟨3686895164695301085912227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457930109796867390608151 3686895164695301085912227)
                  ·
                    refine ⟨5530342747042951628868341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3686895164695301085912227 5530342747042951628868341)
                    ·
                      refine ⟨518469632535276715206407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5530342747042951628868341 518469632535276715206407)
                      ·
                        rfl

theorem cell23_1009716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1009716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009716 prefixEnd_1009716 := by exact prefixLift 1009716
  have htrace : WordTrace (prefixWord ++ tailWord_1009716) baseStart_1009716 baseEnd_1009716 := by
    simpa [prefixWord, tailWord_1009716, baseEnd_1009716] using wordTrace_append hprefix tailTrace_1009716
  have hstable : (prefixWord ++ tailWord_1009716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009716).length < 2 ^ (prefixWord ++ tailWord_1009716).sum := by decide
  have hdescent : baseEnd_1009716 < baseStart_1009716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009735 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1009735 : Nat := 118140960795 + 1009735 * 2 ^ 59
def prefixEnd_1009735 : Nat := 4983230072969 + 3 ^ 40 * 1009735 * 2
def baseEnd_1009735 : Nat := 518479388667712140868819

theorem tailTrace_1009735 : CollatzResearch.WordTrace tailWord_1009735 prefixEnd_1009735 518479388667712140868819 := by
  unfold tailWord_1009735
  simp only [CollatzResearch.WordTrace]
  refine ⟨36828060996910018853742659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24552040664606679235828439 36828060996910018853742659)
  ·
    refine ⟨55242091495365028280613989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36828060996910018853742659 55242091495365028280613989)
    ·
      refine ⟨10357892155380942802615123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55242091495365028280613989 10357892155380942802615123)
      ·
        refine ⟨15536838233071414203922685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357892155380942802615123 15536838233071414203922685)
        ·
          refine ⟨5826314337401780326471007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15536838233071414203922685 5826314337401780326471007)
          ·
            refine ⟨8739471506102670489706511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826314337401780326471007 8739471506102670489706511)
            ·
              refine ⟨13109207259154005734559767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739471506102670489706511 13109207259154005734559767)
              ·
                refine ⟨19663810888731008601839651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13109207259154005734559767 19663810888731008601839651)
                ·
                  refine ⟨29495716333096512902759477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19663810888731008601839651 29495716333096512902759477)
                  ·
                    refine ⟨2765223406227798084633701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29495716333096512902759477 2765223406227798084633701)
                    ·
                      refine ⟨518479388667712140868819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2765223406227798084633701 518479388667712140868819)
                      ·
                        rfl

theorem cell23_1009735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1009735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009735 prefixEnd_1009735 := by exact prefixLift 1009735
  have htrace : WordTrace (prefixWord ++ tailWord_1009735) baseStart_1009735 baseEnd_1009735 := by
    simpa [prefixWord, tailWord_1009735, baseEnd_1009735] using wordTrace_append hprefix tailTrace_1009735
  have hstable : (prefixWord ++ tailWord_1009735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009735).length < 2 ^ (prefixWord ++ tailWord_1009735).sum := by decide
  have hdescent : baseEnd_1009735 < baseStart_1009735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009769 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 4, 2, 2]
def baseStart_1009769 : Nat := 118140960795 + 1009769 * 2 ^ 59
def prefixEnd_1009769 : Nat := 4983230072969 + 3 ^ 40 * 1009769 * 2
def baseEnd_1009769 : Nat := 518496847009965007843663

theorem tailTrace_1009769 : CollatzResearch.WordTrace tailWord_1009769 prefixEnd_1009769 518496847009965007843663 := by
  unfold tailWord_1009769
  simp only [CollatzResearch.WordTrace]
  refine ⟨36829301078786842660480361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24552867385857895106986907 36829301078786842660480361)
  ·
    refine ⟨27621975809090131995360271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36829301078786842660480361 27621975809090131995360271)
    ·
      refine ⟨41432963713635197993040407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27621975809090131995360271 41432963713635197993040407)
      ·
        refine ⟨62149445570452796989560611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41432963713635197993040407 62149445570452796989560611)
        ·
          refine ⟨93224168355679195484340917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62149445570452796989560611 93224168355679195484340917)
          ·
            refine ⟨8739765783344924576656961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93224168355679195484340917 8739765783344924576656961)
            ·
              refine ⟨6554824337508693432492721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8739765783344924576656961 6554824337508693432492721)
              ·
                refine ⟨4916118253131520074369541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554824337508693432492721 4916118253131520074369541)
                ·
                  refine ⟨921772172462160013944289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4916118253131520074369541 921772172462160013944289)
                  ·
                    refine ⟨691329129346620010458217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921772172462160013944289 691329129346620010458217)
                    ·
                      refine ⟨518496847009965007843663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691329129346620010458217 518496847009965007843663)
                      ·
                        rfl

theorem cell23_1009769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 2, 2].length) (baseStart_1009769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009769 prefixEnd_1009769 := by exact prefixLift 1009769
  have htrace : WordTrace (prefixWord ++ tailWord_1009769) baseStart_1009769 baseEnd_1009769 := by
    simpa [prefixWord, tailWord_1009769, baseEnd_1009769] using wordTrace_append hprefix tailTrace_1009769
  have hstable : (prefixWord ++ tailWord_1009769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009769).length < 2 ^ (prefixWord ++ tailWord_1009769).sum := by decide
  have hdescent : baseEnd_1009769 < baseStart_1009769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009826 : List Nat := [3, 3, 1, 3, 1, 1, 3, 3, 5]
def baseStart_1009826 : Nat := 118140960795 + 1009826 * 2 ^ 59
def prefixEnd_1009826 : Nat := 4983230072969 + 3 ^ 40 * 1009826 * 2
def baseEnd_1009826 : Nat := 57614012823030142758989

theorem tailTrace_1009826 : CollatzResearch.WordTrace tailWord_1009826 prefixEnd_1009826 57614012823030142758989 := by
  unfold tailWord_1009826
  simp only [CollatzResearch.WordTrace]
  refine ⟨9207845009895085348826333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24554253359720227596870221 9207845009895085348826333)
  ·
    refine ⟨3452941878710657005809875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9207845009895085348826333 3452941878710657005809875)
    ·
      refine ⟨5179412818065985508714813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452941878710657005809875 5179412818065985508714813)
      ·
        refine ⟨1942279806774744565768055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5179412818065985508714813 1942279806774744565768055)
        ·
          refine ⟨2913419710162116848652083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942279806774744565768055 2913419710162116848652083)
          ·
            refine ⟨4370129565243175272978125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913419710162116848652083 4370129565243175272978125)
            ·
              refine ⟨1638798586966190727366797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4370129565243175272978125 1638798586966190727366797)
              ·
                refine ⟨614549470112321522762549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1638798586966190727366797 614549470112321522762549)
                ·
                  refine ⟨57614012823030142758989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 614549470112321522762549 57614012823030142758989)
                  ·
                    rfl

theorem cell23_1009826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_1009826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009826 prefixEnd_1009826 := by exact prefixLift 1009826
  have htrace : WordTrace (prefixWord ++ tailWord_1009826) baseStart_1009826 baseEnd_1009826 := by
    simpa [prefixWord, tailWord_1009826, baseEnd_1009826] using wordTrace_append hprefix tailTrace_1009826
  have hstable : (prefixWord ++ tailWord_1009826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009826).length < 2 ^ (prefixWord ++ tailWord_1009826).sum := by decide
  have hdescent : baseEnd_1009826 < baseStart_1009826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009865 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 10]
def baseStart_1009865 : Nat := 118140960795 + 1009865 * 2 ^ 59
def prefixEnd_1009865 : Nat := 4983230072969 + 3 ^ 40 * 1009865 * 2
def baseEnd_1009865 : Nat := 57616237905866292471469

theorem tailTrace_1009865 : CollatzResearch.WordTrace tailWord_1009865 prefixEnd_1009865 57616237905866292471469 := by
  unfold tailWord_1009865
  simp only [CollatzResearch.WordTrace]
  refine ⟨36832802486439051055975049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24555201657626034037316699 36832802486439051055975049)
  ·
    refine ⟨27624601864829288291981287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36832802486439051055975049 27624601864829288291981287)
    ·
      refine ⟨41436902797243932437971931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27624601864829288291981287 41436902797243932437971931)
      ·
        refine ⟨62155354195865898656957897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41436902797243932437971931 62155354195865898656957897)
        ·
          refine ⟨46616515646899423992718423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62155354195865898656957897 46616515646899423992718423)
          ·
            refine ⟨69924773470349135989077635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46616515646899423992718423 69924773470349135989077635)
            ·
              refine ⟨104887160205523703983616453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69924773470349135989077635 104887160205523703983616453)
              ·
                refine ⟨19666342538535694496928085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104887160205523703983616453 19666342538535694496928085)
                ·
                  refine ⟨57616237905866292471469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 19666342538535694496928085 57616237905866292471469)
                  ·
                    rfl

theorem cell23_1009865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 10].length) (baseStart_1009865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009865 prefixEnd_1009865 := by exact prefixLift 1009865
  have htrace : WordTrace (prefixWord ++ tailWord_1009865) baseStart_1009865 baseEnd_1009865 := by
    simpa [prefixWord, tailWord_1009865, baseEnd_1009865] using wordTrace_append hprefix tailTrace_1009865
  have hstable : (prefixWord ++ tailWord_1009865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009865).length < 2 ^ (prefixWord ++ tailWord_1009865).sum := by decide
  have hdescent : baseEnd_1009865 < baseStart_1009865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009875 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 9]
def baseStart_1009875 : Nat := 118140960795 + 1009875 * 2 ^ 59
def prefixEnd_1009875 : Nat := 4983230072969 + 3 ^ 40 * 1009875 * 2
def baseEnd_1009875 : Nat := 518551275959341593118175

theorem tailTrace_1009875 : CollatzResearch.WordTrace tailWord_1009875 prefixEnd_1009875 518551275959341593118175 := by
  unfold tailWord_1009875
  simp only [CollatzResearch.WordTrace]
  refine ⟨36833167216402822763839079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24555444810935215175892719 36833167216402822763839079)
  ·
    refine ⟨55249750824604234145758619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36833167216402822763839079 55249750824604234145758619)
    ·
      refine ⟨82874626236906351218637929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55249750824604234145758619 82874626236906351218637929)
      ·
        refine ⟨62155969677679763413978447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82874626236906351218637929 62155969677679763413978447)
        ·
          refine ⟨93233954516519645120967671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62155969677679763413978447 93233954516519645120967671)
          ·
            refine ⟨139850931774779467681451507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93233954516519645120967671 139850931774779467681451507)
            ·
              refine ⟨209776397662169201522177261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139850931774779467681451507 209776397662169201522177261)
              ·
                refine ⟨78666149123313450570816473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209776397662169201522177261 78666149123313450570816473)
                ·
                  refine ⟨58999611842485087928112355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78666149123313450570816473 58999611842485087928112355)
                  ·
                    refine ⟨88499417763727631892168533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58999611842485087928112355 88499417763727631892168533)
                    ·
                      refine ⟨518551275959341593118175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 88499417763727631892168533 518551275959341593118175)
                      ·
                        rfl

theorem cell23_1009875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_1009875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009875 prefixEnd_1009875 := by exact prefixLift 1009875
  have htrace : WordTrace (prefixWord ++ tailWord_1009875) baseStart_1009875 baseEnd_1009875 := by
    simpa [prefixWord, tailWord_1009875, baseEnd_1009875] using wordTrace_append hprefix tailTrace_1009875
  have hstable : (prefixWord ++ tailWord_1009875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009875).length < 2 ^ (prefixWord ++ tailWord_1009875).sum := by decide
  have hdescent : baseEnd_1009875 < baseStart_1009875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009902 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1009902 : Nat := 118140960795 + 1009902 * 2 ^ 59
def prefixEnd_1009902 : Nat := 4983230072969 + 3 ^ 40 * 1009902 * 2
def baseEnd_1009902 : Nat := 518565139937012987480551

theorem tailTrace_1009902 : CollatzResearch.WordTrace tailWord_1009902 prefixEnd_1009902 518565139937012987480551 := by
  unfold tailWord_1009902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604268998413125796883995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24556101324870004250047973 4604268998413125796883995)
  ·
    refine ⟨6906403497619688695325993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4604268998413125796883995 6906403497619688695325993)
    ·
      refine ⟨5179802623214766521494495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6906403497619688695325993 5179802623214766521494495)
      ·
        refine ⟨7769703934822149782241743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179802623214766521494495 7769703934822149782241743)
        ·
          refine ⟨11654555902233224673362615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7769703934822149782241743 11654555902233224673362615)
          ·
            refine ⟨17481833853349837010043923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11654555902233224673362615 17481833853349837010043923)
            ·
              refine ⟨26222750780024755515065885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17481833853349837010043923 26222750780024755515065885)
              ·
                refine ⟨9833531542509283318149707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26222750780024755515065885 9833531542509283318149707)
                ·
                  refine ⟨14750297313763924977224561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9833531542509283318149707 14750297313763924977224561)
                  ·
                    refine ⟨11062722985322943732918421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14750297313763924977224561 11062722985322943732918421)
                    ·
                      refine ⟨518565139937012987480551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11062722985322943732918421 518565139937012987480551)
                      ·
                        rfl

theorem cell23_1009902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1009902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009902 prefixEnd_1009902 := by exact prefixLift 1009902
  have htrace : WordTrace (prefixWord ++ tailWord_1009902) baseStart_1009902 baseEnd_1009902 := by
    simpa [prefixWord, tailWord_1009902, baseEnd_1009902] using wordTrace_append hprefix tailTrace_1009902
  have hstable : (prefixWord ++ tailWord_1009902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009902).length < 2 ^ (prefixWord ++ tailWord_1009902).sum := by decide
  have hdescent : baseEnd_1009902 < baseStart_1009902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009903 : List Nat := [1, 1, 2, 1, 6, 1, 4, 2, 1, 4]
def baseStart_1009903 : Nat := 118140960795 + 1009903 * 2 ^ 59
def prefixEnd_1009903 : Nat := 4983230072969 + 3 ^ 40 * 1009903 * 2
def baseEnd_1009903 : Nat := 172855217805889161189349

theorem tailTrace_1009903 : CollatzResearch.WordTrace tailWord_1009903 prefixEnd_1009903 172855217805889161189349 := by
  unfold tailWord_1009903
  simp only [CollatzResearch.WordTrace]
  refine ⟨36834188460301383545858363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24556125640200922363905575 36834188460301383545858363)
  ·
    refine ⟨55251282690452075318787545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36834188460301383545858363 55251282690452075318787545)
    ·
      refine ⟨41438462017839056489090659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55251282690452075318787545 41438462017839056489090659)
      ·
        refine ⟨62157693026758584733635989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41438462017839056489090659 62157693026758584733635989)
        ·
          refine ⟨2913641860629308659389187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62157693026758584733635989 2913641860629308659389187)
          ·
            refine ⟨4370462790943962989083781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913641860629308659389187 4370462790943962989083781)
            ·
              refine ⟨819461773301993060453209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4370462790943962989083781 819461773301993060453209)
              ·
                refine ⟨614596329976494795339907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819461773301993060453209 614596329976494795339907)
                ·
                  refine ⟨921894494964742193009861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614596329976494795339907 921894494964742193009861)
                  ·
                    refine ⟨172855217805889161189349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 921894494964742193009861 172855217805889161189349)
                    ·
                      rfl

theorem cell23_1009903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 4].length) (baseStart_1009903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009903 prefixEnd_1009903 := by exact prefixLift 1009903
  have htrace : WordTrace (prefixWord ++ tailWord_1009903) baseStart_1009903 baseEnd_1009903 := by
    simpa [prefixWord, tailWord_1009903, baseEnd_1009903] using wordTrace_append hprefix tailTrace_1009903
  have hstable : (prefixWord ++ tailWord_1009903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009903).length < 2 ^ (prefixWord ++ tailWord_1009903).sum := by decide
  have hdescent : baseEnd_1009903 < baseStart_1009903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009919 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 1, 5, 2]
def baseStart_1009919 : Nat := 118140960795 + 1009919 * 2 ^ 59
def prefixEnd_1009919 : Nat := 4983230072969 + 3 ^ 40 * 1009919 * 2
def baseEnd_1009919 : Nat := 518573869108139420967973

theorem tailTrace_1009919 : CollatzResearch.WordTrace tailWord_1009919 prefixEnd_1009919 518573869108139420967973 := by
  unfold tailWord_1009919
  simp only [CollatzResearch.WordTrace]
  refine ⟨36834772028243418278440811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24556514685495612185627207 36834772028243418278440811)
  ·
    refine ⟨55252158042365127417661217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36834772028243418278440811 55252158042365127417661217)
    ·
      refine ⟨41439118531773845563245913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55252158042365127417661217 41439118531773845563245913)
      ·
        refine ⟨31079338898830384172434435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41439118531773845563245913 31079338898830384172434435)
        ·
          refine ⟨46619008348245576258651653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31079338898830384172434435 46619008348245576258651653)
          ·
            refine ⟨8741064065296045548497185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46619008348245576258651653 8741064065296045548497185)
            ·
              refine ⟨6555798048972034161372889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8741064065296045548497185 6555798048972034161372889)
              ·
                refine ⟨4916848536729025621029667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6555798048972034161372889 4916848536729025621029667)
                ·
                  refine ⟨7375272805093538431544501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916848536729025621029667 7375272805093538431544501)
                  ·
                    refine ⟨691431825477519227957297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7375272805093538431544501 691431825477519227957297)
                    ·
                      refine ⟨518573869108139420967973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691431825477519227957297 518573869108139420967973)
                      ·
                        rfl

theorem cell23_1009919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_1009919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009919 prefixEnd_1009919 := by exact prefixLift 1009919
  have htrace : WordTrace (prefixWord ++ tailWord_1009919) baseStart_1009919 baseEnd_1009919 := by
    simpa [prefixWord, tailWord_1009919, baseEnd_1009919] using wordTrace_append hprefix tailTrace_1009919
  have hstable : (prefixWord ++ tailWord_1009919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009919).length < 2 ^ (prefixWord ++ tailWord_1009919).sum := by decide
  have hdescent : baseEnd_1009919 < baseStart_1009919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009943 : List Nat := [1, 1, 3, 4, 1, 2, 1, 5, 1, 1, 3]
def baseStart_1009943 : Nat := 118140960795 + 1009943 * 2 ^ 59
def prefixEnd_1009943 : Nat := 4983230072969 + 3 ^ 40 * 1009943 * 2
def baseEnd_1009943 : Nat := 518586192643847327067863

theorem tailTrace_1009943 : CollatzResearch.WordTrace tailWord_1009943 prefixEnd_1009943 518586192643847327067863 := by
  unfold tailWord_1009943
  simp only [CollatzResearch.WordTrace]
  refine ⟨36835647380156470377314483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24557098253437646918209655 36835647380156470377314483)
  ·
    refine ⟨55253471070234705565971725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36835647380156470377314483 55253471070234705565971725)
    ·
      refine ⟨20720051651338014587239397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55253471070234705565971725 20720051651338014587239397)
      ·
        refine ⟨3885009684625877735107387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20720051651338014587239397 3885009684625877735107387)
        ·
          refine ⟨5827514526938816602661081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885009684625877735107387 5827514526938816602661081)
          ·
            refine ⟨4370635895204112451995811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827514526938816602661081 4370635895204112451995811)
            ·
              refine ⟨6555953842806168677993717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370635895204112451995811 6555953842806168677993717)
              ·
                refine ⟨614620672763078313561911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6555953842806168677993717 614620672763078313561911)
                ·
                  refine ⟨921931009144617470342867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614620672763078313561911 921931009144617470342867)
                  ·
                    refine ⟨1382896513716926205514301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 921931009144617470342867 1382896513716926205514301)
                    ·
                      refine ⟨518586192643847327067863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1382896513716926205514301 518586192643847327067863)
                      ·
                        rfl

theorem cell23_1009943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_1009943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009943 prefixEnd_1009943 := by exact prefixLift 1009943
  have htrace : WordTrace (prefixWord ++ tailWord_1009943) baseStart_1009943 baseEnd_1009943 := by
    simpa [prefixWord, tailWord_1009943, baseEnd_1009943] using wordTrace_append hprefix tailTrace_1009943
  have hstable : (prefixWord ++ tailWord_1009943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009943).length < 2 ^ (prefixWord ++ tailWord_1009943).sum := by decide
  have hdescent : baseEnd_1009943 < baseStart_1009943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009946 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_1009946 : Nat := 118140960795 + 1009946 * 2 ^ 59
def prefixEnd_1009946 : Nat := 4983230072969 + 3 ^ 40 * 1009946 * 2
def baseEnd_1009946 : Nat := 172862577695270271776783

theorem tailTrace_1009946 : CollatzResearch.WordTrace tailWord_1009946 prefixEnd_1009946 172862577695270271776783 := by
  unfold tailWord_1009946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208939199786400472418423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24557171199430401259782461 9208939199786400472418423)
  ·
    refine ⟨13813408799679600708627635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9208939199786400472418423 13813408799679600708627635)
    ·
      refine ⟨20720113199519401062941453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13813408799679600708627635 20720113199519401062941453)
      ·
        refine ⟨7770042449819775398603045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20720113199519401062941453 7770042449819775398603045)
        ·
          refine ⟨1456882959341207887238071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7770042449819775398603045 1456882959341207887238071)
          ·
            refine ⟨2185324439011811830857107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456882959341207887238071 2185324439011811830857107)
            ·
              refine ⟨3277986658517717746285661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185324439011811830857107 3277986658517717746285661)
              ·
                refine ⟨1229244996944144154857123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3277986658517717746285661 1229244996944144154857123)
                ·
                  refine ⟨1843867495416216232285685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229244996944144154857123 1843867495416216232285685)
                  ·
                    refine ⟨172862577695270271776783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1843867495416216232285685 172862577695270271776783)
                    ·
                      rfl

theorem cell23_1009946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_1009946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1009946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1009946 prefixEnd_1009946 := by exact prefixLift 1009946
  have htrace : WordTrace (prefixWord ++ tailWord_1009946) baseStart_1009946 baseEnd_1009946 := by
    simpa [prefixWord, tailWord_1009946, baseEnd_1009946] using wordTrace_append hprefix tailTrace_1009946
  have hstable : (prefixWord ++ tailWord_1009946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009946).length < 2 ^ (prefixWord ++ tailWord_1009946).sum := by decide
  have hdescent : baseEnd_1009946 < baseStart_1009946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010000 : List Nat := [2, 1, 1, 1, 1, 6, 3, 3, 1, 2, 2]
def baseStart_1010000 : Nat := 118140960795 + 1010000 * 2 ^ 59
def prefixEnd_1010000 : Nat := 4983230072969 + 3 ^ 40 * 1010000 * 2
def baseEnd_1010000 : Nat := 518615461041153604055101

theorem tailTrace_1010000 : CollatzResearch.WordTrace tailWord_1010000 prefixEnd_1010000 518615461041153604055101 := by
  unfold tailWord_1010000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18418863170474984556069727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24558484227299979408092969 18418863170474984556069727)
  ·
    refine ⟨27628294755712476834104591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18418863170474984556069727 27628294755712476834104591)
    ·
      refine ⟨41442442133568715251156887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27628294755712476834104591 41442442133568715251156887)
      ·
        refine ⟨62163663200353072876735331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41442442133568715251156887 62163663200353072876735331)
        ·
          refine ⟨93245494800529609315102997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62163663200353072876735331 93245494800529609315102997)
          ·
            refine ⟨4370882568774825436645453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93245494800529609315102997 4370882568774825436645453)
            ·
              refine ⟨1639080963290559538742045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4370882568774825436645453 1639080963290559538742045)
              ·
                refine ⟨614655361233959827028267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1639080963290559538742045 614655361233959827028267)
                ·
                  refine ⟨921983041850939740542401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614655361233959827028267 921983041850939740542401)
                  ·
                    refine ⟨691487281388204805406801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921983041850939740542401 691487281388204805406801)
                    ·
                      refine ⟨518615461041153604055101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691487281388204805406801 518615461041153604055101)
                      ·
                        rfl

theorem cell23_1010000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 1, 2, 2].length) (baseStart_1010000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010000 prefixEnd_1010000 := by exact prefixLift 1010000
  have htrace : WordTrace (prefixWord ++ tailWord_1010000) baseStart_1010000 baseEnd_1010000 := by
    simpa [prefixWord, tailWord_1010000, baseEnd_1010000] using wordTrace_append hprefix tailTrace_1010000
  have hstable : (prefixWord ++ tailWord_1010000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010000).length < 2 ^ (prefixWord ++ tailWord_1010000).sum := by decide
  have hdescent : baseEnd_1010000 < baseStart_1010000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010043 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 1, 3, 2]
def baseStart_1010043 : Nat := 118140960795 + 1010043 * 2 ^ 59
def prefixEnd_1010043 : Nat := 4983230072969 + 3 ^ 40 * 1010043 * 2
def baseEnd_1010043 : Nat := 518637540709296935817403

theorem tailTrace_1010043 : CollatzResearch.WordTrace tailWord_1010043 prefixEnd_1010043 518637540709296935817403 := by
  unfold tailWord_1010043
  simp only [CollatzResearch.WordTrace]
  refine ⟨36839294679794187455954783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24559529786529458303969855 36839294679794187455954783)
  ·
    refine ⟨55258942019691281183932175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36839294679794187455954783 55258942019691281183932175)
    ·
      refine ⟨82888413029536921775898263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55258942019691281183932175 82888413029536921775898263)
      ·
        refine ⟨124332619544305382663847395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82888413029536921775898263 124332619544305382663847395)
        ·
          refine ⟨186498929316458073995771093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124332619544305382663847395 186498929316458073995771093)
          ·
            refine ⟨4371068655854486109275885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 186498929316458073995771093 4371068655854486109275885)
            ·
              refine ⟨1639150745945432290978457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4371068655854486109275885 1639150745945432290978457)
              ·
                refine ⟨1229363059459074218233843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639150745945432290978457 1229363059459074218233843)
                ·
                  refine ⟨1844044589188611327350765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229363059459074218233843 1844044589188611327350765)
                  ·
                    refine ⟨691516720945729247756537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844044589188611327350765 691516720945729247756537)
                    ·
                      refine ⟨518637540709296935817403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691516720945729247756537 518637540709296935817403)
                      ·
                        rfl

theorem cell23_1010043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 3, 2].length) (baseStart_1010043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010043 prefixEnd_1010043 := by exact prefixLift 1010043
  have htrace : WordTrace (prefixWord ++ tailWord_1010043) baseStart_1010043 baseEnd_1010043 := by
    simpa [prefixWord, tailWord_1010043, baseEnd_1010043] using wordTrace_append hprefix tailTrace_1010043
  have hstable : (prefixWord ++ tailWord_1010043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010043).length < 2 ^ (prefixWord ++ tailWord_1010043).sum := by decide
  have hdescent : baseEnd_1010043 < baseStart_1010043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010050 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1010050 : Nat := 118140960795 + 1010050 * 2 ^ 59
def prefixEnd_1010050 : Nat := 4983230072969 + 3 ^ 40 * 1010050 * 2
def baseEnd_1010050 : Nat := 518641135073878408429871

theorem tailTrace_1010050 : CollatzResearch.WordTrace tailWord_1010050 prefixEnd_1010050 518641135073878408429871 := by
  unfold tailWord_1010050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9209887497692206912864901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24559699993845885100973069 9209887497692206912864901)
  ·
    refine ⟨1726853905817288796162169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9209887497692206912864901 1726853905817288796162169)
    ·
      refine ⟨1295140429362966597121627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1726853905817288796162169 1295140429362966597121627)
      ·
        refine ⟨1942710644044449895682441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295140429362966597121627 1942710644044449895682441)
        ·
          refine ⟨1457032983033337421761831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1942710644044449895682441 1457032983033337421761831)
          ·
            refine ⟨2185549474550006132642747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457032983033337421761831 2185549474550006132642747)
            ·
              refine ⟨3278324211825009198964121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185549474550006132642747 3278324211825009198964121)
              ·
                refine ⟨2458743158868756899223091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278324211825009198964121 2458743158868756899223091)
                ·
                  refine ⟨3688114738303135348834637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458743158868756899223091 3688114738303135348834637)
                  ·
                    refine ⟨1383043026863675755812989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3688114738303135348834637 1383043026863675755812989)
                    ·
                      refine ⟨518641135073878408429871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1383043026863675755812989 518641135073878408429871)
                      ·
                        rfl

theorem cell23_1010050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1010050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010050 prefixEnd_1010050 := by exact prefixLift 1010050
  have htrace : WordTrace (prefixWord ++ tailWord_1010050) baseStart_1010050 baseEnd_1010050 := by
    simpa [prefixWord, tailWord_1010050, baseEnd_1010050] using wordTrace_append hprefix tailTrace_1010050
  have hstable : (prefixWord ++ tailWord_1010050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010050).length < 2 ^ (prefixWord ++ tailWord_1010050).sum := by decide
  have hdescent : baseEnd_1010050 < baseStart_1010050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010059 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 5]
def baseStart_1010059 : Nat := 118140960795 + 1010059 * 2 ^ 59
def prefixEnd_1010059 : Nat := 4983230072969 + 3 ^ 40 * 1010059 * 2
def baseEnd_1010059 : Nat := 518645756399768873217329

theorem tailTrace_1010059 : CollatzResearch.WordTrace tailWord_1010059 prefixEnd_1010059 518645756399768873217329 := by
  unfold tailWord_1010059
  simp only [CollatzResearch.WordTrace]
  refine ⟨36839878247736222188537231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24559918831824148125691487 36839878247736222188537231)
  ·
    refine ⟨55259817371604333282805847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36839878247736222188537231 55259817371604333282805847)
    ·
      refine ⟨82889726057406499924208771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55259817371604333282805847 82889726057406499924208771)
      ·
        refine ⟨124334589086109749886313157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82889726057406499924208771 124334589086109749886313157)
        ·
          refine ⟨23312735453645578103683717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124334589086109749886313157 23312735453645578103683717)
          ·
            refine ⟨4371137897558545894440697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23312735453645578103683717 4371137897558545894440697)
            ·
              refine ⟨3278353423168909420830523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371137897558545894440697 3278353423168909420830523)
              ·
                refine ⟨4917530134753364131245785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3278353423168909420830523 4917530134753364131245785)
                ·
                  refine ⟨3688147601065023098434339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4917530134753364131245785 3688147601065023098434339)
                  ·
                    refine ⟨5532221401597534647651509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3688147601065023098434339 5532221401597534647651509)
                    ·
                      refine ⟨518645756399768873217329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5532221401597534647651509 518645756399768873217329)
                      ·
                        rfl

theorem cell23_1010059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_1010059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010059 prefixEnd_1010059 := by exact prefixLift 1010059
  have htrace : WordTrace (prefixWord ++ tailWord_1010059) baseStart_1010059 baseEnd_1010059 := by
    simpa [prefixWord, tailWord_1010059, baseEnd_1010059] using wordTrace_append hprefix tailTrace_1010059
  have hstable : (prefixWord ++ tailWord_1010059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010059).length < 2 ^ (prefixWord ++ tailWord_1010059).sum := by decide
  have hdescent : baseEnd_1010059 < baseStart_1010059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010060 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 1, 3, 2]
def baseStart_1010060 : Nat := 118140960795 + 1010060 * 2 ^ 59
def prefixEnd_1010060 : Nat := 4983230072969 + 3 ^ 40 * 1010060 * 2
def baseEnd_1010060 : Nat := 518646269880423369304825

theorem tailTrace_1010060 : CollatzResearch.WordTrace tailWord_1010060 prefixEnd_1010060 518646269880423369304825 := by
  unfold tailWord_1010060
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419957360366299679661817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24559943147155066239549089 18419957360366299679661817)
  ·
    refine ⟨13814968020274724759746363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18419957360366299679661817 13814968020274724759746363)
    ·
      refine ⟨20722452030412087139619545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13814968020274724759746363 20722452030412087139619545)
      ·
        refine ⟨15541839022809065354714659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20722452030412087139619545 15541839022809065354714659)
        ·
          refine ⟨23312758534213598032071989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15541839022809065354714659 23312758534213598032071989)
          ·
            refine ⟨2185571112582524815506749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23312758534213598032071989 2185571112582524815506749)
            ·
              refine ⟨819589167218446805815031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2185571112582524815506749 819589167218446805815031)
              ·
                refine ⟨1229383750827670208722547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819589167218446805815031 1229383750827670208722547)
                ·
                  refine ⟨1844075626241505313083821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229383750827670208722547 1844075626241505313083821)
                  ·
                    refine ⟨691528359840564492406433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844075626241505313083821 691528359840564492406433)
                    ·
                      refine ⟨518646269880423369304825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691528359840564492406433 518646269880423369304825)
                      ·
                        rfl

theorem cell23_1010060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_1010060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010060 prefixEnd_1010060 := by exact prefixLift 1010060
  have htrace : WordTrace (prefixWord ++ tailWord_1010060) baseStart_1010060 baseEnd_1010060 := by
    simpa [prefixWord, tailWord_1010060, baseEnd_1010060] using wordTrace_append hprefix tailTrace_1010060
  have hstable : (prefixWord ++ tailWord_1010060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010060).length < 2 ^ (prefixWord ++ tailWord_1010060).sum := by decide
  have hdescent : baseEnd_1010060 < baseStart_1010060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010069 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1010069 : Nat := 118140960795 + 1010069 * 2 ^ 59
def prefixEnd_1010069 : Nat := 4983230072969 + 3 ^ 40 * 1010069 * 2
def baseEnd_1010069 : Nat := 518650891206313834092283

theorem tailTrace_1010069 : CollatzResearch.WordTrace tailWord_1010069 prefixEnd_1010069 518650891206313834092283 := by
  unfold tailWord_1010069
  simp only [CollatzResearch.WordTrace]
  refine ⟨36840242977699993896401261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24560161985133329264267507 36840242977699993896401261)
  ·
    refine ⟨13815091116637497711150473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36840242977699993896401261 13815091116637497711150473)
    ·
      refine ⟨10361318337478123283362855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13815091116637497711150473 10361318337478123283362855)
      ·
        refine ⟨15541977506217184925044283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10361318337478123283362855 15541977506217184925044283)
        ·
          refine ⟨23312966259325777387566425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15541977506217184925044283 23312966259325777387566425)
          ·
            refine ⟨17484724694494333040674819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23312966259325777387566425 17484724694494333040674819)
            ·
              refine ⟨26227087041741499561012229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17484724694494333040674819 26227087041741499561012229)
              ·
                refine ⟨4917578820326531167689793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26227087041741499561012229 4917578820326531167689793)
                ·
                  refine ⟨3688184115244898375767345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4917578820326531167689793 3688184115244898375767345)
                  ·
                    refine ⟨2766138086433673781825509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3688184115244898375767345 2766138086433673781825509)
                    ·
                      refine ⟨518650891206313834092283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2766138086433673781825509 518650891206313834092283)
                      ·
                        rfl

theorem cell23_1010069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1010069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010069 prefixEnd_1010069 := by exact prefixLift 1010069
  have htrace : WordTrace (prefixWord ++ tailWord_1010069) baseStart_1010069 baseEnd_1010069 := by
    simpa [prefixWord, tailWord_1010069, baseEnd_1010069] using wordTrace_append hprefix tailTrace_1010069
  have hstable : (prefixWord ++ tailWord_1010069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010069).length < 2 ^ (prefixWord ++ tailWord_1010069).sum := by decide
  have hdescent : baseEnd_1010069 < baseStart_1010069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010079 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 7]
def baseStart_1010079 : Nat := 118140960795 + 1010079 * 2 ^ 59
def prefixEnd_1010079 : Nat := 4983230072969 + 3 ^ 40 * 1010079 * 2
def baseEnd_1010079 : Nat := 57628447334762088329693

theorem tailTrace_1010079 : CollatzResearch.WordTrace tailWord_1010079 prefixEnd_1010079 57628447334762088329693 := by
  unfold tailWord_1010079
  simp only [CollatzResearch.WordTrace]
  refine ⟨36840607707663765604265291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24560405138442510402843527 36840607707663765604265291)
  ·
    refine ⟨55260911561495648406397937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36840607707663765604265291 55260911561495648406397937)
    ·
      refine ⟨41445683671121736304798453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55260911561495648406397937 41445683671121736304798453)
      ·
        refine ⟨3885532844167662778574855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41445683671121736304798453 3885532844167662778574855)
        ·
          refine ⟨5828299266251494167862283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885532844167662778574855 5828299266251494167862283)
          ·
            refine ⟨8742448899377241251793425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828299266251494167862283 8742448899377241251793425)
            ·
              refine ⟨6556836674532930938845069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8742448899377241251793425 6556836674532930938845069)
              ·
                refine ⟨2458813752949849102066901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6556836674532930938845069 2458813752949849102066901)
                ·
                  refine ⟨57628447334762088329693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2458813752949849102066901 57628447334762088329693)
                  ·
                    rfl

theorem cell23_1010079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 7].length) (baseStart_1010079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010079 prefixEnd_1010079 := by exact prefixLift 1010079
  have htrace : WordTrace (prefixWord ++ tailWord_1010079) baseStart_1010079 baseEnd_1010079 := by
    simpa [prefixWord, tailWord_1010079, baseEnd_1010079] using wordTrace_append hprefix tailTrace_1010079
  have hstable : (prefixWord ++ tailWord_1010079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010079).length < 2 ^ (prefixWord ++ tailWord_1010079).sum := by decide
  have hdescent : baseEnd_1010079 < baseStart_1010079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010124 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1010124 : Nat := 118140960795 + 1010124 * 2 ^ 59
def prefixEnd_1010124 : Nat := 4983230072969 + 3 ^ 40 * 1010124 * 2
def baseEnd_1010124 : Nat := 518679132642311118904531

theorem tailTrace_1010124 : CollatzResearch.WordTrace tailWord_1010124 prefixEnd_1010124 518679132642311118904531 := by
  unfold tailWord_1010124
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421124496250369144826713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24561499328333825526435617 18421124496250369144826713)
  ·
    refine ⟨13815843372187776858620035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18421124496250369144826713 13815843372187776858620035)
    ·
      refine ⟨20723765058281665287930053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13815843372187776858620035 20723765058281665287930053)
      ·
        refine ⟨3885705948427812241486885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20723765058281665287930053 3885705948427812241486885)
        ·
          refine ⟨728569865330214795278791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3885705948427812241486885 728569865330214795278791)
          ·
            refine ⟨1092854797995322192918187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728569865330214795278791 1092854797995322192918187)
            ·
              refine ⟨1639282196992983289377281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092854797995322192918187 1639282196992983289377281)
              ·
                refine ⟨1229461647744737467032961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639282196992983289377281 1229461647744737467032961)
                ·
                  refine ⟨922096235808553100274721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229461647744737467032961 922096235808553100274721)
                  ·
                    refine ⟨691572176856414825206041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 922096235808553100274721 691572176856414825206041)
                    ·
                      refine ⟨518679132642311118904531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691572176856414825206041 518679132642311118904531)
                      ·
                        rfl

theorem cell23_1010124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1010124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010124 prefixEnd_1010124 := by exact prefixLift 1010124
  have htrace : WordTrace (prefixWord ++ tailWord_1010124) baseStart_1010124 baseEnd_1010124 := by
    simpa [prefixWord, tailWord_1010124, baseEnd_1010124] using wordTrace_append hprefix tailTrace_1010124
  have hstable : (prefixWord ++ tailWord_1010124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010124).length < 2 ^ (prefixWord ++ tailWord_1010124).sum := by decide
  have hdescent : baseEnd_1010124 < baseStart_1010124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010156 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_1010156 : Nat := 118140960795 + 1010156 * 2 ^ 59
def prefixEnd_1010156 : Nat := 4983230072969 + 3 ^ 40 * 1010156 * 2
def baseEnd_1010156 : Nat := 172898521341084997901461

theorem tailTrace_1010156 : CollatzResearch.WordTrace tailWord_1010156 prefixEnd_1010156 172898521341084997901461 := by
  unfold tailWord_1010156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421708064192403877409161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24562277418923205169878881 18421708064192403877409161)
  ·
    refine ⟨13816281048144302908056871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18421708064192403877409161 13816281048144302908056871)
    ·
      refine ⟨20724421572216454362085307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13816281048144302908056871 20724421572216454362085307)
      ·
        refine ⟨31086632358324681543127961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20724421572216454362085307 31086632358324681543127961)
        ·
          refine ⟨23314974268743511157345971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31086632358324681543127961 23314974268743511157345971)
          ·
            refine ⟨34972461403115266736018957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23314974268743511157345971 34972461403115266736018957)
            ·
              refine ⟨13114673026168225026007109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34972461403115266736018957 13114673026168225026007109)
              ·
                refine ⟨2459001192406542192376333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13114673026168225026007109 2459001192406542192376333)
                ·
                  refine ⟨922125447152453322141125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2459001192406542192376333 922125447152453322141125)
                  ·
                    refine ⟨172898521341084997901461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 922125447152453322141125 172898521341084997901461)
                    ·
                      rfl

theorem cell23_1010156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_1010156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010156 prefixEnd_1010156 := by exact prefixLift 1010156
  have htrace : WordTrace (prefixWord ++ tailWord_1010156) baseStart_1010156 baseEnd_1010156 := by
    simpa [prefixWord, tailWord_1010156, baseEnd_1010156] using wordTrace_append hprefix tailTrace_1010156
  have hstable : (prefixWord ++ tailWord_1010156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010156).length < 2 ^ (prefixWord ++ tailWord_1010156).sum := by decide
  have hdescent : baseEnd_1010156 < baseStart_1010156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010159 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_1010159 : Nat := 118140960795 + 1010159 * 2 ^ 59
def prefixEnd_1010159 : Nat := 4983230072969 + 3 ^ 40 * 1010159 * 2
def baseEnd_1010159 : Nat := 518697104465218481966869

theorem tailTrace_1010159 : CollatzResearch.WordTrace tailWord_1010159 prefixEnd_1010159 518697104465218481966869 := by
  unfold tailWord_1010159
  simp only [CollatzResearch.WordTrace]
  refine ⟨36843525547373939267177531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24562350364915959511451687 36843525547373939267177531)
  ·
    refine ⟨55265288321060908900766297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36843525547373939267177531 55265288321060908900766297)
    ·
      refine ⟨41448966240795681675574723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55265288321060908900766297 41448966240795681675574723)
      ·
        refine ⟨62173449361193522513362085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41448966240795681675574723 62173449361193522513362085)
        ·
          refine ⟨11657521755223785471255391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62173449361193522513362085 11657521755223785471255391)
          ·
            refine ⟨17486282632835678206883087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11657521755223785471255391 17486282632835678206883087)
            ·
              refine ⟨26229423949253517310324631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17486282632835678206883087 26229423949253517310324631)
              ·
                refine ⟨39344135923880275965486947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26229423949253517310324631 39344135923880275965486947)
                ·
                  refine ⟨59016203885820413948230421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39344135923880275965486947 59016203885820413948230421)
                  ·
                    refine ⟨2766384557147831903823301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59016203885820413948230421 2766384557147831903823301)
                    ·
                      refine ⟨518697104465218481966869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2766384557147831903823301 518697104465218481966869)
                      ·
                        rfl

theorem cell23_1010159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_1010159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010159 prefixEnd_1010159 := by exact prefixLift 1010159
  have htrace : WordTrace (prefixWord ++ tailWord_1010159) baseStart_1010159 baseEnd_1010159 := by
    simpa [prefixWord, tailWord_1010159, baseEnd_1010159] using wordTrace_append hprefix tailTrace_1010159
  have hstable : (prefixWord ++ tailWord_1010159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010159).length < 2 ^ (prefixWord ++ tailWord_1010159).sum := by decide
  have hdescent : baseEnd_1010159 < baseStart_1010159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010169 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 8]
def baseStart_1010169 : Nat := 118140960795 + 1010169 * 2 ^ 59
def prefixEnd_1010169 : Nat := 4983230072969 + 3 ^ 40 * 1010169 * 2
def baseEnd_1010169 : Nat := 57633582141307049204647

theorem tailTrace_1010169 : CollatzResearch.WordTrace tailWord_1010169 prefixEnd_1010169 57633582141307049204647 := by
  unfold tailWord_1010169
  simp only [CollatzResearch.WordTrace]
  refine ⟨36843890277337710975041561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24562593518225140650027707 36843890277337710975041561)
  ·
    refine ⟨27632917708003283231281171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36843890277337710975041561 27632917708003283231281171)
    ·
      refine ⟨41449376562004924846921757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27632917708003283231281171 41449376562004924846921757)
      ·
        refine ⟨15543516210751846817595659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41449376562004924846921757 15543516210751846817595659)
        ·
          refine ⟨23315274316127770226393489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15543516210751846817595659 23315274316127770226393489)
          ·
            refine ⟨17486455737095827669795117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23315274316127770226393489 17486455737095827669795117)
            ·
              refine ⟨6557420901410935376173169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17486455737095827669795117 6557420901410935376173169)
              ·
                refine ⟨4918065676058201532129877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6557420901410935376173169 4918065676058201532129877)
                ·
                  refine ⟨57633582141307049204647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4918065676058201532129877 57633582141307049204647)
                  ·
                    rfl

theorem cell23_1010169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 8].length) (baseStart_1010169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010169 prefixEnd_1010169 := by exact prefixLift 1010169
  have htrace : WordTrace (prefixWord ++ tailWord_1010169) baseStart_1010169 baseEnd_1010169 := by
    simpa [prefixWord, tailWord_1010169, baseEnd_1010169] using wordTrace_append hprefix tailTrace_1010169
  have hstable : (prefixWord ++ tailWord_1010169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010169).length < 2 ^ (prefixWord ++ tailWord_1010169).sum := by decide
  have hdescent : baseEnd_1010169 < baseStart_1010169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010186 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 6]
def baseStart_1010186 : Nat := 118140960795 + 1010186 * 2 ^ 59
def prefixEnd_1010186 : Nat := 4983230072969 + 3 ^ 40 * 1010186 * 2
def baseEnd_1010186 : Nat := 57634552049209986258805

theorem tailTrace_1010186 : CollatzResearch.WordTrace tailWord_1010186 prefixEnd_1010186 57634552049209986258805 := by
  unfold tailWord_1010186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9211127579569030719602603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24563006878850748585606941 9211127579569030719602603)
  ·
    refine ⟨13816691369353546079403905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9211127579569030719602603 13816691369353546079403905)
    ·
      refine ⟨10362518527015159559552929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13816691369353546079403905 10362518527015159559552929)
      ·
        refine ⟨7771888895261369669664697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10362518527015159559552929 7771888895261369669664697)
        ·
          refine ⟨5828916671446027252248523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7771888895261369669664697 5828916671446027252248523)
          ·
            refine ⟨8743375007169040878372785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828916671446027252248523 8743375007169040878372785)
            ·
              refine ⟨6557531255376780658779589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8743375007169040878372785 6557531255376780658779589)
              ·
                refine ⟨1229537110383146373521173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6557531255376780658779589 1229537110383146373521173)
                ·
                  refine ⟨57634552049209986258805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1229537110383146373521173 57634552049209986258805)
                  ·
                    rfl

theorem cell23_1010186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_1010186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010186 prefixEnd_1010186 := by exact prefixLift 1010186
  have htrace : WordTrace (prefixWord ++ tailWord_1010186) baseStart_1010186 baseEnd_1010186 := by
    simpa [prefixWord, tailWord_1010186, baseEnd_1010186] using wordTrace_append hprefix tailTrace_1010186
  have hstable : (prefixWord ++ tailWord_1010186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010186).length < 2 ^ (prefixWord ++ tailWord_1010186).sum := by decide
  have hdescent : baseEnd_1010186 < baseStart_1010186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010190 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_1010190 : Nat := 118140960795 + 1010190 * 2 ^ 59
def prefixEnd_1010190 : Nat := 4983230072969 + 3 ^ 40 * 1010190 * 2
def baseEnd_1010190 : Nat := 172904340788502620226409

theorem tailTrace_1010190 : CollatzResearch.WordTrace tailWord_1010190 prefixEnd_1010190 172904340788502620226409 := by
  unfold tailWord_1010190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605582026282703945194503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24563104140174421041037349 4605582026282703945194503)
  ·
    refine ⟨6908373039424055917791755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4605582026282703945194503 6908373039424055917791755)
    ·
      refine ⟨10362559559136083876687633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6908373039424055917791755 10362559559136083876687633)
      ·
        refine ⟨7771919669352062907515725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10362559559136083876687633 7771919669352062907515725)
        ·
          refine ⟨2914469876007023590318397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7771919669352062907515725 2914469876007023590318397)
          ·
            refine ⟨1092926203502633846369399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2914469876007023590318397 1092926203502633846369399)
            ·
              refine ⟨1639389305253950769554099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092926203502633846369399 1639389305253950769554099)
              ·
                refine ⟨2459083957880926154331149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639389305253950769554099 2459083957880926154331149)
                ·
                  refine ⟨922156484205347307874181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2459083957880926154331149 922156484205347307874181)
                  ·
                    refine ⟨172904340788502620226409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 922156484205347307874181 172904340788502620226409)
                    ·
                      rfl

theorem cell23_1010190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_1010190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010190 prefixEnd_1010190 := by exact prefixLift 1010190
  have htrace : WordTrace (prefixWord ++ tailWord_1010190) baseStart_1010190 baseEnd_1010190 := by
    simpa [prefixWord, tailWord_1010190, baseEnd_1010190] using wordTrace_append hprefix tailTrace_1010190
  have hstable : (prefixWord ++ tailWord_1010190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010190).length < 2 ^ (prefixWord ++ tailWord_1010190).sum := by decide
  have hdescent : baseEnd_1010190 < baseStart_1010190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010213 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_1010213 : Nat := 118140960795 + 1010213 * 2 ^ 59
def prefixEnd_1010213 : Nat := 4983230072969 + 3 ^ 40 * 1010213 * 2
def baseEnd_1010213 : Nat := 518724832420561270691621

theorem tailTrace_1010213 : CollatzResearch.WordTrace tailWord_1010213 prefixEnd_1010213 518724832420561270691621 := by
  unfold tailWord_1010213
  simp only [CollatzResearch.WordTrace]
  refine ⟨36845495089178306489643293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24563663392785537659762195 36845495089178306489643293)
  ·
    refine ⟨13817060658441864933616235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36845495089178306489643293 13817060658441864933616235)
    ·
      refine ⟨20725590987662797400424353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13817060658441864933616235 20725590987662797400424353)
      ·
        refine ⟨15544193240747098050318265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20725590987662797400424353 15544193240747098050318265)
        ·
          refine ⟨11658144930560323537738699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15544193240747098050318265 11658144930560323537738699)
          ·
            refine ⟨17487217395840485306608049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11658144930560323537738699 17487217395840485306608049)
            ·
              refine ⟨13115413046880363979956037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17487217395840485306608049 13115413046880363979956037)
              ·
                refine ⟨2459139946290068246241757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13115413046880363979956037 2459139946290068246241757)
                ·
                  refine ⟨922177479858775592340659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2459139946290068246241757 922177479858775592340659)
                  ·
                    refine ⟨1383266219788163388510989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 922177479858775592340659 1383266219788163388510989)
                    ·
                      refine ⟨518724832420561270691621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1383266219788163388510989 518724832420561270691621)
                      ·
                        rfl

theorem cell23_1010213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_1010213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010213 prefixEnd_1010213 := by exact prefixLift 1010213
  have htrace : WordTrace (prefixWord ++ tailWord_1010213) baseStart_1010213 baseEnd_1010213 := by
    simpa [prefixWord, tailWord_1010213, baseEnd_1010213] using wordTrace_append hprefix tailTrace_1010213
  have hstable : (prefixWord ++ tailWord_1010213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010213).length < 2 ^ (prefixWord ++ tailWord_1010213).sum := by decide
  have hdescent : baseEnd_1010213 < baseStart_1010213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010247 : List Nat := [1, 1, 4, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_1010247 : Nat := 118140960795 + 1010247 * 2 ^ 59
def prefixEnd_1010247 : Nat := 4983230072969 + 3 ^ 40 * 1010247 * 2
def baseEnd_1010247 : Nat := 518742290762814137666465

theorem tailTrace_1010247 : CollatzResearch.WordTrace tailWord_1010247 prefixEnd_1010247 518742290762814137666465 := by
  unfold tailWord_1010247
  simp only [CollatzResearch.WordTrace]
  refine ⟨36846735171055130296380995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24564490114036753530920663 36846735171055130296380995)
  ·
    refine ⟨55270102756582695444571493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36846735171055130296380995 55270102756582695444571493)
    ·
      refine ⟨10363144266859255395857155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55270102756582695444571493 10363144266859255395857155)
      ·
        refine ⟨15544716400288883093785733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10363144266859255395857155 15544716400288883093785733)
        ·
          refine ⟨2914634325054165580084825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15544716400288883093785733 2914634325054165580084825)
          ·
            refine ⟨2185975743790624185063619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914634325054165580084825 2185975743790624185063619)
            ·
              refine ⟨3278963615685936277595429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185975743790624185063619 3278963615685936277595429)
              ·
                refine ⟨614805677941113052049143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3278963615685936277595429 614805677941113052049143)
                ·
                  refine ⟨922208516911669578073715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614805677941113052049143 922208516911669578073715)
                  ·
                    refine ⟨1383312775367504367110573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 922208516911669578073715 1383312775367504367110573)
                    ·
                      refine ⟨518742290762814137666465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1383312775367504367110573 518742290762814137666465)
                      ·
                        rfl

theorem cell23_1010247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_1010247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010247 prefixEnd_1010247 := by exact prefixLift 1010247
  have htrace : WordTrace (prefixWord ++ tailWord_1010247) baseStart_1010247 baseEnd_1010247 := by
    simpa [prefixWord, tailWord_1010247, baseEnd_1010247] using wordTrace_append hprefix tailTrace_1010247
  have hstable : (prefixWord ++ tailWord_1010247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010247).length < 2 ^ (prefixWord ++ tailWord_1010247).sum := by decide
  have hdescent : baseEnd_1010247 < baseStart_1010247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010263 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 2, 4]
def baseStart_1010263 : Nat := 118140960795 + 1010263 * 2 ^ 59
def prefixEnd_1010263 : Nat := 4983230072969 + 3 ^ 40 * 1010263 * 2
def baseEnd_1010263 : Nat := 172916835484428691688797

theorem tailTrace_1010263 : CollatzResearch.WordTrace tailWord_1010263 prefixEnd_1010263 172916835484428691688797 := by
  unfold tailWord_1010263
  simp only [CollatzResearch.WordTrace]
  refine ⟨36847318738997165028963443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24564879159331443352642295 36847318738997165028963443)
  ·
    refine ⟨55270978108495747543445165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36847318738997165028963443 55270978108495747543445165)
    ·
      refine ⟨20726616790685905328791937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55270978108495747543445165 20726616790685905328791937)
      ·
        refine ⟨15544962593014428996593953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20726616790685905328791937 15544962593014428996593953)
        ·
          refine ⟨11658721944760821747445465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15544962593014428996593953 11658721944760821747445465)
          ·
            refine ⟨8744041458570616310584099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11658721944760821747445465 8744041458570616310584099)
            ·
              refine ⟨13116062187855924465876149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744041458570616310584099 13116062187855924465876149)
              ·
                refine ⟨1229630830111492918675889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13116062187855924465876149 1229630830111492918675889)
                ·
                  refine ⟨922223122583619689006917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229630830111492918675889 922223122583619689006917)
                  ·
                    refine ⟨172916835484428691688797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 922223122583619689006917 172916835484428691688797)
                    ·
                      rfl

theorem cell23_1010263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_1010263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010263 prefixEnd_1010263 := by exact prefixLift 1010263
  have htrace : WordTrace (prefixWord ++ tailWord_1010263) baseStart_1010263 baseEnd_1010263 := by
    simpa [prefixWord, tailWord_1010263, baseEnd_1010263] using wordTrace_append hprefix tailTrace_1010263
  have hstable : (prefixWord ++ tailWord_1010263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010263).length < 2 ^ (prefixWord ++ tailWord_1010263).sum := by decide
  have hdescent : baseEnd_1010263 < baseStart_1010263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010273 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_1010273 : Nat := 118140960795 + 1010273 * 2 ^ 59
def prefixEnd_1010273 : Nat := 4983230072969 + 3 ^ 40 * 1010273 * 2
def baseEnd_1010273 : Nat := 518755641259831035941345

theorem tailTrace_1010273 : CollatzResearch.WordTrace tailWord_1010273 prefixEnd_1010273 518755641259831035941345 := by
  unfold tailWord_1010273
  simp only [CollatzResearch.WordTrace]
  refine ⟨36847683468960936736827473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24565122312640624491218315 36847683468960936736827473)
  ·
    refine ⟨27635762601720702552620605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36847683468960936736827473 27635762601720702552620605)
    ·
      refine ⟨10363410975645263457232727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27635762601720702552620605 10363410975645263457232727)
      ·
        refine ⟨15545116463467895185849091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10363410975645263457232727 15545116463467895185849091)
        ·
          refine ⟨23317674695201842778773637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15545116463467895185849091 23317674695201842778773637)
          ·
            refine ⟨4372064005350345521020057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23317674695201842778773637 4372064005350345521020057)
            ·
              refine ⟨3279048004012759140765043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4372064005350345521020057 3279048004012759140765043)
              ·
                refine ⟨4918572006019138711147565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279048004012759140765043 4918572006019138711147565)
                ·
                  refine ⟨1844464502257177016680337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4918572006019138711147565 1844464502257177016680337)
                  ·
                    refine ⟨1383348376692882762510253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1844464502257177016680337 1383348376692882762510253)
                    ·
                      refine ⟨518755641259831035941345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1383348376692882762510253 518755641259831035941345)
                      ·
                        rfl

theorem cell23_1010273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_1010273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010273 prefixEnd_1010273 := by exact prefixLift 1010273
  have htrace : WordTrace (prefixWord ++ tailWord_1010273) baseStart_1010273 baseEnd_1010273 := by
    simpa [prefixWord, tailWord_1010273, baseEnd_1010273] using wordTrace_append hprefix tailTrace_1010273
  have hstable : (prefixWord ++ tailWord_1010273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010273).length < 2 ^ (prefixWord ++ tailWord_1010273).sum := by decide
  have hdescent : baseEnd_1010273 < baseStart_1010273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010287 : List Nat := [1, 1, 2, 1, 3, 2, 3, 5, 1, 2, 2]
def baseStart_1010287 : Nat := 118140960795 + 1010287 * 2 ^ 59
def prefixEnd_1010287 : Nat := 4983230072969 + 3 ^ 40 * 1010287 * 2
def baseEnd_1010287 : Nat := 518762829988993981166281

theorem tailTrace_1010287 : CollatzResearch.WordTrace tailWord_1010287 prefixEnd_1010287 518762829988993981166281 := by
  unfold tailWord_1010287
  simp only [CollatzResearch.WordTrace]
  refine ⟨36848194090910217127837115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24565462727273478085224743 36848194090910217127837115)
  ·
    refine ⟨55272291136365325691755673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36848194090910217127837115 55272291136365325691755673)
    ·
      refine ⟨41454218352273994268816755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55272291136365325691755673 41454218352273994268816755)
      ·
        refine ⟨62181327528410991403225133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41454218352273994268816755 62181327528410991403225133)
        ·
          refine ⟨23317997823154121776209425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62181327528410991403225133 23317997823154121776209425)
          ·
            refine ⟨17488498367365591332157069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23317997823154121776209425 17488498367365591332157069)
            ·
              refine ⟨6558186887762096749558901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17488498367365591332157069 6558186887762096749558901)
              ·
                refine ⟨614830020727696570271147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6558186887762096749558901 614830020727696570271147)
                ·
                  refine ⟨922245031091544855406721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614830020727696570271147 922245031091544855406721)
                  ·
                    refine ⟨691683773318658641555041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 922245031091544855406721 691683773318658641555041)
                    ·
                      refine ⟨518762829988993981166281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691683773318658641555041 518762829988993981166281)
                      ·
                        rfl

theorem cell23_1010287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 1, 2, 2].length) (baseStart_1010287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010287 prefixEnd_1010287 := by exact prefixLift 1010287
  have htrace : WordTrace (prefixWord ++ tailWord_1010287) baseStart_1010287 baseEnd_1010287 := by
    simpa [prefixWord, tailWord_1010287, baseEnd_1010287] using wordTrace_append hprefix tailTrace_1010287
  have hstable : (prefixWord ++ tailWord_1010287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010287).length < 2 ^ (prefixWord ++ tailWord_1010287).sum := by decide
  have hdescent : baseEnd_1010287 < baseStart_1010287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010293 : List Nat := [1, 3, 4, 2, 2, 1, 10]
def baseStart_1010293 : Nat := 118140960795 + 1010293 * 2 ^ 59
def prefixEnd_1010293 : Nat := 4983230072969 + 3 ^ 40 * 1010293 * 2
def baseEnd_1010293 : Nat := 6404517418184209354213

theorem tailTrace_1010293 : CollatzResearch.WordTrace tailWord_1010293 prefixEnd_1010293 6404517418184209354213 := by
  unfold tailWord_1010293
  simp only [CollatzResearch.WordTrace]
  refine ⟨36848412928888480152555533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24565608619258986768370355 36848412928888480152555533)
  ·
    refine ⟨13818154848333180057208325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36848412928888480152555533 13818154848333180057208325)
    ·
      refine ⟨2590904034062471260726561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13818154848333180057208325 2590904034062471260726561)
      ·
        refine ⟨1943178025546853445544921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2590904034062471260726561 1943178025546853445544921)
        ·
          refine ⟨1457383519160140084158691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1943178025546853445544921 1457383519160140084158691)
          ·
            refine ⟨2186075278740210126238037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457383519160140084158691 2186075278740210126238037)
            ·
              refine ⟨6404517418184209354213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2186075278740210126238037 6404517418184209354213)
              ·
                rfl

theorem cell23_1010293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 10].length) (baseStart_1010293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010293 prefixEnd_1010293 := by exact prefixLift 1010293
  have htrace : WordTrace (prefixWord ++ tailWord_1010293) baseStart_1010293 baseEnd_1010293 := by
    simpa [prefixWord, tailWord_1010293, baseEnd_1010293] using wordTrace_append hprefix tailTrace_1010293
  have hstable : (prefixWord ++ tailWord_1010293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010293).length < 2 ^ (prefixWord ++ tailWord_1010293).sum := by decide
  have hdescent : baseEnd_1010293 < baseStart_1010293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010433 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1010433 : Nat := 118140960795 + 1010433 * 2 ^ 59
def prefixEnd_1010433 : Nat := 4983230072969 + 3 ^ 40 * 1010433 * 2
def baseEnd_1010433 : Nat := 518837798164550409940609

theorem tailTrace_1010433 : CollatzResearch.WordTrace tailWord_1010433 prefixEnd_1010433 518837798164550409940609 := by
  unfold tailWord_1010433
  simp only [CollatzResearch.WordTrace]
  refine ⟨36853519148381284062651953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24569012765587522708434635 36853519148381284062651953)
  ·
    refine ⟨27640139361285963046988965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36853519148381284062651953 27640139361285963046988965)
    ·
      refine ⟨5182526130241118071310431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27640139361285963046988965 5182526130241118071310431)
      ·
        refine ⟨7773789195361677106965647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182526130241118071310431 7773789195361677106965647)
        ·
          refine ⟨11660683793042515660448471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773789195361677106965647 11660683793042515660448471)
          ·
            refine ⟨17491025689563773490672707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660683793042515660448471 17491025689563773490672707)
            ·
              refine ⟨26236538534345660236009061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17491025689563773490672707 26236538534345660236009061)
              ·
                refine ⟨4919350975189811294251699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26236538534345660236009061 4919350975189811294251699)
                ·
                  refine ⟨7379026462784716941377549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919350975189811294251699 7379026462784716941377549)
                  ·
                    refine ⟨2767134923544268853016581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7379026462784716941377549 2767134923544268853016581)
                    ·
                      refine ⟨518837798164550409940609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2767134923544268853016581 518837798164550409940609)
                      ·
                        rfl

theorem cell23_1010433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1010433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010433 prefixEnd_1010433 := by exact prefixLift 1010433
  have htrace : WordTrace (prefixWord ++ tailWord_1010433) baseStart_1010433 baseEnd_1010433 := by
    simpa [prefixWord, tailWord_1010433, baseEnd_1010433] using wordTrace_append hprefix tailTrace_1010433
  have hstable : (prefixWord ++ tailWord_1010433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010433).length < 2 ^ (prefixWord ++ tailWord_1010433).sum := by decide
  have hdescent : baseEnd_1010433 < baseStart_1010433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010463 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1010463 : Nat := 118140960795 + 1010463 * 2 ^ 59
def prefixEnd_1010463 : Nat := 4983230072969 + 3 ^ 40 * 1010463 * 2
def baseEnd_1010463 : Nat := 518853202584185292565471

theorem tailTrace_1010463 : CollatzResearch.WordTrace tailWord_1010463 prefixEnd_1010463 518853202584185292565471 := by
  unfold tailWord_1010463
  simp only [CollatzResearch.WordTrace]
  refine ⟨36854613338272599186244043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24569742225515066124162695 36854613338272599186244043)
  ·
    refine ⟨55281920007408898779366065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36854613338272599186244043 55281920007408898779366065)
    ·
      refine ⟨41461440005556674084524549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55281920007408898779366065 41461440005556674084524549)
      ·
        refine ⟨7774020001041876390848353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41461440005556674084524549 7774020001041876390848353)
        ·
          refine ⟨5830515000781407293136265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7774020001041876390848353 5830515000781407293136265)
          ·
            refine ⟨4372886250586055469852199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5830515000781407293136265 4372886250586055469852199)
            ·
              refine ⟨6559329375879083204778299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372886250586055469852199 6559329375879083204778299)
              ·
                refine ⟨9838994063818624807167449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559329375879083204778299 9838994063818624807167449)
                ·
                  refine ⟨7379245547863968605375587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9838994063818624807167449 7379245547863968605375587)
                  ·
                    refine ⟨11068868321795952908063381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7379245547863968605375587 11068868321795952908063381)
                    ·
                      refine ⟨518853202584185292565471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11068868321795952908063381 518853202584185292565471)
                      ·
                        rfl

theorem cell23_1010463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1010463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010463 prefixEnd_1010463 := by exact prefixLift 1010463
  have htrace : WordTrace (prefixWord ++ tailWord_1010463) baseStart_1010463 baseEnd_1010463 := by
    simpa [prefixWord, tailWord_1010463, baseEnd_1010463] using wordTrace_append hprefix tailTrace_1010463
  have hstable : (prefixWord ++ tailWord_1010463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010463).length < 2 ^ (prefixWord ++ tailWord_1010463).sum := by decide
  have hdescent : baseEnd_1010463 < baseStart_1010463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010527 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 2, 3, 2]
def baseStart_1010527 : Nat := 118140960795 + 1010527 * 2 ^ 59
def prefixEnd_1010527 : Nat := 4983230072969 + 3 ^ 40 * 1010527 * 2
def baseEnd_1010527 : Nat := 518886065346073042165177

theorem tailTrace_1010527 : CollatzResearch.WordTrace tailWord_1010527 prefixEnd_1010527 518886065346073042165177 := by
  unfold tailWord_1010527
  simp only [CollatzResearch.WordTrace]
  refine ⟨36856947610040738116573835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24571298406693825411049223 36856947610040738116573835)
  ·
    refine ⟨55285421415061107174860753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36856947610040738116573835 55285421415061107174860753)
    ·
      refine ⟨41464066061295830381145565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55285421415061107174860753 41464066061295830381145565)
      ·
        refine ⟨15549024772985936392929587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41464066061295830381145565 15549024772985936392929587)
        ·
          refine ⟨23323537159478904589394381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15549024772985936392929587 23323537159478904589394381)
          ·
            refine ⟨8746326434804589221022893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23323537159478904589394381 8746326434804589221022893)
            ·
              refine ⟨3279872413051720957883585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8746326434804589221022893 3279872413051720957883585)
              ·
                refine ⟨2459904309788790718412689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3279872413051720957883585 2459904309788790718412689)
                ·
                  refine ⟨1844928232341593038809517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2459904309788790718412689 1844928232341593038809517)
                  ·
                    refine ⟨691848087128097389553569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844928232341593038809517 691848087128097389553569)
                    ·
                      refine ⟨518886065346073042165177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691848087128097389553569 518886065346073042165177)
                      ·
                        rfl

theorem cell23_1010527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_1010527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010527 prefixEnd_1010527 := by exact prefixLift 1010527
  have htrace : WordTrace (prefixWord ++ tailWord_1010527) baseStart_1010527 baseEnd_1010527 := by
    simpa [prefixWord, tailWord_1010527, baseEnd_1010527] using wordTrace_append hprefix tailTrace_1010527
  have hstable : (prefixWord ++ tailWord_1010527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010527).length < 2 ^ (prefixWord ++ tailWord_1010527).sum := by decide
  have hdescent : baseEnd_1010527 < baseStart_1010527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010540 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_1010540 : Nat := 118140960795 + 1010540 * 2 ^ 59
def prefixEnd_1010540 : Nat := 4983230072969 + 3 ^ 40 * 1010540 * 2
def baseEnd_1010540 : Nat := 518892740594581491302617

theorem tailTrace_1010540 : CollatzResearch.WordTrace tailWord_1010540 prefixEnd_1010540 518892740594581491302617 := by
  unfold tailWord_1010540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18428710879496820668398537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24571614505995760891198049 18428710879496820668398537)
  ·
    refine ⟨13821533159622615501298903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18428710879496820668398537 13821533159622615501298903)
    ·
      refine ⟨20732299739433923251948355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13821533159622615501298903 20732299739433923251948355)
      ·
        refine ⟨31098449609150884877922533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20732299739433923251948355 31098449609150884877922533)
        ·
          refine ⟨5830959301715790914610475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31098449609150884877922533 5830959301715790914610475)
          ·
            refine ⟨8746438952573686371915713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830959301715790914610475 8746438952573686371915713)
            ·
              refine ⟨6559829214430264778936785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8746438952573686371915713 6559829214430264778936785)
              ·
                refine ⟨4919871910822698584202589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6559829214430264778936785 4919871910822698584202589)
                ·
                  refine ⟨1844951966558511969075971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4919871910822698584202589 1844951966558511969075971)
                  ·
                    refine ⟨2767427949837767953613957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1844951966558511969075971 2767427949837767953613957)
                    ·
                      refine ⟨518892740594581491302617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2767427949837767953613957 518892740594581491302617)
                      ·
                        rfl

theorem cell23_1010540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_1010540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010540 prefixEnd_1010540 := by exact prefixLift 1010540
  have htrace : WordTrace (prefixWord ++ tailWord_1010540) baseStart_1010540 baseEnd_1010540 := by
    simpa [prefixWord, tailWord_1010540, baseEnd_1010540] using wordTrace_append hprefix tailTrace_1010540
  have hstable : (prefixWord ++ tailWord_1010540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010540).length < 2 ^ (prefixWord ++ tailWord_1010540).sum := by decide
  have hdescent : baseEnd_1010540 < baseStart_1010540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010557 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_1010557 : Nat := 118140960795 + 1010557 * 2 ^ 59
def prefixEnd_1010557 : Nat := 4983230072969 + 3 ^ 40 * 1010557 * 2
def baseEnd_1010557 : Nat := 518901469765707924790039

theorem tailTrace_1010557 : CollatzResearch.WordTrace tailWord_1010557 prefixEnd_1010557 518901469765707924790039 := by
  unfold tailWord_1010557
  simp only [CollatzResearch.WordTrace]
  refine ⟨36858041799932053240165925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24572027866621368826777283 36858041799932053240165925)
  ·
    refine ⟨6910882837487259982531111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36858041799932053240165925 6910882837487259982531111)
    ·
      refine ⟨10366324256230889973796667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6910882837487259982531111 10366324256230889973796667)
      ·
        refine ⟨15549486384346334960695001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10366324256230889973796667 15549486384346334960695001)
        ·
          refine ⟨11662114788259751220521251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15549486384346334960695001 11662114788259751220521251)
          ·
            refine ⟨17493172182389626830781877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11662114788259751220521251 17493172182389626830781877)
            ·
              refine ⟨1639984892099027515385801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17493172182389626830781877 1639984892099027515385801)
              ·
                refine ⟨1229988669074270636539351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639984892099027515385801 1229988669074270636539351)
                ·
                  refine ⟨1844983003611405954809027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229988669074270636539351 1844983003611405954809027)
                  ·
                    refine ⟨2767474505417108932213541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1844983003611405954809027 2767474505417108932213541)
                    ·
                      refine ⟨518901469765707924790039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2767474505417108932213541 518901469765707924790039)
                      ·
                        rfl

theorem cell23_1010557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_1010557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010557 prefixEnd_1010557 := by exact prefixLift 1010557
  have htrace : WordTrace (prefixWord ++ tailWord_1010557) baseStart_1010557 baseEnd_1010557 := by
    simpa [prefixWord, tailWord_1010557, baseEnd_1010557] using wordTrace_append hprefix tailTrace_1010557
  have hstable : (prefixWord ++ tailWord_1010557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010557).length < 2 ^ (prefixWord ++ tailWord_1010557).sum := by decide
  have hdescent : baseEnd_1010557 < baseStart_1010557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010563 : List Nat := [1, 1, 1, 3, 4, 1, 1, 11]
def baseStart_1010563 : Nat := 118140960795 + 1010563 * 2 ^ 59
def prefixEnd_1010563 : Nat := 4983230072969 + 3 ^ 40 * 1010563 * 2
def baseEnd_1010563 : Nat := 19218687061097588937593

theorem tailTrace_1010563 : CollatzResearch.WordTrace tailWord_1010563 prefixEnd_1010563 19218687061097588937593 := by
  unfold tailWord_1010563
  simp only [CollatzResearch.WordTrace]
  refine ⟨36858260637910316264884343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24572173758606877509922895 36858260637910316264884343)
  ·
    refine ⟨55287390956865474397326515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36858260637910316264884343 55287390956865474397326515)
    ·
      refine ⟨82931086435298211595989773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55287390956865474397326515 82931086435298211595989773)
      ·
        refine ⟨31099157413236829348496165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82931086435298211595989773 31099157413236829348496165)
        ·
          refine ⟨5831092014981905502843031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31099157413236829348496165 5831092014981905502843031)
          ·
            refine ⟨8746638022472858254264547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831092014981905502843031 8746638022472858254264547)
            ·
              refine ⟨13119957033709287381396821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746638022472858254264547 13119957033709287381396821)
              ·
                refine ⟨19218687061097588937593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 13119957033709287381396821 19218687061097588937593)
                ·
                  rfl

theorem cell23_1010563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 11].length) (baseStart_1010563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010563 prefixEnd_1010563 := by exact prefixLift 1010563
  have htrace : WordTrace (prefixWord ++ tailWord_1010563) baseStart_1010563 baseEnd_1010563 := by
    simpa [prefixWord, tailWord_1010563, baseEnd_1010563] using wordTrace_append hprefix tailTrace_1010563
  have hstable : (prefixWord ++ tailWord_1010563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010563).length < 2 ^ (prefixWord ++ tailWord_1010563).sum := by decide
  have hdescent : baseEnd_1010563 < baseStart_1010563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010660 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1010660 : Nat := 118140960795 + 1010660 * 2 ^ 59
def prefixEnd_1010660 : Nat := 4983230072969 + 3 ^ 40 * 1010660 * 2
def baseEnd_1010660 : Nat := 518954358273121021802065

theorem tailTrace_1010660 : CollatzResearch.WordTrace tailWord_1010660 prefixEnd_1010660 518954358273121021802065 := by
  unfold tailWord_1010660
  simp only [CollatzResearch.WordTrace]
  refine ⟨18430899259279450915582717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24574532345705934554110289 18430899259279450915582717)
  ·
    refine ⟨6911587222229794093343519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18430899259279450915582717 6911587222229794093343519)
    ·
      refine ⟨10367380833344691140015279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6911587222229794093343519 10367380833344691140015279)
      ·
        refine ⟨15551071250017036710022919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10367380833344691140015279 15551071250017036710022919)
        ·
          refine ⟨23326606875025555065034379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15551071250017036710022919 23326606875025555065034379)
          ·
            refine ⟨34989910312538332597551569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23326606875025555065034379 34989910312538332597551569)
            ·
              refine ⟨26242432734403749448163677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34989910312538332597551569 26242432734403749448163677)
              ·
                refine ⟨9840912275401406043061379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26242432734403749448163677 9840912275401406043061379)
                ·
                  refine ⟨14761368413102109064592069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9840912275401406043061379 14761368413102109064592069)
                  ·
                    refine ⟨2767756577456645449611013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14761368413102109064592069 2767756577456645449611013)
                    ·
                      refine ⟨518954358273121021802065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2767756577456645449611013 518954358273121021802065)
                      ·
                        rfl

theorem cell23_1010660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1010660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010660 prefixEnd_1010660 := by exact prefixLift 1010660
  have htrace : WordTrace (prefixWord ++ tailWord_1010660) baseStart_1010660 baseEnd_1010660 := by
    simpa [prefixWord, tailWord_1010660, baseEnd_1010660] using wordTrace_append hprefix tailTrace_1010660
  have hstable : (prefixWord ++ tailWord_1010660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010660).length < 2 ^ (prefixWord ++ tailWord_1010660).sum := by decide
  have hdescent : baseEnd_1010660 < baseStart_1010660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010664 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_1010664 : Nat := 118140960795 + 1010664 * 2 ^ 59
def prefixEnd_1010664 : Nat := 4983230072969 + 3 ^ 40 * 1010664 * 2
def baseEnd_1010664 : Nat := 518956412195739006152047

theorem tailTrace_1010664 : CollatzResearch.WordTrace tailWord_1010664 prefixEnd_1010664 518956412195739006152047 := by
  unfold tailWord_1010664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18430972205272205257155523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24574629607029607009540697 18430972205272205257155523)
  ·
    refine ⟨27646458307908307885733285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18430972205272205257155523 27646458307908307885733285)
    ·
      refine ⟨5183710932732807728574991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27646458307908307885733285 5183710932732807728574991)
      ·
        refine ⟨7775566399099211592862487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183710932732807728574991 7775566399099211592862487)
        ·
          refine ⟨11663349598648817389293731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775566399099211592862487 11663349598648817389293731)
          ·
            refine ⟨17495024397973226083940597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11663349598648817389293731 17495024397973226083940597)
            ·
              refine ⟨1640158537309989945369431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17495024397973226083940597 1640158537309989945369431)
              ·
                refine ⟨2460237805964984918054147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640158537309989945369431 2460237805964984918054147)
                ·
                  refine ⟨3690356708947477377081221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460237805964984918054147 3690356708947477377081221)
                  ·
                    refine ⟨691941882927652008202729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3690356708947477377081221 691941882927652008202729)
                    ·
                      refine ⟨518956412195739006152047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691941882927652008202729 518956412195739006152047)
                      ·
                        rfl

theorem cell23_1010664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_1010664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010664 prefixEnd_1010664 := by exact prefixLift 1010664
  have htrace : WordTrace (prefixWord ++ tailWord_1010664) baseStart_1010664 baseEnd_1010664 := by
    simpa [prefixWord, tailWord_1010664, baseEnd_1010664] using wordTrace_append hprefix tailTrace_1010664
  have hstable : (prefixWord ++ tailWord_1010664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010664).length < 2 ^ (prefixWord ++ tailWord_1010664).sum := by decide
  have hdescent : baseEnd_1010664 < baseStart_1010664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010676 : List Nat := [2, 6, 2, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1010676 : Nat := 118140960795 + 1010676 * 2 ^ 59
def prefixEnd_1010676 : Nat := 4983230072969 + 3 ^ 40 * 1010676 * 2
def baseEnd_1010676 : Nat := 518962573963592959201993

theorem tailTrace_1010676 : CollatzResearch.WordTrace tailWord_1010676 prefixEnd_1010676 518962573963592959201993 := by
  unfold tailWord_1010676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18431191043250468281873941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24574921391000624375831921 18431191043250468281873941)
  ·
    refine ⟨863962080152365700712841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18431191043250468281873941 863962080152365700712841)
    ·
      refine ⟨647971560114274275534631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 863962080152365700712841 647971560114274275534631)
      ·
        refine ⟨971957340171411413301947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647971560114274275534631 971957340171411413301947)
        ·
          refine ⟨1457936010257117119952921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971957340171411413301947 1457936010257117119952921)
          ·
            refine ⟨1093452007692837839964691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457936010257117119952921 1093452007692837839964691)
            ·
              refine ⟨1640178011539256759947037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093452007692837839964691 1640178011539256759947037)
              ·
                refine ⟨615066754327221284980139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1640178011539256759947037 615066754327221284980139)
                ·
                  refine ⟨922600131490831927470209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615066754327221284980139 922600131490831927470209)
                  ·
                    refine ⟨691950098618123945602657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 922600131490831927470209 691950098618123945602657)
                    ·
                      refine ⟨518962573963592959201993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691950098618123945602657 518962573963592959201993)
                      ·
                        rfl

theorem cell23_1010676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1010676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010676 prefixEnd_1010676 := by exact prefixLift 1010676
  have htrace : WordTrace (prefixWord ++ tailWord_1010676) baseStart_1010676 baseEnd_1010676 := by
    simpa [prefixWord, tailWord_1010676, baseEnd_1010676] using wordTrace_append hprefix tailTrace_1010676
  have hstable : (prefixWord ++ tailWord_1010676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010676).length < 2 ^ (prefixWord ++ tailWord_1010676).sum := by decide
  have hdescent : baseEnd_1010676 < baseStart_1010676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010707 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 2, 5, 2]
def baseStart_1010707 : Nat := 118140960795 + 1010707 * 2 ^ 59
def prefixEnd_1010707 : Nat := 4983230072969 + 3 ^ 40 * 1010707 * 2
def baseEnd_1010707 : Nat := 518978491863882337914349

theorem tailTrace_1010707 : CollatzResearch.WordTrace tailWord_1010707 prefixEnd_1010707 518978491863882337914349 := by
  unfold tailWord_1010707
  simp only [CollatzResearch.WordTrace]
  refine ⟨36863512749388628858126375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24575675166259085905417583 36863512749388628858126375)
  ·
    refine ⟨55295269124082943287189563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36863512749388628858126375 55295269124082943287189563)
    ·
      refine ⟨82942903686124414930784345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55295269124082943287189563 82942903686124414930784345)
      ·
        refine ⟨62207177764593311198088259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82942903686124414930784345 62207177764593311198088259)
        ·
          refine ⟨93310766646889966797132389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62207177764593311198088259 93310766646889966797132389)
          ·
            refine ⟨17495768746291868774462323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93310766646889966797132389 17495768746291868774462323)
            ·
              refine ⟨26243653119437803161693485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17495768746291868774462323 26243653119437803161693485)
              ·
                refine ⟨9841369919789176185635057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26243653119437803161693485 9841369919789176185635057)
                ·
                  refine ⟨7381027439841882139226293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9841369919789176185635057 7381027439841882139226293)
                  ·
                    refine ⟨691971322485176450552465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7381027439841882139226293 691971322485176450552465)
                    ·
                      refine ⟨518978491863882337914349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 691971322485176450552465 518978491863882337914349)
                      ·
                        rfl

theorem cell23_1010707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 5, 2].length) (baseStart_1010707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010707 prefixEnd_1010707 := by exact prefixLift 1010707
  have htrace : WordTrace (prefixWord ++ tailWord_1010707) baseStart_1010707 baseEnd_1010707 := by
    simpa [prefixWord, tailWord_1010707, baseEnd_1010707] using wordTrace_append hprefix tailTrace_1010707
  have hstable : (prefixWord ++ tailWord_1010707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010707).length < 2 ^ (prefixWord ++ tailWord_1010707).sum := by decide
  have hdescent : baseEnd_1010707 < baseStart_1010707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010734 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1010734 : Nat := 118140960795 + 1010734 * 2 ^ 59
def prefixEnd_1010734 : Nat := 4983230072969 + 3 ^ 40 * 1010734 * 2
def baseEnd_1010734 : Nat := 172997451947184577425575

theorem tailTrace_1010734 : CollatzResearch.WordTrace tailWord_1010734 prefixEnd_1010734 172997451947184577425575 := by
  unfold tailWord_1010734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608062190036351558669907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24576331680193874979572837 4608062190036351558669907)
  ·
    refine ⟨6912093285054527338004861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4608062190036351558669907 6912093285054527338004861)
    ·
      refine ⟨2592034981895447751751823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6912093285054527338004861 2592034981895447751751823)
      ·
        refine ⟨3888052472843171627627735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2592034981895447751751823 3888052472843171627627735)
        ·
          refine ⟨5832078709264757441441603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888052472843171627627735 5832078709264757441441603)
          ·
            refine ⟨8748118063897136162162405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832078709264757441441603 8748118063897136162162405)
            ·
              refine ⟨1640272136980713030405451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8748118063897136162162405 1640272136980713030405451)
              ·
                refine ⟨2460408205471069545608177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640272136980713030405451 2460408205471069545608177)
                ·
                  refine ⟨1845306154103302159206133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2460408205471069545608177 1845306154103302159206133)
                  ·
                    refine ⟨172997451947184577425575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1845306154103302159206133 172997451947184577425575)
                    ·
                      rfl

theorem cell23_1010734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1010734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010734 prefixEnd_1010734 := by exact prefixLift 1010734
  have htrace : WordTrace (prefixWord ++ tailWord_1010734) baseStart_1010734 baseEnd_1010734 := by
    simpa [prefixWord, tailWord_1010734, baseEnd_1010734] using wordTrace_append hprefix tailTrace_1010734
  have hstable : (prefixWord ++ tailWord_1010734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010734).length < 2 ^ (prefixWord ++ tailWord_1010734).sum := by decide
  have hdescent : baseEnd_1010734 < baseStart_1010734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010791 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_1010791 : Nat := 118140960795 + 1010791 * 2 ^ 59
def prefixEnd_1010791 : Nat := 4983230072969 + 3 ^ 40 * 1010791 * 2
def baseEnd_1010791 : Nat := 519021624238860009263963

theorem tailTrace_1010791 : CollatzResearch.WordTrace tailWord_1010791 prefixEnd_1010791 519021624238860009263963 := by
  unfold tailWord_1010791
  simp only [CollatzResearch.WordTrace]
  refine ⟨36866576481084311204184227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24577717654056207469456151 36866576481084311204184227)
  ·
    refine ⟨55299864721626466806276341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36866576481084311204184227 55299864721626466806276341)
    ·
      refine ⟨5184362317652481263088407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55299864721626466806276341 5184362317652481263088407)
      ·
        refine ⟨7776543476478721894632611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184362317652481263088407 7776543476478721894632611)
        ·
          refine ⟨11664815214718082841948917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7776543476478721894632611 11664815214718082841948917)
          ·
            refine ⟨1093576426379820266432711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11664815214718082841948917 1093576426379820266432711)
            ·
              refine ⟨1640364639569730399649067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093576426379820266432711 1640364639569730399649067)
              ·
                refine ⟨2460546959354595599473601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640364639569730399649067 2460546959354595599473601)
                ·
                  refine ⟨1845410219515946699605201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2460546959354595599473601 1845410219515946699605201)
                  ·
                    refine ⟨1384057664636960024703901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1845410219515946699605201 1384057664636960024703901)
                    ·
                      refine ⟨519021624238860009263963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384057664636960024703901 519021624238860009263963)
                      ·
                        rfl

theorem cell23_1010791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_1010791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010791 prefixEnd_1010791 := by exact prefixLift 1010791
  have htrace : WordTrace (prefixWord ++ tailWord_1010791) baseStart_1010791 baseEnd_1010791 := by
    simpa [prefixWord, tailWord_1010791, baseEnd_1010791] using wordTrace_append hprefix tailTrace_1010791
  have hstable : (prefixWord ++ tailWord_1010791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010791).length < 2 ^ (prefixWord ++ tailWord_1010791).sum := by decide
  have hdescent : baseEnd_1010791 < baseStart_1010791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010798 : List Nat := [4, 1, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1010798 : Nat := 118140960795 + 1010798 * 2 ^ 59
def prefixEnd_1010798 : Nat := 4983230072969 + 3 ^ 40 * 1010798 * 2
def baseEnd_1010798 : Nat := 173008406201147160625477

theorem tailTrace_1010798 : CollatzResearch.WordTrace tailWord_1010798 prefixEnd_1010798 173008406201147160625477 := by
  unfold tailWord_1010798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608353974007368924961131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24577887861372634266459365 4608353974007368924961131)
  ·
    refine ⟨6912530961011053387441697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4608353974007368924961131 6912530961011053387441697)
    ·
      refine ⟨5184398220758290040581273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6912530961011053387441697 5184398220758290040581273)
      ·
        refine ⟨3888298665568717530435955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5184398220758290040581273 3888298665568717530435955)
        ·
          refine ⟨5832447998353076295653933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888298665568717530435955 5832447998353076295653933)
          ·
            refine ⟨2187167999382403610870225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5832447998353076295653933 2187167999382403610870225)
            ·
              refine ⟨1640375999536802708152669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187167999382403610870225 1640375999536802708152669)
              ·
                refine ⟨615140999826301015557251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1640375999536802708152669 615140999826301015557251)
                ·
                  refine ⟨922711499739451523335877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615140999826301015557251 922711499739451523335877)
                  ·
                    refine ⟨173008406201147160625477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 922711499739451523335877 173008406201147160625477)
                    ·
                      rfl

theorem cell23_1010798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1010798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010798 prefixEnd_1010798 := by exact prefixLift 1010798
  have htrace : WordTrace (prefixWord ++ tailWord_1010798) baseStart_1010798 baseEnd_1010798 := by
    simpa [prefixWord, tailWord_1010798, baseEnd_1010798] using wordTrace_append hprefix tailTrace_1010798
  have hstable : (prefixWord ++ tailWord_1010798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010798).length < 2 ^ (prefixWord ++ tailWord_1010798).sum := by decide
  have hdescent : baseEnd_1010798 < baseStart_1010798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010827 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 4]
def baseStart_1010827 : Nat := 118140960795 + 1010827 * 2 ^ 59
def prefixEnd_1010827 : Nat := 4983230072969 + 3 ^ 40 * 1010827 * 2
def baseEnd_1010827 : Nat := 519040109542421868413797

theorem tailTrace_1010827 : CollatzResearch.WordTrace tailWord_1010827 prefixEnd_1010827 519040109542421868413797 := by
  unfold tailWord_1010827
  simp only [CollatzResearch.WordTrace]
  refine ⟨36867889508953889352494735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24578593005969259568329823 36867889508953889352494735)
  ·
    refine ⟨55301834263430834028742103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36867889508953889352494735 55301834263430834028742103)
    ·
      refine ⟨82952751395146251043113155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55301834263430834028742103 82952751395146251043113155)
      ·
        refine ⟨124429127092719376564669733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82952751395146251043113155 124429127092719376564669733)
        ·
          refine ⟨23330461329884883105875575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124429127092719376564669733 23330461329884883105875575)
          ·
            refine ⟨34995691994827324658813363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23330461329884883105875575 34995691994827324658813363)
            ·
              refine ⟨52493537992240986988220045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34995691994827324658813363 52493537992240986988220045)
              ·
                refine ⟨19685076747090370120582517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52493537992240986988220045 19685076747090370120582517)
                ·
                  refine ⟨1845475945039722198804611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19685076747090370120582517 1845475945039722198804611)
                  ·
                    refine ⟨2768213917559583298206917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1845475945039722198804611 2768213917559583298206917)
                    ·
                      refine ⟨519040109542421868413797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2768213917559583298206917 519040109542421868413797)
                      ·
                        rfl

theorem cell23_1010827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 4].length) (baseStart_1010827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010827 prefixEnd_1010827 := by exact prefixLift 1010827
  have htrace : WordTrace (prefixWord ++ tailWord_1010827) baseStart_1010827 baseEnd_1010827 := by
    simpa [prefixWord, tailWord_1010827, baseEnd_1010827] using wordTrace_append hprefix tailTrace_1010827
  have hstable : (prefixWord ++ tailWord_1010827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010827).length < 2 ^ (prefixWord ++ tailWord_1010827).sum := by decide
  have hdescent : baseEnd_1010827 < baseStart_1010827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010837 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_1010837 : Nat := 118140960795 + 1010837 * 2 ^ 59
def prefixEnd_1010837 : Nat := 4983230072969 + 3 ^ 40 * 1010837 * 2
def baseEnd_1010837 : Nat := 173015081449655609762917

theorem tailTrace_1010837 : CollatzResearch.WordTrace tailWord_1010837 prefixEnd_1010837 173015081449655609762917 := by
  unfold tailWord_1010837
  simp only [CollatzResearch.WordTrace]
  refine ⟨36868254238917661060358765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24578836159278440706905843 36868254238917661060358765)
  ·
    refine ⟨13825595339594122897634537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36868254238917661060358765 13825595339594122897634537)
    ·
      refine ⟨10369196504695592173225903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13825595339594122897634537 10369196504695592173225903)
      ·
        refine ⟨15553794757043388259838855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10369196504695592173225903 15553794757043388259838855)
        ·
          refine ⟨23330692135565082389758283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15553794757043388259838855 23330692135565082389758283)
          ·
            refine ⟨34996038203347623584637425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23330692135565082389758283 34996038203347623584637425)
            ·
              refine ⟨26247028652510717688478069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34996038203347623584637425 26247028652510717688478069)
              ·
                refine ⟨2460658936172879783294819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26247028652510717688478069 2460658936172879783294819)
                ·
                  refine ⟨3690988404259319674942229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460658936172879783294819 3690988404259319674942229)
                  ·
                    refine ⟨173015081449655609762917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3690988404259319674942229 173015081449655609762917)
                    ·
                      rfl

theorem cell23_1010837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_1010837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010837 prefixEnd_1010837 := by exact prefixLift 1010837
  have htrace : WordTrace (prefixWord ++ tailWord_1010837) baseStart_1010837 baseEnd_1010837 := by
    simpa [prefixWord, tailWord_1010837, baseEnd_1010837] using wordTrace_append hprefix tailTrace_1010837
  have hstable : (prefixWord ++ tailWord_1010837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010837).length < 2 ^ (prefixWord ++ tailWord_1010837).sum := by decide
  have hdescent : baseEnd_1010837 < baseStart_1010837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010855 : List Nat := [1, 1, 6, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_1010855 : Nat := 118140960795 + 1010855 * 2 ^ 59
def prefixEnd_1010855 : Nat := 4983230072969 + 3 ^ 40 * 1010855 * 2
def baseEnd_1010855 : Nat := 519054487000747758863669

theorem tailTrace_1010855 : CollatzResearch.WordTrace tailWord_1010855 prefixEnd_1010855 519054487000747758863669 := by
  unfold tailWord_1010855
  simp only [CollatzResearch.WordTrace]
  refine ⟨36868910752852450134514019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24579273835234966756342679 36868910752852450134514019)
  ·
    refine ⟨55303366129278675201771029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36868910752852450134514019 55303366129278675201771029)
    ·
      refine ⟨2592345287309937900083017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55303366129278675201771029 2592345287309937900083017)
      ·
        refine ⟨1944258965482453425062263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2592345287309937900083017 1944258965482453425062263)
        ·
          refine ⟨2916388448223680137593395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944258965482453425062263 2916388448223680137593395)
          ·
            refine ⟨4374582672335520206390093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916388448223680137593395 4374582672335520206390093)
            ·
              refine ⟨1640468502125820077396285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4374582672335520206390093 1640468502125820077396285)
              ·
                refine ⟨615175688297182529023607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1640468502125820077396285 615175688297182529023607)
                ·
                  refine ⟨922763532445773793535411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615175688297182529023607 922763532445773793535411)
                  ·
                    refine ⟨1384145298668660690303117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 922763532445773793535411 1384145298668660690303117)
                    ·
                      refine ⟨519054487000747758863669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384145298668660690303117 519054487000747758863669)
                      ·
                        rfl

theorem cell23_1010855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_1010855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010855 prefixEnd_1010855 := by exact prefixLift 1010855
  have htrace : WordTrace (prefixWord ++ tailWord_1010855) baseStart_1010855 baseEnd_1010855 := by
    simpa [prefixWord, tailWord_1010855, baseEnd_1010855] using wordTrace_append hprefix tailTrace_1010855
  have hstable : (prefixWord ++ tailWord_1010855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010855).length < 2 ^ (prefixWord ++ tailWord_1010855).sum := by decide
  have hdescent : baseEnd_1010855 < baseStart_1010855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010881 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1010881 : Nat := 118140960795 + 1010881 * 2 ^ 59
def prefixEnd_1010881 : Nat := 4983230072969 + 3 ^ 40 * 1010881 * 2
def baseEnd_1010881 : Nat := 519067837497764657138549

theorem tailTrace_1010881 : CollatzResearch.WordTrace tailWord_1010881 prefixEnd_1010881 519067837497764657138549 := by
  unfold tailWord_1010881
  simp only [CollatzResearch.WordTrace]
  refine ⟨36869859050758256574960497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24579906033838837716640331 36869859050758256574960497)
  ·
    refine ⟨27652394288068692431220373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36869859050758256574960497 27652394288068692431220373)
    ·
      refine ⟨1296205982253219957713455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27652394288068692431220373 1296205982253219957713455)
      ·
        refine ⟨1944308973379829936570183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296205982253219957713455 1944308973379829936570183)
        ·
          refine ⟨2916463460069744904855275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944308973379829936570183 2916463460069744904855275)
          ·
            refine ⟨4374695190104617357282913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2916463460069744904855275 4374695190104617357282913)
            ·
              refine ⟨3281021392578463017962185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4374695190104617357282913 3281021392578463017962185)
              ·
                refine ⟨2460766044433847263471639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3281021392578463017962185 2460766044433847263471639)
                ·
                  refine ⟨3691149066650770895207459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460766044433847263471639 3691149066650770895207459)
                  ·
                    refine ⟨5536723599976156342811189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3691149066650770895207459 5536723599976156342811189)
                    ·
                      refine ⟨519067837497764657138549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5536723599976156342811189 519067837497764657138549)
                      ·
                        rfl

theorem cell23_1010881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1010881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010881 prefixEnd_1010881 := by exact prefixLift 1010881
  have htrace : WordTrace (prefixWord ++ tailWord_1010881) baseStart_1010881 baseEnd_1010881 := by
    simpa [prefixWord, tailWord_1010881, baseEnd_1010881] using wordTrace_append hprefix tailTrace_1010881
  have hstable : (prefixWord ++ tailWord_1010881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010881).length < 2 ^ (prefixWord ++ tailWord_1010881).sum := by decide
  have hdescent : baseEnd_1010881 < baseStart_1010881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010954 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1010954 : Nat := 118140960795 + 1010954 * 2 ^ 59
def prefixEnd_1010954 : Nat := 4983230072969 + 3 ^ 40 * 1010954 * 2
def baseEnd_1010954 : Nat := 519105321585542871525713

theorem tailTrace_1010954 : CollatzResearch.WordTrace tailWord_1010954 prefixEnd_1010954 519105321585542871525713 := by
  unfold tailWord_1010954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218130394873447510591979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24581681052995860028245277 9218130394873447510591979)
  ·
    refine ⟨13827195592310171265887969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9218130394873447510591979 13827195592310171265887969)
    ·
      refine ⟨10370396694232628449415977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13827195592310171265887969 10370396694232628449415977)
      ·
        refine ⟨7777797520674471337061983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10370396694232628449415977 7777797520674471337061983)
        ·
          refine ⟨11666696281011707005592975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777797520674471337061983 11666696281011707005592975)
          ·
            refine ⟨17500044421517560508389463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11666696281011707005592975 17500044421517560508389463)
            ·
              refine ⟨26250066632276340762584195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17500044421517560508389463 26250066632276340762584195)
              ·
                refine ⟨39375099948414511143876293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26250066632276340762584195 39375099948414511143876293)
                ·
                  refine ⟨7382831240327720839476805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39375099948414511143876293 7382831240327720839476805)
                  ·
                    refine ⟨1384280857561447657401901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7382831240327720839476805 1384280857561447657401901)
                    ·
                      refine ⟨519105321585542871525713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384280857561447657401901 519105321585542871525713)
                      ·
                        rfl

theorem cell23_1010954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1010954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010954 prefixEnd_1010954 := by exact prefixLift 1010954
  have htrace : WordTrace (prefixWord ++ tailWord_1010954) baseStart_1010954 baseEnd_1010954 := by
    simpa [prefixWord, tailWord_1010954, baseEnd_1010954] using wordTrace_append hprefix tailTrace_1010954
  have hstable : (prefixWord ++ tailWord_1010954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010954).length < 2 ^ (prefixWord ++ tailWord_1010954).sum := by decide
  have hdescent : baseEnd_1010954 < baseStart_1010954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010987 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 11]
def baseStart_1010987 : Nat := 118140960795 + 1010987 * 2 ^ 59
def prefixEnd_1010987 : Nat := 4983230072969 + 3 ^ 40 * 1010987 * 2
def baseEnd_1010987 : Nat := 173040755482380414137687

theorem tailTrace_1010987 : CollatzResearch.WordTrace tailWord_1010987 prefixEnd_1010987 173040755482380414137687 := by
  unfold tailWord_1010987
  simp only [CollatzResearch.WordTrace]
  refine ⟨36873725188374236678319215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24582483458916157785546143 36873725188374236678319215)
  ·
    refine ⟨55310587782561355017478823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36873725188374236678319215 55310587782561355017478823)
    ·
      refine ⟨82965881673842032526218235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55310587782561355017478823 82965881673842032526218235)
      ·
        refine ⟨124448822510763048789327353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82965881673842032526218235 124448822510763048789327353)
        ·
          refine ⟨93336616883072286591995515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124448822510763048789327353 93336616883072286591995515)
          ·
            refine ⟨140004925324608429887993273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93336616883072286591995515 140004925324608429887993273)
            ·
              refine ⟨105003693993456322415994955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140004925324608429887993273 105003693993456322415994955)
              ·
                refine ⟨157505540990184483623992433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105003693993456322415994955 157505540990184483623992433)
                ·
                  refine ⟨118129155742638362717994325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157505540990184483623992433 118129155742638362717994325)
                  ·
                    refine ⟨173040755482380414137687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 118129155742638362717994325 173040755482380414137687)
                    ·
                      rfl

theorem cell23_1010987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 11].length) (baseStart_1010987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1010987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1010987 prefixEnd_1010987 := by exact prefixLift 1010987
  have htrace : WordTrace (prefixWord ++ tailWord_1010987) baseStart_1010987 baseEnd_1010987 := by
    simpa [prefixWord, tailWord_1010987, baseEnd_1010987] using wordTrace_append hprefix tailTrace_1010987
  have hstable : (prefixWord ++ tailWord_1010987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010987).length < 2 ^ (prefixWord ++ tailWord_1010987).sum := by decide
  have hdescent : baseEnd_1010987 < baseStart_1010987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011004 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_1011004 : Nat := 118140960795 + 1011004 * 2 ^ 59
def prefixEnd_1011004 : Nat := 4983230072969 + 3 ^ 40 * 1011004 * 2
def baseEnd_1011004 : Nat := 173043665206089225300161

theorem tailTrace_1011004 : CollatzResearch.WordTrace tailWord_1011004 prefixEnd_1011004 173043665206089225300161 := by
  unfold tailWord_1011004
  simp only [CollatzResearch.WordTrace]
  refine ⟨18437172614656324290844033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24582896819541765721125377 18437172614656324290844033)
  ·
    refine ⟨13827879460992243218133025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18437172614656324290844033 13827879460992243218133025)
    ·
      refine ⟨10370909595744182413599769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13827879460992243218133025 10370909595744182413599769)
      ·
        refine ⟨7778182196808136810199827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10370909595744182413599769 7778182196808136810199827)
        ·
          refine ⟨11667273295212205215299741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778182196808136810199827 11667273295212205215299741)
          ·
            refine ⟨4375227485704576955737403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11667273295212205215299741 4375227485704576955737403)
            ·
              refine ⟨6562841228556865433606105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4375227485704576955737403 6562841228556865433606105)
              ·
                refine ⟨4922130921417649075204579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6562841228556865433606105 4922130921417649075204579)
                ·
                  refine ⟨7383196382126473612806869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922130921417649075204579 7383196382126473612806869)
                  ·
                    refine ⟨173043665206089225300161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7383196382126473612806869 173043665206089225300161)
                    ·
                      rfl

theorem cell23_1011004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_1011004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011004 prefixEnd_1011004 := by exact prefixLift 1011004
  have htrace : WordTrace (prefixWord ++ tailWord_1011004) baseStart_1011004 baseEnd_1011004 := by
    simpa [prefixWord, tailWord_1011004, baseEnd_1011004] using wordTrace_append hprefix tailTrace_1011004
  have hstable : (prefixWord ++ tailWord_1011004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011004).length < 2 ^ (prefixWord ++ tailWord_1011004).sum := by decide
  have hdescent : baseEnd_1011004 < baseStart_1011004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011024 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_1011024 : Nat := 118140960795 + 1011024 * 2 ^ 59
def prefixEnd_1011024 : Nat := 4983230072969 + 3 ^ 40 * 1011024 * 2
def baseEnd_1011024 : Nat := 519141265231357597650391

theorem tailTrace_1011024 : CollatzResearch.WordTrace tailWord_1011024 prefixEnd_1011024 519141265231357597650391 := by
  unfold tailWord_1011024
  simp only [CollatzResearch.WordTrace]
  refine ⟨18437537344620095998708063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24583383126160127998277417 18437537344620095998708063)
  ·
    refine ⟨27656306016930143998062095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18437537344620095998708063 27656306016930143998062095)
    ·
      refine ⟨41484459025395215997093143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27656306016930143998062095 41484459025395215997093143)
      ·
        refine ⟨62226688538092823995639715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41484459025395215997093143 62226688538092823995639715)
        ·
          refine ⟨93340032807139235993459573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62226688538092823995639715 93340032807139235993459573)
          ·
            refine ⟨8750628075669303374386835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93340032807139235993459573 8750628075669303374386835)
            ·
              refine ⟨13125942113503955061580253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8750628075669303374386835 13125942113503955061580253)
              ·
                refine ⟨4922228292563983148092595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13125942113503955061580253 4922228292563983148092595)
                ·
                  refine ⟨7383342438845974722138893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922228292563983148092595 7383342438845974722138893)
                  ·
                    refine ⟨2768753414567240520802085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7383342438845974722138893 2768753414567240520802085)
                    ·
                      refine ⟨519141265231357597650391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2768753414567240520802085 519141265231357597650391)
                      ·
                        rfl

theorem cell23_1011024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_1011024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011024 prefixEnd_1011024 := by exact prefixLift 1011024
  have htrace : WordTrace (prefixWord ++ tailWord_1011024) baseStart_1011024 baseEnd_1011024 := by
    simpa [prefixWord, tailWord_1011024, baseEnd_1011024] using wordTrace_append hprefix tailTrace_1011024
  have hstable : (prefixWord ++ tailWord_1011024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011024).length < 2 ^ (prefixWord ++ tailWord_1011024).sum := by decide
  have hdescent : baseEnd_1011024 < baseStart_1011024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011041 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_1011041 : Nat := 118140960795 + 1011041 * 2 ^ 59
def prefixEnd_1011041 : Nat := 4983230072969 + 3 ^ 40 * 1011041 * 2
def baseEnd_1011041 : Nat := 519149994402484031137813

theorem tailTrace_1011041 : CollatzResearch.WordTrace tailWord_1011041 prefixEnd_1011041 519149994402484031137813 := by
  unfold tailWord_1011041
  simp only [CollatzResearch.WordTrace]
  refine ⟨36875694730178603900784977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24583796486785735933856651 36875694730178603900784977)
  ·
    refine ⟨27656771047633952925588733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36875694730178603900784977 27656771047633952925588733)
    ·
      refine ⟨10371289142862732347095775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27656771047633952925588733 10371289142862732347095775)
      ·
        refine ⟨15556933714294098520643663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371289142862732347095775 15556933714294098520643663)
        ·
          refine ⟨23335400571441147780965495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556933714294098520643663 23335400571441147780965495)
          ·
            refine ⟨35003100857161721671448243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23335400571441147780965495 35003100857161721671448243)
            ·
              refine ⟨52504651285742582507172365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35003100857161721671448243 52504651285742582507172365)
              ·
                refine ⟨19689244232153468440189637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52504651285742582507172365 19689244232153468440189637)
                ·
                  refine ⟨3691733293528775332535557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19689244232153468440189637 3691733293528775332535557)
                  ·
                    refine ⟨692199992536645374850417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3691733293528775332535557 692199992536645374850417)
                    ·
                      refine ⟨519149994402484031137813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692199992536645374850417 519149994402484031137813)
                      ·
                        rfl

theorem cell23_1011041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_1011041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011041 prefixEnd_1011041 := by exact prefixLift 1011041
  have htrace : WordTrace (prefixWord ++ tailWord_1011041) baseStart_1011041 baseEnd_1011041 := by
    simpa [prefixWord, tailWord_1011041, baseEnd_1011041] using wordTrace_append hprefix tailTrace_1011041
  have hstable : (prefixWord ++ tailWord_1011041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011041).length < 2 ^ (prefixWord ++ tailWord_1011041).sum := by decide
  have hdescent : baseEnd_1011041 < baseStart_1011041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011108 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_1011108 : Nat := 118140960795 + 1011108 * 2 ^ 59
def prefixEnd_1011108 : Nat := 4983230072969 + 3 ^ 40 * 1011108 * 2
def baseEnd_1011108 : Nat := 519184397606335269000005

theorem tailTrace_1011108 : CollatzResearch.WordTrace tailWord_1011108 prefixEnd_1011108 519184397606335269000005 := by
  unfold tailWord_1011108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18439069210467937171736989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24585425613957249562315985 18439069210467937171736989)
  ·
    refine ⟨6914650953925476439401371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18439069210467937171736989 6914650953925476439401371)
    ·
      refine ⟨10371976430888214659102057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6914650953925476439401371 10371976430888214659102057)
      ·
        refine ⟨7778982323166160994326543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10371976430888214659102057 7778982323166160994326543)
        ·
          refine ⟨11668473484749241491489815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778982323166160994326543 11668473484749241491489815)
          ·
            refine ⟨17502710227123862237234723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11668473484749241491489815 17502710227123862237234723)
            ·
              refine ⟨26254065340685793355852085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17502710227123862237234723 26254065340685793355852085)
              ·
                refine ⟨2461318625689293127111133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26254065340685793355852085 2461318625689293127111133)
                ·
                  refine ⟨922994484633484922666675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2461318625689293127111133 922994484633484922666675)
                  ·
                    refine ⟨1384491726950227384000013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 922994484633484922666675 1384491726950227384000013)
                    ·
                      refine ⟨519184397606335269000005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384491726950227384000013 519184397606335269000005)
                      ·
                        rfl

theorem cell23_1011108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_1011108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011108 prefixEnd_1011108 := by exact prefixLift 1011108
  have htrace : WordTrace (prefixWord ++ tailWord_1011108) baseStart_1011108 baseEnd_1011108 := by
    simpa [prefixWord, tailWord_1011108, baseEnd_1011108] using wordTrace_append hprefix tailTrace_1011108
  have hstable : (prefixWord ++ tailWord_1011108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011108).length < 2 ^ (prefixWord ++ tailWord_1011108).sum := by decide
  have hdescent : baseEnd_1011108 < baseStart_1011108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011111 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1011111 : Nat := 118140960795 + 1011111 * 2 ^ 59
def prefixEnd_1011111 : Nat := 4983230072969 + 3 ^ 40 * 1011111 * 2
def baseEnd_1011111 : Nat := 173061979349432919087497

theorem tailTrace_1011111 : CollatzResearch.WordTrace tailWord_1011111 prefixEnd_1011111 173061979349432919087497 := by
  unfold tailWord_1011111
  simp only [CollatzResearch.WordTrace]
  refine ⟨36878247839925005855833187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24585498559950003903888791 36878247839925005855833187)
  ·
    refine ⟨55317371759887508783749781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36878247839925005855833187 55317371759887508783749781)
    ·
      refine ⟨2593001801244726974238271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55317371759887508783749781 2593001801244726974238271)
      ·
        refine ⟨3889502701867090461357407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593001801244726974238271 3889502701867090461357407)
        ·
          refine ⟨5834254052800635692036111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3889502701867090461357407 5834254052800635692036111)
          ·
            refine ⟨8751381079200953538054167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834254052800635692036111 8751381079200953538054167)
            ·
              refine ⟨13127071618801430307081251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8751381079200953538054167 13127071618801430307081251)
              ·
                refine ⟨19690607428202145460621877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13127071618801430307081251 19690607428202145460621877)
                ·
                  refine ⟨1845994446393951136933301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19690607428202145460621877 1845994446393951136933301)
                  ·
                    refine ⟨173061979349432919087497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1845994446393951136933301 173061979349432919087497)
                    ·
                      rfl

theorem cell23_1011111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1011111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011111 prefixEnd_1011111 := by exact prefixLift 1011111
  have htrace : WordTrace (prefixWord ++ tailWord_1011111) baseStart_1011111 baseEnd_1011111 := by
    simpa [prefixWord, tailWord_1011111, baseEnd_1011111] using wordTrace_append hprefix tailTrace_1011111
  have hstable : (prefixWord ++ tailWord_1011111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011111).length < 2 ^ (prefixWord ++ tailWord_1011111).sum := by decide
  have hdescent : baseEnd_1011111 < baseStart_1011111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011125 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1011125 : Nat := 118140960795 + 1011125 * 2 ^ 59
def prefixEnd_1011125 : Nat := 4983230072969 + 3 ^ 40 * 1011125 * 2
def baseEnd_1011125 : Nat := 519193126777461702487427

theorem tailTrace_1011125 : CollatzResearch.WordTrace tailWord_1011125 prefixEnd_1011125 519193126777461702487427 := by
  unfold tailWord_1011125
  simp only [CollatzResearch.WordTrace]
  refine ⟨36878758461874286246842829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24585838974582857497895219 36878758461874286246842829)
  ·
    refine ⟨13829534423202857342566061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36878758461874286246842829 13829534423202857342566061)
    ·
      refine ⟨5186075408701071503462273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13829534423202857342566061 5186075408701071503462273)
      ·
        refine ⟨3889556556525803627596705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5186075408701071503462273 3889556556525803627596705)
        ·
          refine ⟨2917167417394352720697529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3889556556525803627596705 2917167417394352720697529)
          ·
            refine ⟨2187875563045764540523147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2917167417394352720697529 2187875563045764540523147)
            ·
              refine ⟨3281813344568646810784721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187875563045764540523147 3281813344568646810784721)
              ·
                refine ⟨2461360008426485108088541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3281813344568646810784721 2461360008426485108088541)
                ·
                  refine ⟨923010003159931915533203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2461360008426485108088541 923010003159931915533203)
                  ·
                    refine ⟨1384515004739897873299805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 923010003159931915533203 1384515004739897873299805)
                    ·
                      refine ⟨519193126777461702487427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384515004739897873299805 519193126777461702487427)
                      ·
                        rfl

theorem cell23_1011125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1011125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011125 prefixEnd_1011125 := by exact prefixLift 1011125
  have htrace : WordTrace (prefixWord ++ tailWord_1011125) baseStart_1011125 baseEnd_1011125 := by
    simpa [prefixWord, tailWord_1011125, baseEnd_1011125] using wordTrace_append hprefix tailTrace_1011125
  have hstable : (prefixWord ++ tailWord_1011125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011125).length < 2 ^ (prefixWord ++ tailWord_1011125).sum := by decide
  have hdescent : baseEnd_1011125 < baseStart_1011125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011178 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1011178 : Nat := 118140960795 + 1011178 * 2 ^ 59
def prefixEnd_1011178 : Nat := 4983230072969 + 3 ^ 40 * 1011178 * 2
def baseEnd_1011178 : Nat := 519220341252149995124683

theorem tailTrace_1011178 : CollatzResearch.WordTrace tailWord_1011178 prefixEnd_1011178 519220341252149995124683 := by
  unfold tailWord_1011178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9220172882670569074630547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24587127687121517532348125 9220172882670569074630547)
  ·
    refine ⟨13830259324005853611945821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9220172882670569074630547 13830259324005853611945821)
    ·
      refine ⟨5186347246502195104479683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13830259324005853611945821 5186347246502195104479683)
      ·
        refine ⟨7779520869753292656719525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5186347246502195104479683 7779520869753292656719525)
        ·
          refine ⟨1458660163078742373134911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7779520869753292656719525 1458660163078742373134911)
          ·
            refine ⟨2187990244618113559702367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458660163078742373134911 2187990244618113559702367)
            ·
              refine ⟨3281985366927170339553551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187990244618113559702367 3281985366927170339553551)
              ·
                refine ⟨4922978050390755509330327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281985366927170339553551 4922978050390755509330327)
                ·
                  refine ⟨7384467075586133263995491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922978050390755509330327 7384467075586133263995491)
                  ·
                    refine ⟨11076700613379199895993237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7384467075586133263995491 11076700613379199895993237)
                    ·
                      refine ⟨519220341252149995124683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11076700613379199895993237 519220341252149995124683)
                      ·
                        rfl

theorem cell23_1011178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1011178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011178 prefixEnd_1011178 := by exact prefixLift 1011178
  have htrace : WordTrace (prefixWord ++ tailWord_1011178) baseStart_1011178 baseEnd_1011178 := by
    simpa [prefixWord, tailWord_1011178, baseEnd_1011178] using wordTrace_append hprefix tailTrace_1011178
  have hstable : (prefixWord ++ tailWord_1011178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011178).length < 2 ^ (prefixWord ++ tailWord_1011178).sum := by decide
  have hdescent : baseEnd_1011178 < baseStart_1011178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011185 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_1011185 : Nat := 118140960795 + 1011185 * 2 ^ 59
def prefixEnd_1011185 : Nat := 4983230072969 + 3 ^ 40 * 1011185 * 2
def baseEnd_1011185 : Nat := 519223935616731467737151

theorem tailTrace_1011185 : CollatzResearch.WordTrace tailWord_1011185 prefixEnd_1011185 519223935616731467737151 := by
  unfold tailWord_1011185
  simp only [CollatzResearch.WordTrace]
  refine ⟨36880946841656916494027009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24587297894437944329351339 36880946841656916494027009)
  ·
    refine ⟨27660710131242687370520257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36880946841656916494027009 27660710131242687370520257)
    ·
      refine ⟨20745532598432015527890193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27660710131242687370520257 20745532598432015527890193)
      ·
        refine ⟨15559149448824011645917645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20745532598432015527890193 15559149448824011645917645)
        ·
          refine ⟨5834681043309004367219117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15559149448824011645917645 5834681043309004367219117)
          ·
            refine ⟨2188005391240876637707169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5834681043309004367219117 2188005391240876637707169)
            ·
              refine ⟨1641004043430657478280377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2188005391240876637707169 1641004043430657478280377)
              ·
                refine ⟨1230753032572993108710283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641004043430657478280377 1230753032572993108710283)
                ·
                  refine ⟨1846129548859489663065425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230753032572993108710283 1846129548859489663065425)
                  ·
                    refine ⟨1384597161644617247299069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1846129548859489663065425 1384597161644617247299069)
                    ·
                      refine ⟨519223935616731467737151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384597161644617247299069 519223935616731467737151)
                      ·
                        rfl

theorem cell23_1011185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_1011185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011185 prefixEnd_1011185 := by exact prefixLift 1011185
  have htrace : WordTrace (prefixWord ++ tailWord_1011185) baseStart_1011185 baseEnd_1011185 := by
    simpa [prefixWord, tailWord_1011185, baseEnd_1011185] using wordTrace_append hprefix tailTrace_1011185
  have hstable : (prefixWord ++ tailWord_1011185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011185).length < 2 ^ (prefixWord ++ tailWord_1011185).sum := by decide
  have hdescent : baseEnd_1011185 < baseStart_1011185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011202 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1011202 : Nat := 118140960795 + 1011202 * 2 ^ 59
def prefixEnd_1011202 : Nat := 4983230072969 + 3 ^ 40 * 1011202 * 2
def baseEnd_1011202 : Nat := 519232664787857901224573

theorem tailTrace_1011202 : CollatzResearch.WordTrace tailWord_1011202 prefixEnd_1011202 519232664787857901224573 := by
  unfold tailWord_1011202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9220391720648832099348965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24587711255063552264930573 9220391720648832099348965)
  ·
    refine ⟨1728823447621656018627931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9220391720648832099348965 1728823447621656018627931)
    ·
      refine ⟨2593235171432484027941897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1728823447621656018627931 2593235171432484027941897)
      ·
        refine ⟨1944926378574363020956423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2593235171432484027941897 1944926378574363020956423)
        ·
          refine ⟨2917389567861544531434635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944926378574363020956423 2917389567861544531434635)
          ·
            refine ⟨4376084351792316797151953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2917389567861544531434635 4376084351792316797151953)
            ·
              refine ⟨3282063263844237597863965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4376084351792316797151953 3282063263844237597863965)
              ·
                refine ⟨1230773723941589099198987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3282063263844237597863965 1230773723941589099198987)
                ·
                  refine ⟨1846160585912383648798481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230773723941589099198987 1846160585912383648798481)
                  ·
                    refine ⟨1384620439434287736598861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1846160585912383648798481 1384620439434287736598861)
                    ·
                      refine ⟨519232664787857901224573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384620439434287736598861 519232664787857901224573)
                      ·
                        rfl

theorem cell23_1011202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1011202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011202 prefixEnd_1011202 := by exact prefixLift 1011202
  have htrace : WordTrace (prefixWord ++ tailWord_1011202) baseStart_1011202 baseEnd_1011202 := by
    simpa [prefixWord, tailWord_1011202, baseEnd_1011202] using wordTrace_append hprefix tailTrace_1011202
  have hstable : (prefixWord ++ tailWord_1011202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011202).length < 2 ^ (prefixWord ++ tailWord_1011202).sum := by decide
  have hdescent : baseEnd_1011202 < baseStart_1011202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011231 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 2, 6]
def baseStart_1011231 : Nat := 118140960795 + 1011231 * 2 ^ 59
def prefixEnd_1011231 : Nat := 4983230072969 + 3 ^ 40 * 1011231 * 2
def baseEnd_1011231 : Nat := 173082518575612762587313

theorem tailTrace_1011231 : CollatzResearch.WordTrace tailWord_1011231 prefixEnd_1011231 173082518575612762587313 := by
  unfold tailWord_1011231
  simp only [CollatzResearch.WordTrace]
  refine ⟨36882624599490266350201547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24588416399660177566801031 36882624599490266350201547)
  ·
    refine ⟨55323936899235399525302321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36882624599490266350201547 55323936899235399525302321)
    ·
      refine ⟨41492952674426549643976741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55323936899235399525302321 41492952674426549643976741)
      ·
        refine ⟨7779928626454978058245639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41492952674426549643976741 7779928626454978058245639)
        ·
          refine ⟨11669892939682467087368459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7779928626454978058245639 11669892939682467087368459)
          ·
            refine ⟨17504839409523700631052689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11669892939682467087368459 17504839409523700631052689)
            ·
              refine ⟨13128629557142775473289517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17504839409523700631052689 13128629557142775473289517)
              ·
                refine ⟨4923236083928540802483569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13128629557142775473289517 4923236083928540802483569)
                ·
                  refine ⟨3692427062946405601862677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4923236083928540802483569 3692427062946405601862677)
                  ·
                    refine ⟨173082518575612762587313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3692427062946405601862677 173082518575612762587313)
                    ·
                      rfl

theorem cell23_1011231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_1011231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011231 prefixEnd_1011231 := by exact prefixLift 1011231
  have htrace : WordTrace (prefixWord ++ tailWord_1011231) baseStart_1011231 baseEnd_1011231 := by
    simpa [prefixWord, tailWord_1011231, baseEnd_1011231] using wordTrace_append hprefix tailTrace_1011231
  have hstable : (prefixWord ++ tailWord_1011231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011231).length < 2 ^ (prefixWord ++ tailWord_1011231).sum := by decide
  have hdescent : baseEnd_1011231 < baseStart_1011231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011232 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1011232 : Nat := 118140960795 + 1011232 * 2 ^ 59
def prefixEnd_1011232 : Nat := 4983230072969 + 3 ^ 40 * 1011232 * 2
def baseEnd_1011232 : Nat := 519248069207492783849435

theorem tailTrace_1011232 : CollatzResearch.WordTrace tailWord_1011232 prefixEnd_1011232 519248069207492783849435 := by
  unfold tailWord_1011232
  simp only [CollatzResearch.WordTrace]
  refine ⟨18441330536243321760493975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24588440714991095680658633 18441330536243321760493975)
  ·
    refine ⟨27661995804364982640740963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18441330536243321760493975 27661995804364982640740963)
    ·
      refine ⟨41492993706547473961111445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27661995804364982640740963 41492993706547473961111445)
      ·
        refine ⟨1944984079994412841927099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41492993706547473961111445 1944984079994412841927099)
        ·
          refine ⟨2917476119991619262890649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944984079994412841927099 2917476119991619262890649)
          ·
            refine ⟨2188107089993714447167987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2917476119991619262890649 2188107089993714447167987)
            ·
              refine ⟨3282160634990571670751981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188107089993714447167987 3282160634990571670751981)
              ·
                refine ⟨1230810238121464376531993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3282160634990571670751981 1230810238121464376531993)
                ·
                  refine ⟨923107678591098282398995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1230810238121464376531993 923107678591098282398995)
                  ·
                    refine ⟨1384661517886647423598493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 923107678591098282398995 1384661517886647423598493)
                    ·
                      refine ⟨519248069207492783849435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384661517886647423598493 519248069207492783849435)
                      ·
                        rfl

theorem cell23_1011232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1011232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011232 prefixEnd_1011232 := by exact prefixLift 1011232
  have htrace : WordTrace (prefixWord ++ tailWord_1011232) baseStart_1011232 baseEnd_1011232 := by
    simpa [prefixWord, tailWord_1011232, baseEnd_1011232] using wordTrace_append hprefix tailTrace_1011232
  have hstable : (prefixWord ++ tailWord_1011232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011232).length < 2 ^ (prefixWord ++ tailWord_1011232).sum := by decide
  have hdescent : baseEnd_1011232 < baseStart_1011232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011255 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 1, 4, 2]
def baseStart_1011255 : Nat := 118140960795 + 1011255 * 2 ^ 59
def prefixEnd_1011255 : Nat := 4983230072969 + 3 ^ 40 * 1011255 * 2
def baseEnd_1011255 : Nat := 519259879262546193861829

theorem tailTrace_1011255 : CollatzResearch.WordTrace tailWord_1011255 prefixEnd_1011255 519259879262546193861829 := by
  unfold tailWord_1011255
  simp only [CollatzResearch.WordTrace]
  refine ⟨36883499951403318449075219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24588999967602212299383479 36883499951403318449075219)
  ·
    refine ⟨55325249927104977673612829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36883499951403318449075219 55325249927104977673612829)
    ·
      refine ⟨20746968722664366627604811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55325249927104977673612829 20746968722664366627604811)
      ·
        refine ⟨31120453083996549941407217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20746968722664366627604811 31120453083996549941407217)
        ·
          refine ⟨23340339812997412456055413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31120453083996549941407217 23340339812997412456055413)
          ·
            refine ⟨2188156857468507417755195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23340339812997412456055413 2188156857468507417755195)
            ·
              refine ⟨3282235286202761126632793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188156857468507417755195 3282235286202761126632793)
              ·
                refine ⟨2461676464652070844974595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282235286202761126632793 2461676464652070844974595)
                ·
                  refine ⟨3692514696978106267461893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461676464652070844974595 3692514696978106267461893)
                  ·
                    refine ⟨692346505683394925149105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3692514696978106267461893 692346505683394925149105)
                    ·
                      refine ⟨519259879262546193861829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692346505683394925149105 519259879262546193861829)
                      ·
                        rfl

theorem cell23_1011255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_1011255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011255 prefixEnd_1011255 := by exact prefixLift 1011255
  have htrace : WordTrace (prefixWord ++ tailWord_1011255) baseStart_1011255 baseEnd_1011255 := by
    simpa [prefixWord, tailWord_1011255, baseEnd_1011255] using wordTrace_append hprefix tailTrace_1011255
  have hstable : (prefixWord ++ tailWord_1011255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011255).length < 2 ^ (prefixWord ++ tailWord_1011255).sum := by decide
  have hdescent : baseEnd_1011255 < baseStart_1011255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011328 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_1011328 : Nat := 118140960795 + 1011328 * 2 ^ 59
def prefixEnd_1011328 : Nat := 4983230072969 + 3 ^ 40 * 1011328 * 2
def baseEnd_1011328 : Nat := 519297363350324408248993

theorem tailTrace_1011328 : CollatzResearch.WordTrace tailWord_1011328 prefixEnd_1011328 519297363350324408248993 := by
  unfold tailWord_1011328
  simp only [CollatzResearch.WordTrace]
  refine ⟨18443081240069425958241319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24590774986759234610988425 18443081240069425958241319)
  ·
    refine ⟨27664621860104138937361979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18443081240069425958241319 27664621860104138937361979)
    ·
      refine ⟨41496932790156208406042969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27664621860104138937361979 41496932790156208406042969)
      ·
        refine ⟨31122699592617156304532227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41496932790156208406042969 31122699592617156304532227)
        ·
          refine ⟨46684049388925734456798341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31122699592617156304532227 46684049388925734456798341)
          ·
            refine ⟨8753259260423575210649689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46684049388925734456798341 8753259260423575210649689)
            ·
              refine ⟨6564944445317681407987267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8753259260423575210649689 6564944445317681407987267)
              ·
                refine ⟨9847416667976522111980901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564944445317681407987267 9847416667976522111980901)
                ·
                  refine ⟨1846390625245597895996419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9847416667976522111980901 1846390625245597895996419)
                  ·
                    refine ⟨2769585937868396843994629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1846390625245597895996419 2769585937868396843994629)
                    ·
                      refine ⟨519297363350324408248993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2769585937868396843994629 519297363350324408248993)
                      ·
                        rfl

theorem cell23_1011328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_1011328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011328 prefixEnd_1011328 := by exact prefixLift 1011328
  have htrace : WordTrace (prefixWord ++ tailWord_1011328) baseStart_1011328 baseEnd_1011328 := by
    simpa [prefixWord, tailWord_1011328, baseEnd_1011328] using wordTrace_append hprefix tailTrace_1011328
  have hstable : (prefixWord ++ tailWord_1011328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011328).length < 2 ^ (prefixWord ++ tailWord_1011328).sum := by decide
  have hdescent : baseEnd_1011328 < baseStart_1011328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011389 : List Nat := [1, 4, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_1011389 : Nat := 118140960795 + 1011389 * 2 ^ 59
def prefixEnd_1011389 : Nat := 4983230072969 + 3 ^ 40 * 1011389 * 2
def baseEnd_1011389 : Nat := 173109561890082889862071

theorem tailTrace_1011389 : CollatzResearch.WordTrace tailWord_1011389 prefixEnd_1011389 173109561890082889862071 := by
  unfold tailWord_1011389
  simp only [CollatzResearch.WordTrace]
  refine ⟨36888387332917859334453221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24592258221945239556302147 36888387332917859334453221)
  ·
    refine ⟨6916572624922098625209979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36888387332917859334453221 6916572624922098625209979)
    ·
      refine ⟨10374858937383147937814969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6916572624922098625209979 10374858937383147937814969)
      ·
        refine ⟨7781144203037360953361227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10374858937383147937814969 7781144203037360953361227)
        ·
          refine ⟨11671716304556041430041841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781144203037360953361227 11671716304556041430041841)
          ·
            refine ⟨8753787228417031072531381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11671716304556041430041841 8753787228417031072531381)
            ·
              refine ⟨820667552664096663049817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8753787228417031072531381 820667552664096663049817)
              ·
                refine ⟨615500664498072497287363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820667552664096663049817 615500664498072497287363)
                ·
                  refine ⟨923250996747108745931045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615500664498072497287363 923250996747108745931045)
                  ·
                    refine ⟨173109561890082889862071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 923250996747108745931045 173109561890082889862071)
                    ·
                      rfl

theorem cell23_1011389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_1011389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011389 prefixEnd_1011389 := by exact prefixLift 1011389
  have htrace : WordTrace (prefixWord ++ tailWord_1011389) baseStart_1011389 baseEnd_1011389 := by
    simpa [prefixWord, tailWord_1011389, baseEnd_1011389] using wordTrace_append hprefix tailTrace_1011389
  have hstable : (prefixWord ++ tailWord_1011389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011389).length < 2 ^ (prefixWord ++ tailWord_1011389).sum := by decide
  have hdescent : baseEnd_1011389 < baseStart_1011389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011429 : List Nat := [1, 3, 1, 4, 1, 1, 2, 5, 1, 1, 3]
def baseStart_1011429 : Nat := 118140960795 + 1011429 * 2 ^ 59
def prefixEnd_1011429 : Nat := 4983230072969 + 3 ^ 40 * 1011429 * 2
def baseEnd_1011429 : Nat := 519349224896428513086029

theorem tailTrace_1011429 : CollatzResearch.WordTrace tailWord_1011429 prefixEnd_1011429 519349224896428513086029 := by
  unfold tailWord_1011429
  simp only [CollatzResearch.WordTrace]
  refine ⟨36889846252772946165909341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24593230835181964110606227 36889846252772946165909341)
  ·
    refine ⟨13833692344789854812216003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36889846252772946165909341 13833692344789854812216003)
    ·
      refine ⟨20750538517184782218324005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13833692344789854812216003 20750538517184782218324005)
      ·
        refine ⟨3890725971972146665935751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20750538517184782218324005 3890725971972146665935751)
        ·
          refine ⟨5836088957958219998903627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890725971972146665935751 5836088957958219998903627)
          ·
            refine ⟨8754133436937329998355441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836088957958219998903627 8754133436937329998355441)
            ·
              refine ⟨6565600077702997498766581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8754133436937329998355441 6565600077702997498766581)
              ·
                refine ⟨615525007284656015509367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6565600077702997498766581 615525007284656015509367)
                ·
                  refine ⟨923287510926984023264051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615525007284656015509367 923287510926984023264051)
                  ·
                    refine ⟨1384931266390476034896077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 923287510926984023264051 1384931266390476034896077)
                    ·
                      refine ⟨519349224896428513086029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384931266390476034896077 519349224896428513086029)
                      ·
                        rfl

theorem cell23_1011429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_1011429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011429 prefixEnd_1011429 := by exact prefixLift 1011429
  have htrace : WordTrace (prefixWord ++ tailWord_1011429) baseStart_1011429 baseEnd_1011429 := by
    simpa [prefixWord, tailWord_1011429, baseEnd_1011429] using wordTrace_append hprefix tailTrace_1011429
  have hstable : (prefixWord ++ tailWord_1011429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011429).length < 2 ^ (prefixWord ++ tailWord_1011429).sum := by decide
  have hdescent : baseEnd_1011429 < baseStart_1011429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011435 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 4]
def baseStart_1011435 : Nat := 118140960795 + 1011435 * 2 ^ 59
def prefixEnd_1011435 : Nat := 4983230072969 + 3 ^ 40 * 1011435 * 2
def baseEnd_1011435 : Nat := 519352305780355489611001

theorem tailTrace_1011435 : CollatzResearch.WordTrace tailWord_1011435 prefixEnd_1011435 519352305780355489611001 := by
  unfold tailWord_1011435
  simp only [CollatzResearch.WordTrace]
  refine ⟨36890065090751209190627759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24593376727167472793751839 36890065090751209190627759)
  ·
    refine ⟨55335097636126813785941639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36890065090751209190627759 55335097636126813785941639)
    ·
      refine ⟨83002646454190220678912459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55335097636126813785941639 83002646454190220678912459)
      ·
        refine ⟨124503969681285331018368689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83002646454190220678912459 124503969681285331018368689)
        ·
          refine ⟨93377977260963998263776517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124503969681285331018368689 93377977260963998263776517)
          ·
            refine ⟨17508370736430749674458097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93377977260963998263776517 17508370736430749674458097)
            ·
              refine ⟨13131278052323062255843573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17508370736430749674458097 13131278052323062255843573)
              ·
                refine ⟨1231057317405287086485335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13131278052323062255843573 1231057317405287086485335)
                ·
                  refine ⟨1846585976107930629728003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231057317405287086485335 1846585976107930629728003)
                  ·
                    refine ⟨2769878964161895944592005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1846585976107930629728003 2769878964161895944592005)
                    ·
                      refine ⟨519352305780355489611001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2769878964161895944592005 519352305780355489611001)
                      ·
                        rfl

theorem cell23_1011435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 4].length) (baseStart_1011435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011435 prefixEnd_1011435 := by exact prefixLift 1011435
  have htrace : WordTrace (prefixWord ++ tailWord_1011435) baseStart_1011435 baseEnd_1011435 := by
    simpa [prefixWord, tailWord_1011435, baseEnd_1011435] using wordTrace_append hprefix tailTrace_1011435
  have hstable : (prefixWord ++ tailWord_1011435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011435).length < 2 ^ (prefixWord ++ tailWord_1011435).sum := by decide
  have hdescent : baseEnd_1011435 < baseStart_1011435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011446 : List Nat := [5, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_1011446 : Nat := 118140960795 + 1011446 * 2 ^ 59
def prefixEnd_1011446 : Nat := 4983230072969 + 3 ^ 40 * 1011446 * 2
def baseEnd_1011446 : Nat := 519357954067554946573451

theorem tailTrace_1011446 : CollatzResearch.WordTrace tailWord_1011446 prefixEnd_1011446 519357954067554946573451 := by
  unfold tailWord_1011446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305654143356959879329887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24593644195807572046185461 2305654143356959879329887)
  ·
    refine ⟨3458481215035439818994831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2305654143356959879329887 3458481215035439818994831)
    ·
      refine ⟨5187721822553159728492247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458481215035439818994831 5187721822553159728492247)
      ·
        refine ⟨7781582733829739592738371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187721822553159728492247 7781582733829739592738371)
        ·
          refine ⟨11672374100744609389107557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781582733829739592738371 11672374100744609389107557)
          ·
            refine ⟨2188570143889614260457667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11672374100744609389107557 2188570143889614260457667)
            ·
              refine ⟨3282855215834421390686501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188570143889614260457667 3282855215834421390686501)
              ·
                refine ⟨615535352968954010753719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3282855215834421390686501 615535352968954010753719)
                ·
                  refine ⟨923303029453431016130579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615535352968954010753719 923303029453431016130579)
                  ·
                    refine ⟨1384954544180146524195869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 923303029453431016130579 1384954544180146524195869)
                    ·
                      refine ⟨519357954067554946573451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384954544180146524195869 519357954067554946573451)
                      ·
                        rfl

theorem cell23_1011446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_1011446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011446 prefixEnd_1011446 := by exact prefixLift 1011446
  have htrace : WordTrace (prefixWord ++ tailWord_1011446) baseStart_1011446 baseEnd_1011446 := by
    simpa [prefixWord, tailWord_1011446, baseEnd_1011446] using wordTrace_append hprefix tailTrace_1011446
  have hstable : (prefixWord ++ tailWord_1011446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011446).length < 2 ^ (prefixWord ++ tailWord_1011446).sum := by decide
  have hdescent : baseEnd_1011446 < baseStart_1011446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011448 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_1011448 : Nat := 118140960795 + 1011448 * 2 ^ 59
def prefixEnd_1011448 : Nat := 4983230072969 + 3 ^ 40 * 1011448 * 2
def baseEnd_1011448 : Nat := 519358981028863938748441

theorem tailTrace_1011448 : CollatzResearch.WordTrace tailWord_1011448 prefixEnd_1011448 519358981028863938748441 := by
  unfold tailWord_1011448
  simp only [CollatzResearch.WordTrace]
  refine ⟨18445269619852056205425499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24593692826469408273900665 18445269619852056205425499)
  ·
    refine ⟨27667904429778084308138249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18445269619852056205425499 27667904429778084308138249)
    ·
      refine ⟨20750928322333563231103687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27667904429778084308138249 20750928322333563231103687)
      ·
        refine ⟨31126392483500344846655531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20750928322333563231103687 31126392483500344846655531)
        ·
          refine ⟨46689588725250517269983297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31126392483500344846655531 46689588725250517269983297)
          ·
            refine ⟨35017191543937887952487473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46689588725250517269983297 35017191543937887952487473)
            ·
              refine ⟨26262893657953415964365605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35017191543937887952487473 26262893657953415964365605)
              ·
                refine ⟨4924292560866265493318551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26262893657953415964365605 4924292560866265493318551)
                ·
                  refine ⟨7386438841299398239977827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924292560866265493318551 7386438841299398239977827)
                  ·
                    refine ⟨11079658261949097359966741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7386438841299398239977827 11079658261949097359966741)
                    ·
                      refine ⟨519358981028863938748441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11079658261949097359966741 519358981028863938748441)
                      ·
                        rfl

theorem cell23_1011448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_1011448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011448 prefixEnd_1011448 := by exact prefixLift 1011448
  have htrace : WordTrace (prefixWord ++ tailWord_1011448) baseStart_1011448 baseEnd_1011448 := by
    simpa [prefixWord, tailWord_1011448, baseEnd_1011448] using wordTrace_append hprefix tailTrace_1011448
  have hstable : (prefixWord ++ tailWord_1011448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011448).length < 2 ^ (prefixWord ++ tailWord_1011448).sum := by decide
  have hdescent : baseEnd_1011448 < baseStart_1011448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011455 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 3]
def baseStart_1011455 : Nat := 118140960795 + 1011455 * 2 ^ 59
def prefixEnd_1011455 : Nat := 4983230072969 + 3 ^ 40 * 1011455 * 2
def baseEnd_1011455 : Nat := 519362575393445411360909

theorem tailTrace_1011455 : CollatzResearch.WordTrace tailWord_1011455 prefixEnd_1011455 519362575393445411360909 := by
  unfold tailWord_1011455
  simp only [CollatzResearch.WordTrace]
  refine ⟨36890794550678752606355819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24593863033785835070903879 36890794550678752606355819)
  ·
    refine ⟨55336191826018128909533729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36890794550678752606355819 55336191826018128909533729)
    ·
      refine ⟨41502143869513596682150297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55336191826018128909533729 41502143869513596682150297)
      ·
        refine ⟨31126607902135197511612723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41502143869513596682150297 31126607902135197511612723)
        ·
          refine ⟨46689911853202796267419085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31126607902135197511612723 46689911853202796267419085)
          ·
            refine ⟨17508716944951048600282157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46689911853202796267419085 17508716944951048600282157)
            ·
              refine ⟨6565768854356643225105809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17508716944951048600282157 6565768854356643225105809)
              ·
                refine ⟨4924326640767482418829357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6565768854356643225105809 4924326640767482418829357)
                ·
                  refine ⟨1846622490287805907061009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4924326640767482418829357 1846622490287805907061009)
                  ·
                    refine ⟨1384966867715854430295757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1846622490287805907061009 1384966867715854430295757)
                    ·
                      refine ⟨519362575393445411360909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1384966867715854430295757 519362575393445411360909)
                      ·
                        rfl

theorem cell23_1011455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_1011455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011455 prefixEnd_1011455 := by exact prefixLift 1011455
  have htrace : WordTrace (prefixWord ++ tailWord_1011455) baseStart_1011455 baseEnd_1011455 := by
    simpa [prefixWord, tailWord_1011455, baseEnd_1011455] using wordTrace_append hprefix tailTrace_1011455
  have hstable : (prefixWord ++ tailWord_1011455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011455).length < 2 ^ (prefixWord ++ tailWord_1011455).sum := by decide
  have hdescent : baseEnd_1011455 < baseStart_1011455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011489 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_1011489 : Nat := 118140960795 + 1011489 * 2 ^ 59
def prefixEnd_1011489 : Nat := 4983230072969 + 3 ^ 40 * 1011489 * 2
def baseEnd_1011489 : Nat := 519380033735698278335753

theorem tailTrace_1011489 : CollatzResearch.WordTrace tailWord_1011489 prefixEnd_1011489 519380033735698278335753 := by
  unfold tailWord_1011489
  simp only [CollatzResearch.WordTrace]
  refine ⟨36892034632555576413093521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24594689755037050942062347 36892034632555576413093521)
  ·
    refine ⟨27669025974416682309820141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36892034632555576413093521 27669025974416682309820141)
    ·
      refine ⟨10375884740406255866182553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27669025974416682309820141 10375884740406255866182553)
      ·
        refine ⟨7781913555304691899636915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10375884740406255866182553 7781913555304691899636915)
        ·
          refine ⟨11672870332957037849455373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781913555304691899636915 11672870332957037849455373)
          ·
            refine ⟨4377326374858889193545765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11672870332957037849455373 4377326374858889193545765)
            ·
              refine ⟨820748695286041723789831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4377326374858889193545765 820748695286041723789831)
              ·
                refine ⟨1231123042929062585684747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820748695286041723789831 1231123042929062585684747)
                ·
                  refine ⟨1846684564393593878527121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231123042929062585684747 1846684564393593878527121)
                  ·
                    refine ⟨1385013423295195408895341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1846684564393593878527121 1385013423295195408895341)
                    ·
                      refine ⟨519380033735698278335753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1385013423295195408895341 519380033735698278335753)
                      ·
                        rfl

theorem cell23_1011489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_1011489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011489 prefixEnd_1011489 := by exact prefixLift 1011489
  have htrace : WordTrace (prefixWord ++ tailWord_1011489) baseStart_1011489 baseEnd_1011489 := by
    simpa [prefixWord, tailWord_1011489, baseEnd_1011489] using wordTrace_append hprefix tailTrace_1011489
  have hstable : (prefixWord ++ tailWord_1011489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011489).length < 2 ^ (prefixWord ++ tailWord_1011489).sum := by decide
  have hdescent : baseEnd_1011489 < baseStart_1011489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011519 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 3]
def baseStart_1011519 : Nat := 118140960795 + 1011519 * 2 ^ 59
def prefixEnd_1011519 : Nat := 4983230072969 + 3 ^ 40 * 1011519 * 2
def baseEnd_1011519 : Nat := 519395438155333160960615

theorem tailTrace_1011519 : CollatzResearch.WordTrace tailWord_1011519 prefixEnd_1011519 519395438155333160960615 := by
  unfold tailWord_1011519
  simp only [CollatzResearch.WordTrace]
  refine ⟨36893128822446891536685611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24595419214964594357790407 36893128822446891536685611)
  ·
    refine ⟨55339693233670337305028417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36893128822446891536685611 55339693233670337305028417)
    ·
      refine ⟨41504769925252752978771313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55339693233670337305028417 41504769925252752978771313)
      ·
        refine ⟨31128577443939564734078485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41504769925252752978771313 31128577443939564734078485)
        ·
          refine ⟨1459152067684667096909929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31128577443939564734078485 1459152067684667096909929)
          ·
            refine ⟨1094364050763500322682447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459152067684667096909929 1094364050763500322682447)
            ·
              refine ⟨1641546076145250484023671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094364050763500322682447 1641546076145250484023671)
              ·
                refine ⟨2462319114217875726035507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641546076145250484023671 2462319114217875726035507)
                ·
                  refine ⟨3693478671326813589053261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462319114217875726035507 3693478671326813589053261)
                  ·
                    refine ⟨1385054501747555095894973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693478671326813589053261 1385054501747555095894973)
                    ·
                      refine ⟨519395438155333160960615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1385054501747555095894973 519395438155333160960615)
                      ·
                        rfl

theorem cell23_1011519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_1011519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011519 prefixEnd_1011519 := by exact prefixLift 1011519
  have htrace : WordTrace (prefixWord ++ tailWord_1011519) baseStart_1011519 baseEnd_1011519 := by
    simpa [prefixWord, tailWord_1011519, baseEnd_1011519] using wordTrace_append hprefix tailTrace_1011519
  have hstable : (prefixWord ++ tailWord_1011519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011519).length < 2 ^ (prefixWord ++ tailWord_1011519).sum := by decide
  have hdescent : baseEnd_1011519 < baseStart_1011519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011526 : List Nat := [6, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1011526 : Nat := 118140960795 + 1011526 * 2 ^ 59
def prefixEnd_1011526 : Nat := 4983230072969 + 3 ^ 40 * 1011526 * 2
def baseEnd_1011526 : Nat := 19237001204441282724929

theorem tailTrace_1011526 : CollatzResearch.WordTrace tailWord_1011526 prefixEnd_1011526 19237001204441282724929 := by
  unfold tailWord_1011526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152918254169422866630951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24595589422281021154793621 1152918254169422866630951)
  ·
    refine ⟨1729377381254134299946427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1152918254169422866630951 1729377381254134299946427)
    ·
      refine ⟨2594066071881201449919641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729377381254134299946427 2594066071881201449919641)
      ·
        refine ⟨1945549553910901087439731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2594066071881201449919641 1945549553910901087439731)
        ·
          refine ⟨2918324330866351631159597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945549553910901087439731 2918324330866351631159597)
          ·
            refine ⟨1094371624074881861684849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2918324330866351631159597 1094371624074881861684849)
            ·
              refine ⟨820778718056161396263637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094371624074881861684849 820778718056161396263637)
              ·
                refine ⟨19237001204441282724929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 820778718056161396263637 19237001204441282724929)
                ·
                  rfl

theorem cell23_1011526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1011526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011526 prefixEnd_1011526 := by exact prefixLift 1011526
  have htrace : WordTrace (prefixWord ++ tailWord_1011526) baseStart_1011526 baseEnd_1011526 := by
    simpa [prefixWord, tailWord_1011526, baseEnd_1011526] using wordTrace_append hprefix tailTrace_1011526
  have hstable : (prefixWord ++ tailWord_1011526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011526).length < 2 ^ (prefixWord ++ tailWord_1011526).sum := by decide
  have hdescent : baseEnd_1011526 < baseStart_1011526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011529 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 1, 3, 2]
def baseStart_1011529 : Nat := 118140960795 + 1011529 * 2 ^ 59
def prefixEnd_1011529 : Nat := 4983230072969 + 3 ^ 40 * 1011529 * 2
def baseEnd_1011529 : Nat := 519400572961878121835569

theorem tailTrace_1011529 : CollatzResearch.WordTrace tailWord_1011529 prefixEnd_1011529 519400572961878121835569 := by
  unfold tailWord_1011529
  simp only [CollatzResearch.WordTrace]
  refine ⟨36893493552410663244549641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24595662368273775496366427 36893493552410663244549641)
  ·
    refine ⟨27670120164307997433412231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36893493552410663244549641 27670120164307997433412231)
    ·
      refine ⟨41505180246461996150118347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27670120164307997433412231 41505180246461996150118347)
      ·
        refine ⟨62257770369692994225177521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41505180246461996150118347 62257770369692994225177521)
        ·
          refine ⟨46693327777269745668883141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62257770369692994225177521 46693327777269745668883141)
          ·
            refine ⟨8754998958238077312915589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46693327777269745668883141 8754998958238077312915589)
            ·
              refine ⟨1641562304669639496171673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8754998958238077312915589 1641562304669639496171673)
              ·
                refine ⟨1231171728502229622128755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641562304669639496171673 1231171728502229622128755)
                ·
                  refine ⟨1846757592753344433193133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231171728502229622128755 1846757592753344433193133)
                  ·
                    refine ⟨692534097282504162447425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846757592753344433193133 692534097282504162447425)
                    ·
                      refine ⟨519400572961878121835569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692534097282504162447425 519400572961878121835569)
                      ·
                        rfl

theorem cell23_1011529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 3, 2].length) (baseStart_1011529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011529 prefixEnd_1011529 := by exact prefixLift 1011529
  have htrace : WordTrace (prefixWord ++ tailWord_1011529) baseStart_1011529 baseEnd_1011529 := by
    simpa [prefixWord, tailWord_1011529, baseEnd_1011529] using wordTrace_append hprefix tailTrace_1011529
  have hstable : (prefixWord ++ tailWord_1011529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011529).length < 2 ^ (prefixWord ++ tailWord_1011529).sum := by decide
  have hdescent : baseEnd_1011529 < baseStart_1011529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011545 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_1011545 : Nat := 118140960795 + 1011545 * 2 ^ 59
def prefixEnd_1011545 : Nat := 4983230072969 + 3 ^ 40 * 1011545 * 2
def baseEnd_1011545 : Nat := 519408788652350059235495

theorem tailTrace_1011545 : CollatzResearch.WordTrace tailWord_1011545 prefixEnd_1011545 519408788652350059235495 := by
  unfold tailWord_1011545
  simp only [CollatzResearch.WordTrace]
  refine ⟨36894077120352697977132089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24596051413568465318088059 36894077120352697977132089)
  ·
    refine ⟨27670557840264523482849067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36894077120352697977132089 27670557840264523482849067)
    ·
      refine ⟨41505836760396785224273601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27670557840264523482849067 41505836760396785224273601)
      ·
        refine ⟨31129377570297588918205201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41505836760396785224273601 31129377570297588918205201)
        ·
          refine ⟨23347033177723191688653901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31129377570297588918205201 23347033177723191688653901)
          ·
            refine ⟨8755137441646196883245213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23347033177723191688653901 8755137441646196883245213)
            ·
              refine ⟨3283176540617323831216955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8755137441646196883245213 3283176540617323831216955)
              ·
                refine ⟨4924764810925985746825433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283176540617323831216955 4924764810925985746825433)
                ·
                  refine ⟨3693573608194489310119075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4924764810925985746825433 3693573608194489310119075)
                  ·
                    refine ⟨5540360412291733965178613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3693573608194489310119075 5540360412291733965178613)
                    ·
                      refine ⟨519408788652350059235495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5540360412291733965178613 519408788652350059235495)
                      ·
                        rfl

theorem cell23_1011545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_1011545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011545 prefixEnd_1011545 := by exact prefixLift 1011545
  have htrace : WordTrace (prefixWord ++ tailWord_1011545) baseStart_1011545 baseEnd_1011545 := by
    simpa [prefixWord, tailWord_1011545, baseEnd_1011545] using wordTrace_append hprefix tailTrace_1011545
  have hstable : (prefixWord ++ tailWord_1011545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011545).length < 2 ^ (prefixWord ++ tailWord_1011545).sum := by decide
  have hdescent : baseEnd_1011545 < baseStart_1011545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011559 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_1011559 : Nat := 118140960795 + 1011559 * 2 ^ 59
def prefixEnd_1011559 : Nat := 4983230072969 + 3 ^ 40 * 1011559 * 2
def baseEnd_1011559 : Nat := 519415977381513004460431

theorem tailTrace_1011559 : CollatzResearch.WordTrace tailWord_1011559 prefixEnd_1011559 519415977381513004460431 := by
  unfold tailWord_1011559
  simp only [CollatzResearch.WordTrace]
  refine ⟨36894587742301978368141731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24596391828201318912094487 36894587742301978368141731)
  ·
    refine ⟨55341881613452967552212597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36894587742301978368141731 55341881613452967552212597)
    ·
      refine ⟨5188301401261215708019931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55341881613452967552212597 5188301401261215708019931)
      ·
        refine ⟨7782452101891823562029897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188301401261215708019931 7782452101891823562029897)
        ·
          refine ⟨5836839076418867671522423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7782452101891823562029897 5836839076418867671522423)
          ·
            refine ⟨8755258614628301507283635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836839076418867671522423 8755258614628301507283635)
            ·
              refine ⟨13132887921942452260925453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755258614628301507283635 13132887921942452260925453)
              ·
                refine ⟨4924832970728419597847045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13132887921942452260925453 4924832970728419597847045)
                ·
                  refine ⟨923406182011578674596321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4924832970728419597847045 923406182011578674596321)
                  ·
                    refine ⟨692554636508684005947241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 923406182011578674596321 692554636508684005947241)
                    ·
                      refine ⟨519415977381513004460431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692554636508684005947241 519415977381513004460431)
                      ·
                        rfl

theorem cell23_1011559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_1011559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011559 prefixEnd_1011559 := by exact prefixLift 1011559
  have htrace : WordTrace (prefixWord ++ tailWord_1011559) baseStart_1011559 baseEnd_1011559 := by
    simpa [prefixWord, tailWord_1011559, baseEnd_1011559] using wordTrace_append hprefix tailTrace_1011559
  have hstable : (prefixWord ++ tailWord_1011559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011559).length < 2 ^ (prefixWord ++ tailWord_1011559).sum := by decide
  have hdescent : baseEnd_1011559 < baseStart_1011559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011605 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1011605 : Nat := 118140960795 + 1011605 * 2 ^ 59
def prefixEnd_1011605 : Nat := 4983230072969 + 3 ^ 40 * 1011605 * 2
def baseEnd_1011605 : Nat := 519439597491619824485219

theorem tailTrace_1011605 : CollatzResearch.WordTrace tailWord_1011605 prefixEnd_1011605 519439597491619824485219 := by
  unfold tailWord_1011605
  simp only [CollatzResearch.WordTrace]
  refine ⟨36896265500135328224316269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24597510333423552149544179 36896265500135328224316269)
  ·
    refine ⟨13836099562550748084118601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36896265500135328224316269 13836099562550748084118601)
    ·
      refine ⟨10377074671913061063088951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13836099562550748084118601 10377074671913061063088951)
      ·
        refine ⟨15565612007869591594633427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377074671913061063088951 15565612007869591594633427)
        ·
          refine ⟨23348418011804387391950141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15565612007869591594633427 23348418011804387391950141)
          ·
            refine ⟨8755656754426645271981303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23348418011804387391950141 8755656754426645271981303)
            ·
              refine ⟨13133485131639967907971955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755656754426645271981303 13133485131639967907971955)
              ·
                refine ⟨19700227697459951861957933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13133485131639967907971955 19700227697459951861957933)
                ·
                  refine ⟨7387585386547481948234225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19700227697459951861957933 7387585386547481948234225)
                  ·
                    refine ⟨5540689039910611461175669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387585386547481948234225 5540689039910611461175669)
                    ·
                      refine ⟨519439597491619824485219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5540689039910611461175669 519439597491619824485219)
                      ·
                        rfl

theorem cell23_1011605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1011605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011605 prefixEnd_1011605 := by exact prefixLift 1011605
  have htrace : WordTrace (prefixWord ++ tailWord_1011605) baseStart_1011605 baseEnd_1011605 := by
    simpa [prefixWord, tailWord_1011605, baseEnd_1011605] using wordTrace_append hprefix tailTrace_1011605
  have hstable : (prefixWord ++ tailWord_1011605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011605).length < 2 ^ (prefixWord ++ tailWord_1011605).sum := by decide
  have hdescent : baseEnd_1011605 < baseStart_1011605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011655 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 8]
def baseStart_1011655 : Nat := 118140960795 + 1011655 * 2 ^ 59
def prefixEnd_1011655 : Nat := 4983230072969 + 3 ^ 40 * 1011655 * 2
def baseEnd_1011655 : Nat := 57718363502704958762221

theorem tailTrace_1011655 : CollatzResearch.WordTrace tailWord_1011655 prefixEnd_1011655 57718363502704958762221 := by
  unfold tailWord_1011655
  simp only [CollatzResearch.WordTrace]
  refine ⟨36898089149954186763636419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24598726099969457842424279 36898089149954186763636419)
  ·
    refine ⟨55347133724931280145454629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36898089149954186763636419 55347133724931280145454629)
    ·
      refine ⟨10377587573424615027272743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55347133724931280145454629 10377587573424615027272743)
      ·
        refine ⟨15566381360136922540909115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377587573424615027272743 15566381360136922540909115)
        ·
          refine ⟨23349572040205383811363673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15566381360136922540909115 23349572040205383811363673)
          ·
            refine ⟨17512179030154037858522755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23349572040205383811363673 17512179030154037858522755)
            ·
              refine ⟨26268268545231056787784133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17512179030154037858522755 26268268545231056787784133)
              ·
                refine ⟨4925300352230823147709525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26268268545231056787784133 4925300352230823147709525)
                ·
                  refine ⟨57718363502704958762221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4925300352230823147709525 57718363502704958762221)
                  ·
                    rfl

theorem cell23_1011655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 8].length) (baseStart_1011655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011655 prefixEnd_1011655 := by exact prefixLift 1011655
  have htrace : WordTrace (prefixWord ++ tailWord_1011655) baseStart_1011655 baseEnd_1011655 := by
    simpa [prefixWord, tailWord_1011655, baseEnd_1011655] using wordTrace_append hprefix tailTrace_1011655
  have hstable : (prefixWord ++ tailWord_1011655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011655).length < 2 ^ (prefixWord ++ tailWord_1011655).sum := by decide
  have hdescent : baseEnd_1011655 < baseStart_1011655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011709 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_1011709 : Nat := 118140960795 + 1011709 * 2 ^ 59
def prefixEnd_1011709 : Nat := 4983230072969 + 3 ^ 40 * 1011709 * 2
def baseEnd_1011709 : Nat := 519492999479687417584741

theorem tailTrace_1011709 : CollatzResearch.WordTrace tailWord_1011709 prefixEnd_1011709 519492999479687417584741 := by
  unfold tailWord_1011709
  simp only [CollatzResearch.WordTrace]
  refine ⟨36900058691758553986102181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24600039127839035990734787 36900058691758553986102181)
  ·
    refine ⟨6918761004704728872394159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36900058691758553986102181 6918761004704728872394159)
    ·
      refine ⟨10378141507057093308591239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6918761004704728872394159 10378141507057093308591239)
      ·
        refine ⟨15567212260585639962886859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10378141507057093308591239 15567212260585639962886859)
        ·
          refine ⟨23350818390878459944330289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15567212260585639962886859 23350818390878459944330289)
          ·
            refine ⟨17513113793158844958247717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23350818390878459944330289 17513113793158844958247717)
            ·
              refine ⟨3283708836217283429671447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17513113793158844958247717 3283708836217283429671447)
              ·
                refine ⟨4925563254325925144507171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283708836217283429671447 4925563254325925144507171)
                ·
                  refine ⟨7388344881488887716760757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925563254325925144507171 7388344881488887716760757)
                  ·
                    refine ⟨692657332639583223446321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7388344881488887716760757 692657332639583223446321)
                    ·
                      refine ⟨519492999479687417584741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 692657332639583223446321 519492999479687417584741)
                      ·
                        rfl

theorem cell23_1011709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_1011709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011709 prefixEnd_1011709 := by exact prefixLift 1011709
  have htrace : WordTrace (prefixWord ++ tailWord_1011709) baseStart_1011709 baseEnd_1011709 := by
    simpa [prefixWord, tailWord_1011709, baseEnd_1011709] using wordTrace_append hprefix tailTrace_1011709
  have hstable : (prefixWord ++ tailWord_1011709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011709).length < 2 ^ (prefixWord ++ tailWord_1011709).sum := by decide
  have hdescent : baseEnd_1011709 < baseStart_1011709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011710 : List Nat := [4, 2, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1011710 : Nat := 118140960795 + 1011710 * 2 ^ 59
def prefixEnd_1011710 : Nat := 4983230072969 + 3 ^ 40 * 1011710 * 2
def baseEnd_1011710 : Nat := 173164504320113971224079

theorem tailTrace_1011710 : CollatzResearch.WordTrace tailWord_1011710 prefixEnd_1011710 173164504320113971224079 := by
  unfold tailWord_1011710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612511895594366394611073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24600063443169954104592389 4612511895594366394611073)
  ·
    refine ⟨3459383921695774795958305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4612511895594366394611073 3459383921695774795958305)
    ·
      refine ⟨2594537941271831096968729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3459383921695774795958305 2594537941271831096968729)
      ·
        refine ⟨1945903455953873322726547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2594537941271831096968729 1945903455953873322726547)
        ·
          refine ⟨2918855183930809984089821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945903455953873322726547 2918855183930809984089821)
          ·
            refine ⟨1094570693974053744033683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2918855183930809984089821 1094570693974053744033683)
            ·
              refine ⟨1641856040961080616050525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094570693974053744033683 1641856040961080616050525)
              ·
                refine ⟨615696015360405231018947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1641856040961080616050525 615696015360405231018947)
                ·
                  refine ⟨923544023040607846528421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615696015360405231018947 923544023040607846528421)
                  ·
                    refine ⟨173164504320113971224079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 923544023040607846528421 173164504320113971224079)
                    ·
                      rfl

theorem cell23_1011710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1011710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011710 prefixEnd_1011710 := by exact prefixLift 1011710
  have htrace : WordTrace (prefixWord ++ tailWord_1011710) baseStart_1011710 baseEnd_1011710 := by
    simpa [prefixWord, tailWord_1011710, baseEnd_1011710] using wordTrace_append hprefix tailTrace_1011710
  have hstable : (prefixWord ++ tailWord_1011710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011710).length < 2 ^ (prefixWord ++ tailWord_1011710).sum := by decide
  have hdescent : baseEnd_1011710 < baseStart_1011710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1011719 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 1, 5]
def baseStart_1011719 : Nat := 118140960795 + 1011719 * 2 ^ 59
def prefixEnd_1011719 : Nat := 4983230072969 + 3 ^ 40 * 1011719 * 2
def baseEnd_1011719 : Nat := 173166044762077459486565

theorem tailTrace_1011719 : CollatzResearch.WordTrace tailWord_1011719 prefixEnd_1011719 173166044762077459486565 := by
  unfold tailWord_1011719
  simp only [CollatzResearch.WordTrace]
  refine ⟨36900423421722325693966211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24600282281148217129310807 36900423421722325693966211)
  ·
    refine ⟨55350635132583488540949317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36900423421722325693966211 55350635132583488540949317)
    ·
      refine ⟨10378244087359404101427997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55350635132583488540949317 10378244087359404101427997)
      ·
        refine ⟨3891841532759776538035499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10378244087359404101427997 3891841532759776538035499)
        ·
          refine ⟨5837762299139664807053249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3891841532759776538035499 5837762299139664807053249)
          ·
            refine ⟨4378321724354748605289937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5837762299139664807053249 4378321724354748605289937)
            ·
              refine ⟨3283741293266061453967453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4378321724354748605289937 3283741293266061453967453)
              ·
                refine ⟨1231402984974773045237795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3283741293266061453967453 1231402984974773045237795)
                ·
                  refine ⟨1847104477462159567856693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231402984974773045237795 1847104477462159567856693)
                  ·
                    refine ⟨173166044762077459486565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1847104477462159567856693 173166044762077459486565)
                    ·
                      rfl

theorem cell23_1011719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_1011719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1011719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1011719 prefixEnd_1011719 := by exact prefixLift 1011719
  have htrace : WordTrace (prefixWord ++ tailWord_1011719) baseStart_1011719 baseEnd_1011719 := by
    simpa [prefixWord, tailWord_1011719, baseEnd_1011719] using wordTrace_append hprefix tailTrace_1011719
  have hstable : (prefixWord ++ tailWord_1011719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1011719).length < 2 ^ (prefixWord ++ tailWord_1011719).sum := by decide
  have hdescent : baseEnd_1011719 < baseStart_1011719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1011719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
