import V185TrunkScan23Chunk0504

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2987504 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_2987504 : Nat := 118140960795 + 2987504 * 2 ^ 59
def prefixEnd_2987504 : Nat := 4983230072969 + 3 ^ 40 * 2987504 * 2
def baseEnd_2987504 : Nat := 1534025509229784610560725

theorem tailTrace_2987504 : CollatzResearch.WordTrace tailWord_2987504 prefixEnd_2987504 1534025509229784610560725 := by
  unfold tailWord_2987504
  simp only [CollatzResearch.WordTrace]
  refine ⟨54481611284395353953608783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72642148379193805271478377 54481611284395353953608783)
  ·
    refine ⟨81722416926593030930413175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54481611284395353953608783 81722416926593030930413175)
    ·
      refine ⟨122583625389889546395619763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81722416926593030930413175 122583625389889546395619763)
      ·
        refine ⟨183875438084834319593429645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122583625389889546395619763 183875438084834319593429645)
        ·
          refine ⟨68953289281812869847536117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183875438084834319593429645 68953289281812869847536117)
          ·
            refine ⟨6464370870169956548206511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68953289281812869847536117 6464370870169956548206511)
            ·
              refine ⟨9696556305254934822309767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6464370870169956548206511 9696556305254934822309767)
              ·
                refine ⟨14544834457882402233464651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9696556305254934822309767 14544834457882402233464651)
                ·
                  refine ⟨21817251686823603350196977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14544834457882402233464651 21817251686823603350196977)
                  ·
                    refine ⟨16362938765117702512647733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21817251686823603350196977 16362938765117702512647733)
                    ·
                      refine ⟨1534025509229784610560725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16362938765117702512647733 1534025509229784610560725)
                      ·
                        rfl

theorem cell23_2987504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_2987504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987504 prefixEnd_2987504 := by exact prefixLift 2987504
  have htrace : WordTrace (prefixWord ++ tailWord_2987504) baseStart_2987504 baseEnd_2987504 := by
    simpa [prefixWord, tailWord_2987504, baseEnd_2987504] using wordTrace_append hprefix tailTrace_2987504
  have hstable : (prefixWord ++ tailWord_2987504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987504).length < 2 ^ (prefixWord ++ tailWord_2987504).sum := by decide
  have hdescent : baseEnd_2987504 < baseStart_2987504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987507 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 2, 8]
def baseStart_2987507 : Nat := 118140960795 + 2987507 * 2 ^ 59
def prefixEnd_2987507 : Nat := 4983230072969 + 3 ^ 40 * 2987507 * 2
def baseEnd_2987507 : Nat := 511342349890582699607737

theorem tailTrace_2987507 : CollatzResearch.WordTrace tailWord_2987507 prefixEnd_2987507 511342349890582699607737 := by
  unfold tailWord_2987507
  simp only [CollatzResearch.WordTrace]
  refine ⟨108963331987779839419576775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72642221325186559613051183 108963331987779839419576775)
  ·
    refine ⟨163444997981669759129365163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108963331987779839419576775 163444997981669759129365163)
    ·
      refine ⟨245167496972504638694047745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163444997981669759129365163 245167496972504638694047745)
      ·
        refine ⟨183875622729378479020535809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245167496972504638694047745 183875622729378479020535809)
        ·
          refine ⟨137906717047033859265401857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183875622729378479020535809 137906717047033859265401857)
          ·
            refine ⟨103430037785275394449051393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137906717047033859265401857 103430037785275394449051393)
            ·
              refine ⟨77572528338956545836788545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103430037785275394449051393 77572528338956545836788545)
              ·
                refine ⟨58179396254217409377591409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77572528338956545836788545 58179396254217409377591409)
                ·
                  refine ⟨43634547190663057033193557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58179396254217409377591409 43634547190663057033193557)
                  ·
                    refine ⟨511342349890582699607737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43634547190663057033193557 511342349890582699607737)
                    ·
                      rfl

theorem cell23_2987507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 8].length) (baseStart_2987507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987507 prefixEnd_2987507 := by exact prefixLift 2987507
  have htrace : WordTrace (prefixWord ++ tailWord_2987507) baseStart_2987507 baseEnd_2987507 := by
    simpa [prefixWord, tailWord_2987507, baseEnd_2987507] using wordTrace_append hprefix tailTrace_2987507
  have hstable : (prefixWord ++ tailWord_2987507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987507).length < 2 ^ (prefixWord ++ tailWord_2987507).sum := by decide
  have hdescent : baseEnd_2987507 < baseStart_2987507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987509 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2987509 : Nat := 118140960795 + 2987509 * 2 ^ 59
def prefixEnd_2987509 : Nat := 4983230072969 + 3 ^ 40 * 2987509 * 2
def baseEnd_2987509 : Nat := 1534028076633057090998203

theorem tailTrace_2987509 : CollatzResearch.WordTrace tailWord_2987509 prefixEnd_2987509 1534028076633057090998203 := by
  unfold tailWord_2987509
  simp only [CollatzResearch.WordTrace]
  refine ⟨108963404933772593761149581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72642269955848395840766387 108963404933772593761149581)
  ·
    refine ⟨40861276850164722660431093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108963404933772593761149581 40861276850164722660431093)
    ·
      refine ⟨3830744704702942749415415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40861276850164722660431093 3830744704702942749415415)
      ·
        refine ⟨5746117057054414124123123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830744704702942749415415 5746117057054414124123123)
        ·
          refine ⟨8619175585581621186184685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5746117057054414124123123 8619175585581621186184685)
          ·
            refine ⟨3232190844593107944819257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8619175585581621186184685 3232190844593107944819257)
            ·
              refine ⟨2424143133444830958614443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232190844593107944819257 2424143133444830958614443)
              ·
                refine ⟨3636214700167246437921665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424143133444830958614443 3636214700167246437921665)
                ·
                  refine ⟨2727161025125434828441249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3636214700167246437921665 2727161025125434828441249)
                  ·
                    refine ⟨2045370768844076121330937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727161025125434828441249 2045370768844076121330937)
                    ·
                      refine ⟨1534028076633057090998203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045370768844076121330937 1534028076633057090998203)
                      ·
                        rfl

theorem cell23_2987509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2987509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987509 prefixEnd_2987509 := by exact prefixLift 2987509
  have htrace : WordTrace (prefixWord ++ tailWord_2987509) baseStart_2987509 baseEnd_2987509 := by
    simpa [prefixWord, tailWord_2987509, baseEnd_2987509] using wordTrace_append hprefix tailTrace_2987509
  have hstable : (prefixWord ++ tailWord_2987509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987509).length < 2 ^ (prefixWord ++ tailWord_2987509).sum := by decide
  have hdescent : baseEnd_2987509 < baseStart_2987509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987514 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_2987514 : Nat := 118140960795 + 2987514 * 2 ^ 59
def prefixEnd_2987514 : Nat := 4983230072969 + 3 ^ 40 * 2987514 * 2
def baseEnd_2987514 : Nat := 1534030644036329571435679

theorem tailTrace_2987514 : CollatzResearch.WordTrace tailWord_2987514 prefixEnd_2987514 1534030644036329571435679 := by
  unfold tailWord_2987514
  simp only [CollatzResearch.WordTrace]
  refine ⟨27240896824688619903770399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72642391532502986410054397 27240896824688619903770399)
  ·
    refine ⟨40861345237032929855655599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27240896824688619903770399 40861345237032929855655599)
    ·
      refine ⟨61292017855549394783483399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40861345237032929855655599 61292017855549394783483399)
      ·
        refine ⟨91938026783324092175225099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61292017855549394783483399 91938026783324092175225099)
        ·
          refine ⟨137907040174986138262837649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91938026783324092175225099 137907040174986138262837649)
          ·
            refine ⟨103430280131239603697128237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137907040174986138262837649 103430280131239603697128237)
            ·
              refine ⟨38786355049214851386423089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103430280131239603697128237 38786355049214851386423089)
              ·
                refine ⟨29089766286911138539817317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38786355049214851386423089 29089766286911138539817317)
                ·
                  refine ⟨5454331178795838476215747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29089766286911138539817317 5454331178795838476215747)
                  ·
                    refine ⟨8181496768193757714323621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5454331178795838476215747 8181496768193757714323621)
                    ·
                      refine ⟨1534030644036329571435679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8181496768193757714323621 1534030644036329571435679)
                      ·
                        rfl

theorem cell23_2987514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_2987514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987514 prefixEnd_2987514 := by exact prefixLift 2987514
  have htrace : WordTrace (prefixWord ++ tailWord_2987514) baseStart_2987514 baseEnd_2987514 := by
    simpa [prefixWord, tailWord_2987514, baseEnd_2987514] using wordTrace_append hprefix tailTrace_2987514
  have hstable : (prefixWord ++ tailWord_2987514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987514).length < 2 ^ (prefixWord ++ tailWord_2987514).sum := by decide
  have hdescent : baseEnd_2987514 < baseStart_2987514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987551 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 3]
def baseStart_2987551 : Nat := 118140960795 + 2987551 * 2 ^ 59
def prefixEnd_2987551 : Nat := 4983230072969 + 3 ^ 40 * 2987551 * 2
def baseEnd_2987551 : Nat := 1534049642820545926673009

theorem tailTrace_2987551 : CollatzResearch.WordTrace tailWord_2987551 prefixEnd_2987551 1534049642820545926673009 := by
  unfold tailWord_2987551
  simp only [CollatzResearch.WordTrace]
  refine ⟨108964936799620434934178507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72643291199746956622785671 108964936799620434934178507)
  ·
    refine ⟨163447405199430652401267761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108964936799620434934178507 163447405199430652401267761)
    ·
      refine ⟨122585553899572989300950821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163447405199430652401267761 122585553899572989300950821)
      ·
        refine ⟨22984791356169935493928279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122585553899572989300950821 22984791356169935493928279)
        ·
          refine ⟨34477187034254903240892419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22984791356169935493928279 34477187034254903240892419)
          ·
            refine ⟨51715780551382354861338629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34477187034254903240892419 51715780551382354861338629)
            ·
              refine ⟨9696708853384191536500993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51715780551382354861338629 9696708853384191536500993)
              ·
                refine ⟨7272531640038143652375745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9696708853384191536500993 7272531640038143652375745)
                ·
                  refine ⟨5454398730028607739281809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7272531640038143652375745 5454398730028607739281809)
                  ·
                    refine ⟨4090799047521455804461357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5454398730028607739281809 4090799047521455804461357)
                    ·
                      refine ⟨1534049642820545926673009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4090799047521455804461357 1534049642820545926673009)
                      ·
                        rfl

theorem cell23_2987551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_2987551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987551 prefixEnd_2987551 := by exact prefixLift 2987551
  have htrace : WordTrace (prefixWord ++ tailWord_2987551) baseStart_2987551 baseEnd_2987551 := by
    simpa [prefixWord, tailWord_2987551, baseEnd_2987551] using wordTrace_append hprefix tailTrace_2987551
  have hstable : (prefixWord ++ tailWord_2987551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987551).length < 2 ^ (prefixWord ++ tailWord_2987551).sum := by decide
  have hdescent : baseEnd_2987551 < baseStart_2987551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987554 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 8]
def baseStart_2987554 : Nat := 118140960795 + 2987554 * 2 ^ 59
def prefixEnd_2987554 : Nat := 4983230072969 + 3 ^ 40 * 2987554 * 2
def baseEnd_2987554 : Nat := 170450131473612157215055

theorem tailTrace_2987554 : CollatzResearch.WordTrace tailWord_2987554 prefixEnd_2987554 170450131473612157215055 := by
  unfold tailWord_2987554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27241261554652391611634429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72643364145739710964358477 27241261554652391611634429)
  ·
    refine ⟨10215473082994646854362911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27241261554652391611634429 10215473082994646854362911)
    ·
      refine ⟨15323209624491970281544367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10215473082994646854362911 15323209624491970281544367)
      ·
        refine ⟨22984814436737955422316551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15323209624491970281544367 22984814436737955422316551)
        ·
          refine ⟨34477221655106933133474827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22984814436737955422316551 34477221655106933133474827)
          ·
            refine ⟨51715832482660399700212241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34477221655106933133474827 51715832482660399700212241)
            ·
              refine ⟨38786874361995299775159181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51715832482660399700212241 38786874361995299775159181)
              ·
                refine ⟨14545077885748237415684693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38786874361995299775159181 14545077885748237415684693)
                ·
                  refine ⟨170450131473612157215055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14545077885748237415684693 170450131473612157215055)
                  ·
                    rfl

theorem cell23_2987554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_2987554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987554 prefixEnd_2987554 := by exact prefixLift 2987554
  have htrace : WordTrace (prefixWord ++ tailWord_2987554) baseStart_2987554 baseEnd_2987554 := by
    simpa [prefixWord, tailWord_2987554, baseEnd_2987554] using wordTrace_append hprefix tailTrace_2987554
  have hstable : (prefixWord ++ tailWord_2987554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987554).length < 2 ^ (prefixWord ++ tailWord_2987554).sum := by decide
  have hdescent : baseEnd_2987554 < baseStart_2987554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987564 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_2987564 : Nat := 118140960795 + 2987564 * 2 ^ 59
def prefixEnd_2987564 : Nat := 4983230072969 + 3 ^ 40 * 2987564 * 2
def baseEnd_2987564 : Nat := 1534056318069054375810449

theorem tailTrace_2987564 : CollatzResearch.WordTrace tailWord_2987564 prefixEnd_2987564 1534056318069054375810449 := by
  unfold tailWord_2987564
  simp only [CollatzResearch.WordTrace]
  refine ⟨54482705474286669077200873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72643607299048892102934497 54482705474286669077200873)
  ·
    refine ⟨40862029105715001807900655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54482705474286669077200873 40862029105715001807900655)
    ·
      refine ⟨61293043658572502711850983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40862029105715001807900655 61293043658572502711850983)
      ·
        refine ⟨91939565487858754067776475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61293043658572502711850983 91939565487858754067776475)
        ·
          refine ⟨137909348231788131101664713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91939565487858754067776475 137909348231788131101664713)
          ·
            refine ⟨103432011173841098326248535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137909348231788131101664713 103432011173841098326248535)
            ·
              refine ⟨155148016760761647489372803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103432011173841098326248535 155148016760761647489372803)
              ·
                refine ⟨232722025141142471234059205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155148016760761647489372803 232722025141142471234059205)
                ·
                  refine ⟨43635379713964213356386101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232722025141142471234059205 43635379713964213356386101)
                  ·
                    refine ⟨4090816848184145002161197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43635379713964213356386101 4090816848184145002161197)
                    ·
                      refine ⟨1534056318069054375810449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4090816848184145002161197 1534056318069054375810449)
                      ·
                        rfl

theorem cell23_2987564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_2987564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987564 prefixEnd_2987564 := by exact prefixLift 2987564
  have htrace : WordTrace (prefixWord ++ tailWord_2987564) baseStart_2987564 baseEnd_2987564 := by
    simpa [prefixWord, tailWord_2987564, baseEnd_2987564] using wordTrace_append hprefix tailTrace_2987564
  have hstable : (prefixWord ++ tailWord_2987564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987564).length < 2 ^ (prefixWord ++ tailWord_2987564).sum := by decide
  have hdescent : baseEnd_2987564 < baseStart_2987564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987601 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 1, 5]
def baseStart_2987601 : Nat := 118140960795 + 2987601 * 2 ^ 59
def prefixEnd_2987601 : Nat := 4983230072969 + 3 ^ 40 * 2987601 * 2
def baseEnd_2987601 : Nat := 511358438951090243682593

theorem tailTrace_2987601 : CollatzResearch.WordTrace tailWord_2987601 prefixEnd_2987601 511358438951090243682593 := by
  unfold tailWord_2987601
  simp only [CollatzResearch.WordTrace]
  refine ⟨108966760449439293473498657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72644506966292862315665771 108966760449439293473498657)
  ·
    refine ⟨81725070337079470105123993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108966760449439293473498657 81725070337079470105123993)
    ·
      refine ⟨61293802752809602578842995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81725070337079470105123993 61293802752809602578842995)
      ·
        refine ⟨91940704129214403868264493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61293802752809602578842995 91940704129214403868264493)
        ·
          refine ⟨34477764048455401450599185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91940704129214403868264493 34477764048455401450599185)
          ·
            refine ⟨25858323036341551087949389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34477764048455401450599185 25858323036341551087949389)
            ·
              refine ⟨9696871138628081657981021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25858323036341551087949389 9696871138628081657981021)
              ·
                refine ⟨3636326676985530621742883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9696871138628081657981021 3636326676985530621742883)
                ·
                  refine ⟨5454490015478295932614325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636326676985530621742883 5454490015478295932614325)
                  ·
                    refine ⟨511358438951090243682593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5454490015478295932614325 511358438951090243682593)
                    ·
                      rfl

theorem cell23_2987601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_2987601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987601 prefixEnd_2987601 := by exact prefixLift 2987601
  have htrace : WordTrace (prefixWord ++ tailWord_2987601) baseStart_2987601 baseEnd_2987601 := by
    simpa [prefixWord, tailWord_2987601, baseEnd_2987601] using wordTrace_append hprefix tailTrace_2987601
  have hstable : (prefixWord ++ tailWord_2987601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987601).length < 2 ^ (prefixWord ++ tailWord_2987601).sum := by decide
  have hdescent : baseEnd_2987601 < baseStart_2987601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987658 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2987658 : Nat := 118140960795 + 2987658 * 2 ^ 59
def prefixEnd_2987658 : Nat := 4983230072969 + 3 ^ 40 * 2987658 * 2
def baseEnd_2987658 : Nat := 1534104585250577008035017

theorem tailTrace_2987658 : CollatzResearch.WordTrace tailWord_2987658 prefixEnd_2987658 1534104585250577008035017 := by
  unfold tailWord_2987658
  simp only [CollatzResearch.WordTrace]
  refine ⟨27242209852558198052080907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72645892940155194805549085 27242209852558198052080907)
  ·
    refine ⟨40863314778837297078121361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27242209852558198052080907 40863314778837297078121361)
    ·
      refine ⟨30647486084127972808591021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40863314778837297078121361 30647486084127972808591021)
      ·
        refine ⟨11492807281547989803221633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30647486084127972808591021 11492807281547989803221633)
        ·
          refine ⟨8619605461160992352416225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11492807281547989803221633 8619605461160992352416225)
          ·
            refine ⟨6464704095870744264312169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8619605461160992352416225 6464704095870744264312169)
            ·
              refine ⟨4848528071903058198234127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464704095870744264312169 4848528071903058198234127)
              ·
                refine ⟨7272792107854587297351191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848528071903058198234127 7272792107854587297351191)
                ·
                  refine ⟨10909188161781880946026787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7272792107854587297351191 10909188161781880946026787)
                  ·
                    refine ⟨16363782242672821419040181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10909188161781880946026787 16363782242672821419040181)
                    ·
                      refine ⟨1534104585250577008035017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16363782242672821419040181 1534104585250577008035017)
                      ·
                        rfl

theorem cell23_2987658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2987658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987658 prefixEnd_2987658 := by exact prefixLift 2987658
  have htrace : WordTrace (prefixWord ++ tailWord_2987658) baseStart_2987658 baseEnd_2987658 := by
    simpa [prefixWord, tailWord_2987658, baseEnd_2987658] using wordTrace_append hprefix tailTrace_2987658
  have hstable : (prefixWord ++ tailWord_2987658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987658).length < 2 ^ (prefixWord ++ tailWord_2987658).sum := by decide
  have hdescent : baseEnd_2987658 < baseStart_2987658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987672 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 3, 2, 2]
def baseStart_2987672 : Nat := 118140960795 + 2987672 * 2 ^ 59
def prefixEnd_2987672 : Nat := 4983230072969 + 3 ^ 40 * 2987672 * 2
def baseEnd_2987672 : Nat := 1534111773979739953259953

theorem tailTrace_2987672 : CollatzResearch.WordTrace tailWord_2987672 prefixEnd_2987672 1534111773979739953259953 := by
  unfold tailWord_2987672
  simp only [CollatzResearch.WordTrace]
  refine ⟨54484675016091036299666635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72646233354788048399555513 54484675016091036299666635)
  ·
    refine ⟨81727012524136554449499953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54484675016091036299666635 81727012524136554449499953)
    ·
      refine ⟨61295259393102415837124965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81727012524136554449499953 61295259393102415837124965)
      ·
        refine ⟨11492861136206702969460931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61295259393102415837124965 11492861136206702969460931)
        ·
          refine ⟨17239291704310054454191397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11492861136206702969460931 17239291704310054454191397)
          ·
            refine ⟨3232367194558135210160887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17239291704310054454191397 3232367194558135210160887)
            ·
              refine ⟨4848550791837202815241331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232367194558135210160887 4848550791837202815241331)
              ·
                refine ⟨7272826187755804222861997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4848550791837202815241331 7272826187755804222861997)
                ·
                  refine ⟨2727309820408426583573249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7272826187755804222861997 2727309820408426583573249)
                  ·
                    refine ⟨2045482365306319937679937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727309820408426583573249 2045482365306319937679937)
                    ·
                      refine ⟨1534111773979739953259953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045482365306319937679937 1534111773979739953259953)
                      ·
                        rfl

theorem cell23_2987672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_2987672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987672 prefixEnd_2987672 := by exact prefixLift 2987672
  have htrace : WordTrace (prefixWord ++ tailWord_2987672) baseStart_2987672 baseEnd_2987672 := by
    simpa [prefixWord, tailWord_2987672, baseEnd_2987672] using wordTrace_append hprefix tailTrace_2987672
  have hstable : (prefixWord ++ tailWord_2987672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987672).length < 2 ^ (prefixWord ++ tailWord_2987672).sum := by decide
  have hdescent : baseEnd_2987672 < baseStart_2987672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987678 : List Nat := [4, 3, 1, 1, 1, 3, 2, 8]
def baseStart_2987678 : Nat := 118140960795 + 2987678 * 2 ^ 59
def prefixEnd_2987678 : Nat := 4983230072969 + 3 ^ 40 * 2987678 * 2
def baseEnd_2987678 : Nat := 56819068698654330732775

theorem tailTrace_2987678 : CollatzResearch.WordTrace tailWord_2987678 prefixEnd_2987678 56819068698654330732775 := by
  unfold tailWord_2987678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13621196108770041953006461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72646379246773557082701125 13621196108770041953006461)
  ·
    refine ⟨5107948540788765732377423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13621196108770041953006461 5107948540788765732377423)
    ·
      refine ⟨7661922811183148598566135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5107948540788765732377423 7661922811183148598566135)
      ·
        refine ⟨11492884216774722897849203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7661922811183148598566135 11492884216774722897849203)
        ·
          refine ⟨17239326325162084346773805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11492884216774722897849203 17239326325162084346773805)
          ·
            refine ⟨6464747371935781630040177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17239326325162084346773805 6464747371935781630040177)
            ·
              refine ⟨4848560528951836222530133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464747371935781630040177 4848560528951836222530133)
              ·
                refine ⟨56819068698654330732775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4848560528951836222530133 56819068698654330732775)
                ·
                  rfl

theorem cell23_2987678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_2987678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987678 prefixEnd_2987678 := by exact prefixLift 2987678
  have htrace : WordTrace (prefixWord ++ tailWord_2987678) baseStart_2987678 baseEnd_2987678 := by
    simpa [prefixWord, tailWord_2987678, baseEnd_2987678] using wordTrace_append hprefix tailTrace_2987678
  have hstable : (prefixWord ++ tailWord_2987678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987678).length < 2 ^ (prefixWord ++ tailWord_2987678).sum := by decide
  have hdescent : baseEnd_2987678 < baseStart_2987678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987682 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2987682 : Nat := 118140960795 + 2987682 * 2 ^ 59
def prefixEnd_2987682 : Nat := 4983230072969 + 3 ^ 40 * 2987682 * 2
def baseEnd_2987682 : Nat := 511372302928761638044969

theorem tailTrace_2987682 : CollatzResearch.WordTrace tailWord_2987682 prefixEnd_2987682 511372302928761638044969 := by
  unfold tailWord_2987682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27242428690536461076799325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72646476508097229538131533 27242428690536461076799325)
  ·
    refine ⟨10215910758951172903799747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27242428690536461076799325 10215910758951172903799747)
    ·
      refine ⟨15323866138426759355699621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10215910758951172903799747 15323866138426759355699621)
      ·
        refine ⟨2873224900955017379193679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15323866138426759355699621 2873224900955017379193679)
        ·
          refine ⟨4309837351432526068790519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873224900955017379193679 4309837351432526068790519)
          ·
            refine ⟨6464756027148789103185779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309837351432526068790519 6464756027148789103185779)
            ·
              refine ⟨9697134040723183654778669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6464756027148789103185779 9697134040723183654778669)
              ·
                refine ⟨3636425265271193870542001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9697134040723183654778669 3636425265271193870542001)
                ·
                  refine ⟨2727318948953395402906501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3636425265271193870542001 2727318948953395402906501)
                  ·
                    refine ⟨511372302928761638044969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2727318948953395402906501 511372302928761638044969)
                    ·
                      rfl

theorem cell23_2987682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2987682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987682 prefixEnd_2987682 := by exact prefixLift 2987682
  have htrace : WordTrace (prefixWord ++ tailWord_2987682) baseStart_2987682 baseEnd_2987682 := by
    simpa [prefixWord, tailWord_2987682, baseEnd_2987682] using wordTrace_append hprefix tailTrace_2987682
  have hstable : (prefixWord ++ tailWord_2987682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987682).length < 2 ^ (prefixWord ++ tailWord_2987682).sum := by decide
  have hdescent : baseEnd_2987682 < baseStart_2987682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987722 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_2987722 : Nat := 118140960795 + 2987722 * 2 ^ 59
def prefixEnd_2987722 : Nat := 4983230072969 + 3 ^ 40 * 2987722 * 2
def baseEnd_2987722 : Nat := 1534137448012464757634723

theorem tailTrace_2987722 : CollatzResearch.WordTrace tailWord_2987722 prefixEnd_2987722 1534137448012464757634723 := by
  unfold tailWord_2987722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27242793420500232784663355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72647449121333954092435613 27242793420500232784663355)
  ·
    refine ⟨40864190130750349176995033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27242793420500232784663355 40864190130750349176995033)
    ·
      refine ⟨30648142598062761882746275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40864190130750349176995033 30648142598062761882746275)
      ·
        refine ⟨45972213897094142824119413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30648142598062761882746275 45972213897094142824119413)
        ·
          refine ⟨4309895052852575889761195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45972213897094142824119413 4309895052852575889761195)
          ·
            refine ⟨6464842579278863834641793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309895052852575889761195 6464842579278863834641793)
            ·
              refine ⟨4848631934459147875981345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464842579278863834641793 4848631934459147875981345)
              ·
                refine ⟨3636473950844360906986009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4848631934459147875981345 3636473950844360906986009)
                ·
                  refine ⟨2727355463133270680239507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3636473950844360906986009 2727355463133270680239507)
                  ·
                    refine ⟨4091033194699906020359261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2727355463133270680239507 4091033194699906020359261)
                    ·
                      refine ⟨1534137448012464757634723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4091033194699906020359261 1534137448012464757634723)
                      ·
                        rfl

theorem cell23_2987722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_2987722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987722 prefixEnd_2987722 := by exact prefixLift 2987722
  have htrace : WordTrace (prefixWord ++ tailWord_2987722) baseStart_2987722 baseEnd_2987722 := by
    simpa [prefixWord, tailWord_2987722, baseEnd_2987722] using wordTrace_append hprefix tailTrace_2987722
  have hstable : (prefixWord ++ tailWord_2987722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987722).length < 2 ^ (prefixWord ++ tailWord_2987722).sum := by decide
  have hdescent : baseEnd_2987722 < baseStart_2987722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987788 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 1, 7, 2]
def baseStart_2987788 : Nat := 118140960795 + 2987788 * 2 ^ 59
def prefixEnd_2987788 : Nat := 4983230072969 + 3 ^ 40 * 2987788 * 2
def baseEnd_2987788 : Nat := 1534171337735661499409419

theorem tailTrace_2987788 : CollatzResearch.WordTrace tailWord_2987788 prefixEnd_2987788 1534171337735661499409419 := by
  unfold tailWord_2987788
  simp only [CollatzResearch.WordTrace]
  refine ⟨54486790449880912205278009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72649053933174549607037345 54486790449880912205278009)
  ·
    refine ⟨40865092837410684153958507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54486790449880912205278009 40865092837410684153958507)
    ·
      refine ⟨61297639256116026230937761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40865092837410684153958507 61297639256116026230937761)
      ·
        refine ⟨45973229442087019673203321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61297639256116026230937761 45973229442087019673203321)
        ·
          refine ⟨34479922081565264754902491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45973229442087019673203321 34479922081565264754902491)
          ·
            refine ⟨51719883122347897132353737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34479922081565264754902491 51719883122347897132353737)
            ·
              refine ⟨38789912341760922849265303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51719883122347897132353737 38789912341760922849265303)
              ·
                refine ⟨58184868512641384273897955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38789912341760922849265303 58184868512641384273897955)
                ·
                  refine ⟨87277302768962076410846933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58184868512641384273897955 87277302768962076410846933)
                  ·
                    refine ⟨2045561783647548665879225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 87277302768962076410846933 2045561783647548665879225)
                    ·
                      refine ⟨1534171337735661499409419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045561783647548665879225 1534171337735661499409419)
                      ·
                        rfl

theorem cell23_2987788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_2987788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987788 prefixEnd_2987788 := by exact prefixLift 2987788
  have htrace : WordTrace (prefixWord ++ tailWord_2987788) baseStart_2987788 baseEnd_2987788 := by
    simpa [prefixWord, tailWord_2987788, baseEnd_2987788] using wordTrace_append hprefix tailTrace_2987788
  have hstable : (prefixWord ++ tailWord_2987788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987788).length < 2 ^ (prefixWord ++ tailWord_2987788).sum := by decide
  have hdescent : baseEnd_2987788 < baseStart_2987788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987831 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_2987831 : Nat := 118140960795 + 2987831 * 2 ^ 59
def prefixEnd_2987831 : Nat := 4983230072969 + 3 ^ 40 * 2987831 * 2
def baseEnd_2987831 : Nat := 1534193417403804831171721

theorem tailTrace_2987831 : CollatzResearch.WordTrace tailWord_2987831 prefixEnd_2987831 1534193417403804831171721 := by
  unfold tailWord_2987831
  simp only [CollatzResearch.WordTrace]
  refine ⟨108975149238606042754371347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72650099492404028502914231 108975149238606042754371347)
  ·
    refine ⟨163462723857909064131557021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108975149238606042754371347 163462723857909064131557021)
    ·
      refine ⟨61298521446715899049333883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163462723857909064131557021 61298521446715899049333883)
      ·
        refine ⟨91947782170073848574000825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61298521446715899049333883 91947782170073848574000825)
        ·
          refine ⟨68960836627555386430500619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91947782170073848574000825 68960836627555386430500619)
          ·
            refine ⟨103441254941333079645750929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68960836627555386430500619 103441254941333079645750929)
            ·
              refine ⟨77580941205999809734313197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103441254941333079645750929 77580941205999809734313197)
              ·
                refine ⟨29092852952249928650367449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77580941205999809734313197 29092852952249928650367449)
                ·
                  refine ⟨21819639714187446487775587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29092852952249928650367449 21819639714187446487775587)
                  ·
                    refine ⟨32729459571281169731663381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21819639714187446487775587 32729459571281169731663381)
                    ·
                      refine ⟨1534193417403804831171721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32729459571281169731663381 1534193417403804831171721)
                      ·
                        rfl

theorem cell23_2987831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_2987831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987831 prefixEnd_2987831 := by exact prefixLift 2987831
  have htrace : WordTrace (prefixWord ++ tailWord_2987831) baseStart_2987831 baseEnd_2987831 := by
    simpa [prefixWord, tailWord_2987831, baseEnd_2987831] using wordTrace_append hprefix tailTrace_2987831
  have hstable : (prefixWord ++ tailWord_2987831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987831).length < 2 ^ (prefixWord ++ tailWord_2987831).sum := by decide
  have hdescent : baseEnd_2987831 < baseStart_2987831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987881 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_2987881 : Nat := 118140960795 + 2987881 * 2 ^ 59
def prefixEnd_2987881 : Nat := 4983230072969 + 3 ^ 40 * 2987881 * 2
def baseEnd_2987881 : Nat := 1534219091436529635546491

theorem tailTrace_2987881 : CollatzResearch.WordTrace tailWord_2987881 prefixEnd_2987881 1534219091436529635546491 := by
  unfold tailWord_2987881
  simp only [CollatzResearch.WordTrace]
  refine ⟨108976972888424901293691497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72651315258949934195794331 108976972888424901293691497)
  ·
    refine ⟨81732729666318675970268623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108976972888424901293691497 81732729666318675970268623)
    ·
      refine ⟨122599094499478013955402935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81732729666318675970268623 122599094499478013955402935)
      ·
        refine ⟨183898641749217020933104403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122599094499478013955402935 183898641749217020933104403)
        ·
          refine ⟨275847962623825531399656605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183898641749217020933104403 275847962623825531399656605)
          ·
            refine ⟨103442985983934574274871227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275847962623825531399656605 103442985983934574274871227)
            ·
              refine ⟨155164478975901861412306841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103442985983934574274871227 155164478975901861412306841)
              ·
                refine ⟨116373359231926396059230131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155164478975901861412306841 116373359231926396059230131)
                ·
                  refine ⟨174560038847889594088845197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116373359231926396059230131 174560038847889594088845197)
                  ·
                    refine ⟨65460014567958597783316949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174560038847889594088845197 65460014567958597783316949)
                    ·
                      refine ⟨1534219091436529635546491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65460014567958597783316949 1534219091436529635546491)
                      ·
                        rfl

theorem cell23_2987881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_2987881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987881 prefixEnd_2987881 := by exact prefixLift 2987881
  have htrace : WordTrace (prefixWord ++ tailWord_2987881) baseStart_2987881 baseEnd_2987881 := by
    simpa [prefixWord, tailWord_2987881, baseEnd_2987881] using wordTrace_append hprefix tailTrace_2987881
  have hstable : (prefixWord ++ tailWord_2987881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987881).length < 2 ^ (prefixWord ++ tailWord_2987881).sum := by decide
  have hdescent : baseEnd_2987881 < baseStart_2987881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987925 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_2987925 : Nat := 118140960795 + 2987925 * 2 ^ 59
def prefixEnd_2987925 : Nat := 4983230072969 + 3 ^ 40 * 2987925 * 2
def baseEnd_2987925 : Nat := 1534241684585327463396289

theorem tailTrace_2987925 : CollatzResearch.WordTrace tailWord_2987925 prefixEnd_2987925 1534241684585327463396289 := by
  unfold tailWord_2987925
  simp only [CollatzResearch.WordTrace]
  refine ⟨108978577700265496808293229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72652385133510331205528819 108978577700265496808293229)
  ·
    refine ⟨40866966637599561303109961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108978577700265496808293229 40866966637599561303109961)
    ·
      refine ⟨30650224978199670977332471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40866966637599561303109961 30650224978199670977332471)
      ·
        refine ⟨45975337467299506465998707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30650224978199670977332471 45975337467299506465998707)
        ·
          refine ⟨68963006200949259698998061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45975337467299506465998707 68963006200949259698998061)
          ·
            refine ⟨25861127325355972387124273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68963006200949259698998061 25861127325355972387124273)
            ·
              refine ⟨19395845494016979290343205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25861127325355972387124273 19395845494016979290343205)
              ·
                refine ⟨3636721030128183616939351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19395845494016979290343205 3636721030128183616939351)
                ·
                  refine ⟨5455081545192275425409027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636721030128183616939351 5455081545192275425409027)
                  ·
                    refine ⟨8182622317788413138113541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5455081545192275425409027 8182622317788413138113541)
                    ·
                      refine ⟨1534241684585327463396289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8182622317788413138113541 1534241684585327463396289)
                      ·
                        rfl

theorem cell23_2987925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_2987925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987925 prefixEnd_2987925 := by exact prefixLift 2987925
  have htrace : WordTrace (prefixWord ++ tailWord_2987925) baseStart_2987925 baseEnd_2987925 := by
    simpa [prefixWord, tailWord_2987925, baseEnd_2987925] using wordTrace_append hprefix tailTrace_2987925
  have hstable : (prefixWord ++ tailWord_2987925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987925).length < 2 ^ (prefixWord ++ tailWord_2987925).sum := by decide
  have hdescent : baseEnd_2987925 < baseStart_2987925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987978 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_2987978 : Nat := 118140960795 + 2987978 * 2 ^ 59
def prefixEnd_2987978 : Nat := 4983230072969 + 3 ^ 40 * 2987978 * 2
def baseEnd_2987978 : Nat := 511422966353338585344515

theorem tailTrace_2987978 : CollatzResearch.WordTrace tailWord_2987978 prefixEnd_2987978 511422966353338585344515 := by
  unfold tailWord_2987978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27245127692268371714993147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72653673846048991239981725 27245127692268371714993147)
  ·
    refine ⟨40867691538402557572489721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27245127692268371714993147 40867691538402557572489721)
    ·
      refine ⟨30650768653801918179367291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40867691538402557572489721 30650768653801918179367291)
      ·
        refine ⟨45976152980702877269050937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30650768653801918179367291 45976152980702877269050937)
        ·
          refine ⟨34482114735527157951788203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45976152980702877269050937 34482114735527157951788203)
          ·
            refine ⟨51723172103290736927682305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34482114735527157951788203 51723172103290736927682305)
            ·
              refine ⟨38792379077468052695761729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51723172103290736927682305 38792379077468052695761729)
              ·
                refine ⟨29094284308101039521821297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38792379077468052695761729 29094284308101039521821297)
                ·
                  refine ⟨21820713231075779641365973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29094284308101039521821297 21820713231075779641365973)
                  ·
                    refine ⟨511422966353338585344515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21820713231075779641365973 511422966353338585344515)
                    ·
                      rfl

theorem cell23_2987978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_2987978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987978 prefixEnd_2987978 := by exact prefixLift 2987978
  have htrace : WordTrace (prefixWord ++ tailWord_2987978) baseStart_2987978 baseEnd_2987978 := by
    simpa [prefixWord, tailWord_2987978, baseEnd_2987978] using wordTrace_append hprefix tailTrace_2987978
  have hstable : (prefixWord ++ tailWord_2987978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987978).length < 2 ^ (prefixWord ++ tailWord_2987978).sum := by decide
  have hdescent : baseEnd_2987978 < baseStart_2987978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987993 : List Nat := [1, 2, 1, 2, 6, 2, 1, 3, 1, 2, 2]
def baseStart_2987993 : Nat := 118140960795 + 2987993 * 2 ^ 59
def prefixEnd_2987993 : Nat := 4983230072969 + 3 ^ 40 * 2987993 * 2
def baseEnd_2987993 : Nat := 1534276601269833197345977

theorem tailTrace_2987993 : CollatzResearch.WordTrace tailWord_2987993 prefixEnd_2987993 1534276601269833197345977 := by
  unfold tailWord_2987993
  simp only [CollatzResearch.WordTrace]
  refine ⟨108981057864019144421768633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72654038576012762947845755 108981057864019144421768633)
  ·
    refine ⟨81735793398014358316326475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108981057864019144421768633 81735793398014358316326475)
    ·
      refine ⟨122603690097021537474489713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81735793398014358316326475 122603690097021537474489713)
      ·
        refine ⟨91952767572766153105867285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122603690097021537474489713 91952767572766153105867285)
        ·
          refine ⟨4310285979973413426837529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91952767572766153105867285 4310285979973413426837529)
          ·
            refine ⟨3232714484980060070128147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310285979973413426837529 3232714484980060070128147)
            ·
              refine ⟨4849071727470090105192221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232714484980060070128147 4849071727470090105192221)
              ·
                refine ⟨1818401897801283789447083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4849071727470090105192221 1818401897801283789447083)
                ·
                  refine ⟨2727602846701925684170625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818401897801283789447083 2727602846701925684170625)
                  ·
                    refine ⟨2045702135026444263127969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727602846701925684170625 2045702135026444263127969)
                    ·
                      refine ⟨1534276601269833197345977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045702135026444263127969 1534276601269833197345977)
                      ·
                        rfl

theorem cell23_2987993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_2987993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987993 prefixEnd_2987993 := by exact prefixLift 2987993
  have htrace : WordTrace (prefixWord ++ tailWord_2987993) baseStart_2987993 baseEnd_2987993 := by
    simpa [prefixWord, tailWord_2987993, baseEnd_2987993] using wordTrace_append hprefix tailTrace_2987993
  have hstable : (prefixWord ++ tailWord_2987993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987993).length < 2 ^ (prefixWord ++ tailWord_2987993).sum := by decide
  have hdescent : baseEnd_2987993 < baseStart_2987993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2987996 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2987996 : Nat := 118140960795 + 2987996 * 2 ^ 59
def prefixEnd_2987996 : Nat := 4983230072969 + 3 ^ 40 * 2987996 * 2
def baseEnd_2987996 : Nat := 1534278141711796685608463

theorem tailTrace_2987996 : CollatzResearch.WordTrace tailWord_2987996 prefixEnd_2987996 1534278141711796685608463 := by
  unfold tailWord_2987996
  simp only [CollatzResearch.WordTrace]
  refine ⟨54490583641504137967063921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72654111522005517289418561 54490583641504137967063921)
  ·
    refine ⟨40867937731128103475297941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54490583641504137967063921 40867937731128103475297941)
    ·
      refine ⟨1915684581146629850404591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40867937731128103475297941 1915684581146629850404591)
      ·
        refine ⟨2873526871719944775606887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915684581146629850404591 2873526871719944775606887)
        ·
          refine ⟨4310290307579917163410331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873526871719944775606887 4310290307579917163410331)
          ·
            refine ⟨6465435461369875745115497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4310290307579917163410331 6465435461369875745115497)
            ·
              refine ⟨4849076596027406808836623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6465435461369875745115497 4849076596027406808836623)
              ·
                refine ⟨7273614894041110213254935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4849076596027406808836623 7273614894041110213254935)
                ·
                  refine ⟨10910422341061665319882403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7273614894041110213254935 10910422341061665319882403)
                  ·
                    refine ⟨16365633511592497979823605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10910422341061665319882403 16365633511592497979823605)
                    ·
                      refine ⟨1534278141711796685608463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16365633511592497979823605 1534278141711796685608463)
                      ·
                        rfl

theorem cell23_2987996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2987996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2987996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2987996 prefixEnd_2987996 := by exact prefixLift 2987996
  have htrace : WordTrace (prefixWord ++ tailWord_2987996) baseStart_2987996 baseEnd_2987996 := by
    simpa [prefixWord, tailWord_2987996, baseEnd_2987996] using wordTrace_append hprefix tailTrace_2987996
  have hstable : (prefixWord ++ tailWord_2987996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2987996).length < 2 ^ (prefixWord ++ tailWord_2987996).sum := by decide
  have hdescent : baseEnd_2987996 < baseStart_2987996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2987996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988032 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 6, 2, 2]
def baseStart_2988032 : Nat := 118140960795 + 2988032 * 2 ^ 59
def prefixEnd_2988032 : Nat := 4983230072969 + 3 ^ 40 * 2988032 * 2
def baseEnd_2988032 : Nat := 1534296627015358544758297

theorem tailTrace_2988032 : CollatzResearch.WordTrace tailWord_2988032 prefixEnd_2988032 1534296627015358544758297 := by
  unfold tailWord_2988032
  simp only [CollatzResearch.WordTrace]
  refine ⟨54491240155438927041219175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72654986873918569388292233 54491240155438927041219175)
  ·
    refine ⟨81736860233158390561828763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54491240155438927041219175 81736860233158390561828763)
    ·
      refine ⟨122605290349737585842743145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81736860233158390561828763 122605290349737585842743145)
      ·
        refine ⟨91953967762303189382057359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122605290349737585842743145 91953967762303189382057359)
        ·
          refine ⟨137930951643454784073086039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91953967762303189382057359 137930951643454784073086039)
          ·
            refine ⟨206896427465182176109629059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137930951643454784073086039 206896427465182176109629059)
            ·
              refine ⟨310344641197773264164443589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206896427465182176109629059 310344641197773264164443589)
              ·
                refine ⟨58189620224582487030833173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310344641197773264164443589 58189620224582487030833173)
                ·
                  refine ⟨2727638448027304079570305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58189620224582487030833173 2727638448027304079570305)
                  ·
                    refine ⟨2045728836020478059677729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727638448027304079570305 2045728836020478059677729)
                    ·
                      refine ⟨1534296627015358544758297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045728836020478059677729 1534296627015358544758297)
                      ·
                        rfl

theorem cell23_2988032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_2988032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988032 prefixEnd_2988032 := by exact prefixLift 2988032
  have htrace : WordTrace (prefixWord ++ tailWord_2988032) baseStart_2988032 baseEnd_2988032 := by
    simpa [prefixWord, tailWord_2988032, baseEnd_2988032] using wordTrace_append hprefix tailTrace_2988032
  have hstable : (prefixWord ++ tailWord_2988032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988032).length < 2 ^ (prefixWord ++ tailWord_2988032).sum := by decide
  have hdescent : baseEnd_2988032 < baseStart_2988032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988036 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2988036 : Nat := 118140960795 + 2988036 * 2 ^ 59
def prefixEnd_2988036 : Nat := 4983230072969 + 3 ^ 40 * 2988036 * 2
def baseEnd_2988036 : Nat := 1534298680937976529108279

theorem tailTrace_2988036 : CollatzResearch.WordTrace tailWord_2988036 prefixEnd_2988036 1534298680937976529108279 := by
  unfold tailWord_2988036
  simp only [CollatzResearch.WordTrace]
  refine ⟨54491313101431681382791981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72655084135242241843722641 54491313101431681382791981)
  ·
    refine ⟨20434242413036880518546993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54491313101431681382791981 20434242413036880518546993)
    ·
      refine ⟨15325681809777660388910245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20434242413036880518546993 15325681809777660388910245)
      ·
        refine ⟨2873565339333311322920671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15325681809777660388910245 2873565339333311322920671)
        ·
          refine ⟨4310348008999966984381007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873565339333311322920671 4310348008999966984381007)
          ·
            refine ⟨6465522013499950476571511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4310348008999966984381007 6465522013499950476571511)
            ·
              refine ⟨9698283020249925714857267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6465522013499950476571511 9698283020249925714857267)
              ·
                refine ⟨14547424530374888572285901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9698283020249925714857267 14547424530374888572285901)
                ·
                  refine ⟨5455284198890583214607213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14547424530374888572285901 5455284198890583214607213)
                  ·
                    refine ⟨2045731574583968705477705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5455284198890583214607213 2045731574583968705477705)
                    ·
                      refine ⟨1534298680937976529108279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045731574583968705477705 1534298680937976529108279)
                      ·
                        rfl

theorem cell23_2988036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2988036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988036 prefixEnd_2988036 := by exact prefixLift 2988036
  have htrace : WordTrace (prefixWord ++ tailWord_2988036) baseStart_2988036 baseEnd_2988036 := by
    simpa [prefixWord, tailWord_2988036, baseEnd_2988036] using wordTrace_append hprefix tailTrace_2988036
  have hstable : (prefixWord ++ tailWord_2988036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988036).length < 2 ^ (prefixWord ++ tailWord_2988036).sum := by decide
  have hdescent : baseEnd_2988036 < baseStart_2988036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988066 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_2988066 : Nat := 118140960795 + 2988066 * 2 ^ 59
def prefixEnd_2988066 : Nat := 4983230072969 + 3 ^ 40 * 2988066 * 2
def baseEnd_2988066 : Nat := 1534314085357611411733141

theorem tailTrace_2988066 : CollatzResearch.WordTrace tailWord_2988066 prefixEnd_2988066 1534314085357611411733141 := by
  unfold tailWord_2988066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27245930098188669472294013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72655813595169785259450701 27245930098188669472294013)
  ·
    refine ⟨10217223786820751052110255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27245930098188669472294013 10217223786820751052110255)
    ·
      refine ⟨15325835680231126578165383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10217223786820751052110255 15325835680231126578165383)
      ·
        refine ⟨22988753520346689867248075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15325835680231126578165383 22988753520346689867248075)
        ·
          refine ⟨34483130280520034800872113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22988753520346689867248075 34483130280520034800872113)
          ·
            refine ⟨25862347710390026100654085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34483130280520034800872113 25862347710390026100654085)
            ·
              refine ⟨4849190195698129893872641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25862347710390026100654085 4849190195698129893872641)
              ·
                refine ⟨3636892646773597420404481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4849190195698129893872641 3636892646773597420404481)
                ·
                  refine ⟨2727669485080198065303361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3636892646773597420404481 2727669485080198065303361)
                  ·
                    refine ⟨2045752113810148548977521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727669485080198065303361 2045752113810148548977521)
                    ·
                      refine ⟨1534314085357611411733141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045752113810148548977521 1534314085357611411733141)
                      ·
                        rfl

theorem cell23_2988066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_2988066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988066 prefixEnd_2988066 := by exact prefixLift 2988066
  have htrace : WordTrace (prefixWord ++ tailWord_2988066) baseStart_2988066 baseEnd_2988066 := by
    simpa [prefixWord, tailWord_2988066, baseEnd_2988066] using wordTrace_append hprefix tailTrace_2988066
  have hstable : (prefixWord ++ tailWord_2988066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988066).length < 2 ^ (prefixWord ++ tailWord_2988066).sum := by decide
  have hdescent : baseEnd_2988066 < baseStart_2988066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988082 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_2988082 : Nat := 118140960795 + 2988082 * 2 ^ 59
def prefixEnd_2988082 : Nat := 4983230072969 + 3 ^ 40 * 2988082 * 2
def baseEnd_2988082 : Nat := 1534322301048083349133067

theorem tailTrace_2988082 : CollatzResearch.WordTrace tailWord_2988082 prefixEnd_2988082 1534322301048083349133067 := by
  unfold tailWord_2988082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27246075990174178155439625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72656202640464475081172333 27246075990174178155439625)
  ·
    refine ⟨20434556992630633616579719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27246075990174178155439625 20434556992630633616579719)
    ·
      refine ⟨30651835488945950424869579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20434556992630633616579719 30651835488945950424869579)
      ·
        refine ⟨45977753233418925637304369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30651835488945950424869579 45977753233418925637304369)
        ·
          refine ⟨34483314925064194227978277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45977753233418925637304369 34483314925064194227978277)
          ·
            refine ⟨6465621548449536417745927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34483314925064194227978277 6465621548449536417745927)
            ·
              refine ⟨9698432322674304626618891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6465621548449536417745927 9698432322674304626618891)
              ·
                refine ⟨14547648484011456939928337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9698432322674304626618891 14547648484011456939928337)
                ·
                  refine ⟨10910736363008592704946253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14547648484011456939928337 10910736363008592704946253)
                  ·
                    refine ⟨4091526136128222264354845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10910736363008592704946253 4091526136128222264354845)
                    ·
                      refine ⟨1534322301048083349133067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4091526136128222264354845 1534322301048083349133067)
                      ·
                        rfl

theorem cell23_2988082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_2988082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988082 prefixEnd_2988082 := by exact prefixLift 2988082
  have htrace : WordTrace (prefixWord ++ tailWord_2988082) baseStart_2988082 baseEnd_2988082 := by
    simpa [prefixWord, tailWord_2988082, baseEnd_2988082] using wordTrace_append hprefix tailTrace_2988082
  have hstable : (prefixWord ++ tailWord_2988082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988082).length < 2 ^ (prefixWord ++ tailWord_2988082).sum := by decide
  have hdescent : baseEnd_2988082 < baseStart_2988082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988085 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2988085 : Nat := 118140960795 + 2988085 * 2 ^ 59
def prefixEnd_2988085 : Nat := 4983230072969 + 3 ^ 40 * 2988085 * 2
def baseEnd_2988085 : Nat := 511441280496682279131851

theorem tailTrace_2988085 : CollatzResearch.WordTrace tailWord_2988085 prefixEnd_2988085 511441280496682279131851 := by
  unfold tailWord_2988085
  simp only [CollatzResearch.WordTrace]
  refine ⟨108984413379685844134117709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72656275586457229422745139 108984413379685844134117709)
  ·
    refine ⟨40869155017382191550294141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108984413379685844134117709 40869155017382191550294141)
    ·
      refine ⟨15325933131518321831360303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40869155017382191550294141 15325933131518321831360303)
      ·
        refine ⟨22988899697277482747040455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15325933131518321831360303 22988899697277482747040455)
        ·
          refine ⟨34483349545916224120560683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22988899697277482747040455 34483349545916224120560683)
          ·
            refine ⟨51725024318874336180841025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34483349545916224120560683 51725024318874336180841025)
            ·
              refine ⟨38793768239155752135630769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51725024318874336180841025 38793768239155752135630769)
              ·
                refine ⟨29095326179366814101723077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38793768239155752135630769 29095326179366814101723077)
                ·
                  refine ⟨5455373658631277644073077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29095326179366814101723077 5455373658631277644073077)
                  ·
                    refine ⟨511441280496682279131851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5455373658631277644073077 511441280496682279131851)
                    ·
                      rfl

theorem cell23_2988085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2988085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988085 prefixEnd_2988085 := by exact prefixLift 2988085
  have htrace : WordTrace (prefixWord ++ tailWord_2988085) baseStart_2988085 baseEnd_2988085 := by
    simpa [prefixWord, tailWord_2988085, baseEnd_2988085] using wordTrace_append hprefix tailTrace_2988085
  have hstable : (prefixWord ++ tailWord_2988085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988085).length < 2 ^ (prefixWord ++ tailWord_2988085).sum := by decide
  have hdescent : baseEnd_2988085 < baseStart_2988085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988092 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_2988092 : Nat := 118140960795 + 2988092 * 2 ^ 59
def prefixEnd_2988092 : Nat := 4983230072969 + 3 ^ 40 * 2988092 * 2
def baseEnd_2988092 : Nat := 1534327435854628310008021

theorem tailTrace_2988092 : CollatzResearch.WordTrace tailWord_2988092 prefixEnd_2988092 1534327435854628310008021 := by
  unfold tailWord_2988092
  simp only [CollatzResearch.WordTrace]
  refine ⟨54492334345330242164811265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72656445793773656219748353 54492334345330242164811265)
  ·
    refine ⟨40869250758997681623608449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54492334345330242164811265 40869250758997681623608449)
    ·
      refine ⟨30651938069248261217706337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40869250758997681623608449 30651938069248261217706337)
      ·
        refine ⟨22988953551936195913279753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30651938069248261217706337 22988953551936195913279753)
        ·
          refine ⟨17241715163952146934959815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22988953551936195913279753 17241715163952146934959815)
          ·
            refine ⟨25862572745928220402439723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17241715163952146934959815 25862572745928220402439723)
            ·
              refine ⟨38793859118892330603659585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25862572745928220402439723 38793859118892330603659585)
              ·
                refine ⟨29095394339169247952744689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38793859118892330603659585 29095394339169247952744689)
                ·
                  refine ⟨21821545754376935964558517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29095394339169247952744689 21821545754376935964558517)
                  ·
                    refine ⟨2045769914472837746677361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21821545754376935964558517 2045769914472837746677361)
                    ·
                      refine ⟨1534327435854628310008021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045769914472837746677361 1534327435854628310008021)
                      ·
                        rfl

theorem cell23_2988092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_2988092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988092 prefixEnd_2988092 := by exact prefixLift 2988092
  have htrace : WordTrace (prefixWord ++ tailWord_2988092) baseStart_2988092 baseEnd_2988092 := by
    simpa [prefixWord, tailWord_2988092, baseEnd_2988092] using wordTrace_append hprefix tailTrace_2988092
  have hstable : (prefixWord ++ tailWord_2988092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988092).length < 2 ^ (prefixWord ++ tailWord_2988092).sum := by decide
  have hdescent : baseEnd_2988092 < baseStart_2988092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988105 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_2988105 : Nat := 118140960795 + 2988105 * 2 ^ 59
def prefixEnd_2988105 : Nat := 4983230072969 + 3 ^ 40 * 2988105 * 2
def baseEnd_2988105 : Nat := 1534334111103136759145461

theorem tailTrace_2988105 : CollatzResearch.WordTrace tailWord_2988105 prefixEnd_2988105 1534334111103136759145461 := by
  unfold tailWord_2988105
  simp only [CollatzResearch.WordTrace]
  refine ⟨108985142839613387549845769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72656761893075591699897179 108985142839613387549845769)
  ·
    refine ⟨81738857129710040662384327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108985142839613387549845769 81738857129710040662384327)
    ·
      refine ⟨122608285694565060993576491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81738857129710040662384327 122608285694565060993576491)
      ·
        refine ⟨183912428541847591490364737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122608285694565060993576491 183912428541847591490364737)
        ·
          refine ⟨137934321406385693617773553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183912428541847591490364737 137934321406385693617773553)
          ·
            refine ⟨103450741054789270213330165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137934321406385693617773553 103450741054789270213330165)
            ·
              refine ⟨9698506973886494082499703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103450741054789270213330165 9698506973886494082499703)
              ·
                refine ⟨14547760460829741123749555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9698506973886494082499703 14547760460829741123749555)
                ·
                  refine ⟨21821640691244611685624333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14547760460829741123749555 21821640691244611685624333)
                  ·
                    refine ⟨8183115259216729382109125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21821640691244611685624333 8183115259216729382109125)
                    ·
                      refine ⟨1534334111103136759145461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8183115259216729382109125 1534334111103136759145461)
                      ·
                        rfl

theorem cell23_2988105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_2988105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988105 prefixEnd_2988105 := by exact prefixLift 2988105
  have htrace : WordTrace (prefixWord ++ tailWord_2988105) baseStart_2988105 baseEnd_2988105 := by
    simpa [prefixWord, tailWord_2988105, baseEnd_2988105] using wordTrace_append hprefix tailTrace_2988105
  have hstable : (prefixWord ++ tailWord_2988105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988105).length < 2 ^ (prefixWord ++ tailWord_2988105).sum := by decide
  have hdescent : baseEnd_2988105 < baseStart_2988105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988122 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2]
def baseStart_2988122 : Nat := 118140960795 + 2988122 * 2 ^ 59
def prefixEnd_2988122 : Nat := 4983230072969 + 3 ^ 40 * 2988122 * 2
def baseEnd_2988122 : Nat := 1534342840274263192632883

theorem tailTrace_2988122 : CollatzResearch.WordTrace tailWord_2988122 prefixEnd_2988122 1534342840274263192632883 := by
  unfold tailWord_2988122
  simp only [CollatzResearch.WordTrace]
  refine ⟨27246440720137949863303655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72657175253701199635476413 27246440720137949863303655)
  ·
    refine ⟨40869661080206924794955483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27246440720137949863303655 40869661080206924794955483)
    ·
      refine ⟨61304491620310387192433225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40869661080206924794955483 61304491620310387192433225)
      ·
        refine ⟨45978368715232790394324919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61304491620310387192433225 45978368715232790394324919)
        ·
          refine ⟨68967553072849185591487379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45978368715232790394324919 68967553072849185591487379)
          ·
            refine ⟨103451329609273778387231069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68967553072849185591487379 103451329609273778387231069)
            ·
              refine ⟨38794248603477666895211651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103451329609273778387231069 38794248603477666895211651)
              ·
                refine ⟨58191372905216500342817477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38794248603477666895211651 58191372905216500342817477)
                ·
                  refine ⟨10910882419728093814278277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58191372905216500342817477 10910882419728093814278277)
                  ·
                    refine ⟨2045790453699017590177177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10910882419728093814278277 2045790453699017590177177)
                    ·
                      refine ⟨1534342840274263192632883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045790453699017590177177 1534342840274263192632883)
                      ·
                        rfl

theorem cell23_2988122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_2988122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988122 prefixEnd_2988122 := by exact prefixLift 2988122
  have htrace : WordTrace (prefixWord ++ tailWord_2988122) baseStart_2988122 baseEnd_2988122 := by
    simpa [prefixWord, tailWord_2988122, baseEnd_2988122] using wordTrace_append hprefix tailTrace_2988122
  have hstable : (prefixWord ++ tailWord_2988122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988122).length < 2 ^ (prefixWord ++ tailWord_2988122).sum := by decide
  have hdescent : baseEnd_2988122 < baseStart_2988122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988132 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_2988132 : Nat := 118140960795 + 2988132 * 2 ^ 59
def prefixEnd_2988132 : Nat := 4983230072969 + 3 ^ 40 * 2988132 * 2
def baseEnd_2988132 : Nat := 511449325026936051169279

theorem tailTrace_2988132 : CollatzResearch.WordTrace tailWord_2988132 prefixEnd_2988132 511449325026936051169279 := by
  unfold tailWord_2988132
  simp only [CollatzResearch.WordTrace]
  refine ⟨54493063805257785580539325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72657418407010380774052433 54493063805257785580539325)
  ·
    refine ⟨20434898926971669592702247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54493063805257785580539325 20434898926971669592702247)
    ·
      refine ⟨30652348390457504389053371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20434898926971669592702247 30652348390457504389053371)
      ·
        refine ⟨45978522585686256583580057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30652348390457504389053371 45978522585686256583580057)
        ·
          refine ⟨34483891939264692437685043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45978522585686256583580057 34483891939264692437685043)
          ·
            refine ⟨51725837908897038656527565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34483891939264692437685043 51725837908897038656527565)
            ·
              refine ⟨19397189215836389496197837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51725837908897038656527565 19397189215836389496197837)
              ·
                refine ⟨7273945955938646061074189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19397189215836389496197837 7273945955938646061074189)
                ·
                  refine ⟨2727729733476992272902821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7273945955938646061074189 2727729733476992272902821)
                  ·
                    refine ⟨511449325026936051169279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2727729733476992272902821 511449325026936051169279)
                    ·
                      rfl

theorem cell23_2988132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_2988132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988132 prefixEnd_2988132 := by exact prefixLift 2988132
  have htrace : WordTrace (prefixWord ++ tailWord_2988132) baseStart_2988132 baseEnd_2988132 := by
    simpa [prefixWord, tailWord_2988132, baseEnd_2988132] using wordTrace_append hprefix tailTrace_2988132
  have hstable : (prefixWord ++ tailWord_2988132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988132).length < 2 ^ (prefixWord ++ tailWord_2988132).sum := by decide
  have hdescent : baseEnd_2988132 < baseStart_2988132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988135 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2988135 : Nat := 118140960795 + 2988135 * 2 ^ 59
def prefixEnd_2988135 : Nat := 4983230072969 + 3 ^ 40 * 2988135 * 2
def baseEnd_2988135 : Nat := 1534349515522771641770323

theorem tailTrace_2988135 : CollatzResearch.WordTrace tailWord_2988135 prefixEnd_2988135 1534349515522771641770323 := by
  unfold tailWord_2988135
  simp only [CollatzResearch.WordTrace]
  refine ⟨108986237029504702673437859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72657491353003135115625239 108986237029504702673437859)
  ·
    refine ⟨163479355544257054010156789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108986237029504702673437859 163479355544257054010156789)
    ·
      refine ⟨15326189582274098813452199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163479355544257054010156789 15326189582274098813452199)
      ·
        refine ⟨22989284373411148220178299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15326189582274098813452199 22989284373411148220178299)
        ·
          refine ⟨34483926560116722330267449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22989284373411148220178299 34483926560116722330267449)
          ·
            refine ⟨25862944920087541747700587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34483926560116722330267449 25862944920087541747700587)
            ·
              refine ⟨38794417380131312621550881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25862944920087541747700587 38794417380131312621550881)
              ·
                refine ⟨29095813035098484466163161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38794417380131312621550881 29095813035098484466163161)
                ·
                  refine ⟨21821859776323863349622371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29095813035098484466163161 21821859776323863349622371)
                  ·
                    refine ⟨32732789664485795024433557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21821859776323863349622371 32732789664485795024433557)
                    ·
                      refine ⟨1534349515522771641770323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32732789664485795024433557 1534349515522771641770323)
                      ·
                        rfl

theorem cell23_2988135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2988135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988135 prefixEnd_2988135 := by exact prefixLift 2988135
  have htrace : WordTrace (prefixWord ++ tailWord_2988135) baseStart_2988135 baseEnd_2988135 := by
    simpa [prefixWord, tailWord_2988135, baseEnd_2988135] using wordTrace_append hprefix tailTrace_2988135
  have hstable : (prefixWord ++ tailWord_2988135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988135).length < 2 ^ (prefixWord ++ tailWord_2988135).sum := by decide
  have hdescent : baseEnd_2988135 < baseStart_2988135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988142 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2988142 : Nat := 118140960795 + 2988142 * 2 ^ 59
def prefixEnd_2988142 : Nat := 4983230072969 + 3 ^ 40 * 2988142 * 2
def baseEnd_2988142 : Nat := 1534353109887353114382791

theorem tailTrace_2988142 : CollatzResearch.WordTrace tailWord_2988142 prefixEnd_2988142 1534353109887353114382791 := by
  unfold tailWord_2988142
  simp only [CollatzResearch.WordTrace]
  refine ⟨13623311542559917858617835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72657661560319561912628453 13623311542559917858617835)
  ·
    refine ⟨20434967313839876787926753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13623311542559917858617835 20434967313839876787926753)
    ·
      refine ⟨15326225485379907590945065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20434967313839876787926753 15326225485379907590945065)
      ·
        refine ⟨11494669114034930693208799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15326225485379907590945065 11494669114034930693208799)
        ·
          refine ⟨17242003671052396039813199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11494669114034930693208799 17242003671052396039813199)
          ·
            refine ⟨25863005506578594059719799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17242003671052396039813199 25863005506578594059719799)
            ·
              refine ⟨38794508259867891089579699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25863005506578594059719799 38794508259867891089579699)
              ·
                refine ⟨58191762389801836634369549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38794508259867891089579699 58191762389801836634369549)
                ·
                  refine ⟨21821910896175688737888581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58191762389801836634369549 21821910896175688737888581)
                  ·
                    refine ⟨4091608293032941638354109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21821910896175688737888581 4091608293032941638354109)
                    ·
                      refine ⟨1534353109887353114382791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4091608293032941638354109 1534353109887353114382791)
                      ·
                        rfl

theorem cell23_2988142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2988142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988142 prefixEnd_2988142 := by exact prefixLift 2988142
  have htrace : WordTrace (prefixWord ++ tailWord_2988142) baseStart_2988142 baseEnd_2988142 := by
    simpa [prefixWord, tailWord_2988142, baseEnd_2988142] using wordTrace_append hprefix tailTrace_2988142
  have hstable : (prefixWord ++ tailWord_2988142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988142).length < 2 ^ (prefixWord ++ tailWord_2988142).sum := by decide
  have hdescent : baseEnd_2988142 < baseStart_2988142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988183 : List Nat := [1, 1, 3, 3, 4, 1, 3, 2, 1, 4]
def baseStart_2988183 : Nat := 118140960795 + 2988183 * 2 ^ 59
def prefixEnd_2988183 : Nat := 4983230072969 + 3 ^ 40 * 2988183 * 2
def baseEnd_2988183 : Nat := 511458054198062484656701

theorem tailTrace_2988183 : CollatzResearch.WordTrace tailWord_2988183 prefixEnd_2988183 511458054198062484656701 := by
  unfold tailWord_2988183
  simp only [CollatzResearch.WordTrace]
  refine ⟨108987987733330806871185203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72658658488887204580790135 108987987733330806871185203)
  ·
    refine ⟨163481981599996210306777805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108987987733330806871185203 163481981599996210306777805)
    ·
      refine ⟨61305743099998578865041677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163481981599996210306777805 61305743099998578865041677)
      ·
        refine ⟨22989653662499467074390629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61305743099998578865041677 22989653662499467074390629)
        ·
          refine ⟨4310560061718650076448243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22989653662499467074390629 4310560061718650076448243)
          ·
            refine ⟨6465840092577975114672365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4310560061718650076448243 6465840092577975114672365)
            ·
              refine ⟨2424690034716740668002137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6465840092577975114672365 2424690034716740668002137)
              ·
                refine ⟨1818517526037555501001603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424690034716740668002137 1818517526037555501001603)
                ·
                  refine ⟨2727776289056333251502405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818517526037555501001603 2727776289056333251502405)
                  ·
                    refine ⟨511458054198062484656701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2727776289056333251502405 511458054198062484656701)
                    ·
                      rfl

theorem cell23_2988183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_2988183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988183 prefixEnd_2988183 := by exact prefixLift 2988183
  have htrace : WordTrace (prefixWord ++ tailWord_2988183) baseStart_2988183 baseEnd_2988183 := by
    simpa [prefixWord, tailWord_2988183, baseEnd_2988183] using wordTrace_append hprefix tailTrace_2988183
  have hstable : (prefixWord ++ tailWord_2988183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988183).length < 2 ^ (prefixWord ++ tailWord_2988183).sum := by decide
  have hdescent : baseEnd_2988183 < baseStart_2988183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988195 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 4]
def baseStart_2988195 : Nat := 118140960795 + 2988195 * 2 ^ 59
def prefixEnd_2988195 : Nat := 4983230072969 + 3 ^ 40 * 2988195 * 2
def baseEnd_2988195 : Nat := 1534380324362041407020047

theorem tailTrace_2988195 : CollatzResearch.WordTrace tailWord_2988195 prefixEnd_2988195 1534380324362041407020047 := by
  unfold tailWord_2988195
  simp only [CollatzResearch.WordTrace]
  refine ⟨108988425409287332920622039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72658950272858221947081359 108988425409287332920622039)
  ·
    refine ⟨163482638113930999380933059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108988425409287332920622039 163482638113930999380933059)
    ·
      refine ⟨245223957170896499071399589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163482638113930999380933059 245223957170896499071399589)
      ·
        refine ⟨45979491969543093575887423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245223957170896499071399589 45979491969543093575887423)
        ·
          refine ⟨68969237954314640363831135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45979491969543093575887423 68969237954314640363831135)
          ·
            refine ⟨103453856931471960545746703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68969237954314640363831135 103453856931471960545746703)
            ·
              refine ⟨155180785397207940818620055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103453856931471960545746703 155180785397207940818620055)
              ·
                refine ⟨232771178095811911227930083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155180785397207940818620055 232771178095811911227930083)
                ·
                  refine ⟨349156767143717866841895125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232771178095811911227930083 349156767143717866841895125)
                  ·
                    refine ⟨8183361729930887504106917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 349156767143717866841895125 8183361729930887504106917)
                    ·
                      refine ⟨1534380324362041407020047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8183361729930887504106917 1534380324362041407020047)
                      ·
                        rfl

theorem cell23_2988195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_2988195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988195 prefixEnd_2988195 := by exact prefixLift 2988195
  have htrace : WordTrace (prefixWord ++ tailWord_2988195) baseStart_2988195 baseEnd_2988195 := by
    simpa [prefixWord, tailWord_2988195, baseEnd_2988195] using wordTrace_append hprefix tailTrace_2988195
  have hstable : (prefixWord ++ tailWord_2988195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988195).length < 2 ^ (prefixWord ++ tailWord_2988195).sum := by decide
  have hdescent : baseEnd_2988195 < baseStart_2988195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988196 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 6]
def baseStart_2988196 : Nat := 118140960795 + 2988196 * 2 ^ 59
def prefixEnd_2988196 : Nat := 4983230072969 + 3 ^ 40 * 2988196 * 2
def baseEnd_2988196 : Nat := 170486759760299544789727

theorem tailTrace_2988196 : CollatzResearch.WordTrace tailWord_2988196 prefixEnd_2988196 170486759760299544789727 := by
  unfold tailWord_2988196
  simp only [CollatzResearch.WordTrace]
  refine ⟨54494230941141855045704221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72658974588189140060938961 54494230941141855045704221)
  ·
    refine ⟨20435336602928195642139083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54494230941141855045704221 20435336602928195642139083)
    ·
      refine ⟨30653004904392293463208625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20435336602928195642139083 30653004904392293463208625)
      ·
        refine ⟨22989753678294220097406469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30653004904392293463208625 22989753678294220097406469)
        ·
          refine ⟨4310578814680166268263713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22989753678294220097406469 4310578814680166268263713)
          ·
            refine ⟨3232934111010124701197785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310578814680166268263713 3232934111010124701197785)
            ·
              refine ⟨2424700583257593525898339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232934111010124701197785 2424700583257593525898339)
              ·
                refine ⟨3637050874886390288847509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424700583257593525898339 3637050874886390288847509)
                ·
                  refine ⟨170486759760299544789727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3637050874886390288847509 170486759760299544789727)
                  ·
                    rfl

theorem cell23_2988196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_2988196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988196 prefixEnd_2988196 := by exact prefixLift 2988196
  have htrace : WordTrace (prefixWord ++ tailWord_2988196) baseStart_2988196 baseEnd_2988196 := by
    simpa [prefixWord, tailWord_2988196, baseEnd_2988196] using wordTrace_append hprefix tailTrace_2988196
  have hstable : (prefixWord ++ tailWord_2988196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988196).length < 2 ^ (prefixWord ++ tailWord_2988196).sum := by decide
  have hdescent : baseEnd_2988196 < baseStart_2988196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988209 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 3, 5]
def baseStart_2988209 : Nat := 118140960795 + 2988209 * 2 ^ 59
def prefixEnd_2988209 : Nat := 4983230072969 + 3 ^ 40 * 2988209 * 2
def baseEnd_2988209 : Nat := 511462504363734784081661

theorem tailTrace_2988209 : CollatzResearch.WordTrace tailWord_2988209 prefixEnd_2988209 511462504363734784081661 := by
  unfold tailWord_2988209
  simp only [CollatzResearch.WordTrace]
  refine ⟨108988936031236613311631681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72659290687491075541087787 108988936031236613311631681)
  ·
    refine ⟨81741702023427459983723761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108988936031236613311631681 81741702023427459983723761)
    ·
      refine ⟨61306276517570594987792821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81741702023427459983723761 61306276517570594987792821)
      ·
        refine ⟨5747463423522243280105577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61306276517570594987792821 5747463423522243280105577)
        ·
          refine ⟨4310597567641682460079183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5747463423522243280105577 4310597567641682460079183)
          ·
            refine ⟨6465896351462523690118775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4310597567641682460079183 6465896351462523690118775)
            ·
              refine ⟨9698844527193785535178163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6465896351462523690118775 9698844527193785535178163)
              ·
                refine ⟨14548266790790678302767245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9698844527193785535178163 14548266790790678302767245)
                ·
                  refine ⟨5455600046546504363537717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14548266790790678302767245 5455600046546504363537717)
                  ·
                    refine ⟨511462504363734784081661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5455600046546504363537717 511462504363734784081661)
                    ·
                      rfl

theorem cell23_2988209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_2988209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988209 prefixEnd_2988209 := by exact prefixLift 2988209
  have htrace : WordTrace (prefixWord ++ tailWord_2988209) baseStart_2988209 baseEnd_2988209 := by
    simpa [prefixWord, tailWord_2988209, baseEnd_2988209] using wordTrace_append hprefix tailTrace_2988209
  have hstable : (prefixWord ++ tailWord_2988209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988209).length < 2 ^ (prefixWord ++ tailWord_2988209).sum := by decide
  have hdescent : baseEnd_2988209 < baseStart_2988209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988239 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 2, 4]
def baseStart_2988239 : Nat := 118140960795 + 2988239 * 2 ^ 59
def prefixEnd_2988239 : Nat := 4983230072969 + 3 ^ 40 * 2988239 * 2
def baseEnd_2988239 : Nat := 511467639170279744956615

theorem tailTrace_2988239 : CollatzResearch.WordTrace tailWord_2988239 prefixEnd_2988239 511467639170279744956615 := by
  unfold tailWord_2988239
  simp only [CollatzResearch.WordTrace]
  refine ⟨108990030221127928435223771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72660020147418618956815847 108990030221127928435223771)
  ·
    refine ⟨163485045331691892652835657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108990030221127928435223771 163485045331691892652835657)
    ·
      refine ⟨122613783998768919489626743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163485045331691892652835657 122613783998768919489626743)
      ·
        refine ⟨183920675998153379234440115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122613783998768919489626743 183920675998153379234440115)
        ·
          refine ⟨275881013997230068851660173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183920675998153379234440115 275881013997230068851660173)
          ·
            refine ⟨103455380248961275819372565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275881013997230068851660173 103455380248961275819372565)
            ·
              refine ⟨4849470949170059804033089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103455380248961275819372565 4849470949170059804033089)
              ·
                refine ⟨3637103211877544853024817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4849470949170059804033089 3637103211877544853024817)
                ·
                  refine ⟨2727827408908158639768613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3637103211877544853024817 2727827408908158639768613)
                  ·
                    refine ⟨511467639170279744956615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2727827408908158639768613 511467639170279744956615)
                    ·
                      rfl

theorem cell23_2988239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 4].length) (baseStart_2988239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988239 prefixEnd_2988239 := by exact prefixLift 2988239
  have htrace : WordTrace (prefixWord ++ tailWord_2988239) baseStart_2988239 baseEnd_2988239 := by
    simpa [prefixWord, tailWord_2988239, baseEnd_2988239] using wordTrace_append hprefix tailTrace_2988239
  have hstable : (prefixWord ++ tailWord_2988239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988239).length < 2 ^ (prefixWord ++ tailWord_2988239).sum := by decide
  have hdescent : baseEnd_2988239 < baseStart_2988239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988246 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2988246 : Nat := 118140960795 + 2988246 * 2 ^ 59
def prefixEnd_2988246 : Nat := 4983230072969 + 3 ^ 40 * 2988246 * 2
def baseEnd_2988246 : Nat := 1534406511875420707482313

theorem tailTrace_2988246 : CollatzResearch.WordTrace tailWord_2988246 prefixEnd_2988246 1534406511875420707482313 := by
  unfold tailWord_2988246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811892845756410539420537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72660190354735045753819061 6811892845756410539420537)
  ·
    refine ⟨5108919634317307904565403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6811892845756410539420537 5108919634317307904565403)
    ·
      refine ⟨7663379451475961856848105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5108919634317307904565403 7663379451475961856848105)
      ·
        refine ⟨5747534588606971392636079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7663379451475961856848105 5747534588606971392636079)
        ·
          refine ⟨8621301882910457088954119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747534588606971392636079 8621301882910457088954119)
          ·
            refine ⟨12931952824365685633431179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621301882910457088954119 12931952824365685633431179)
            ·
              refine ⟨19397929236548528450146769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12931952824365685633431179 19397929236548528450146769)
              ·
                refine ⟨14548446927411396337610077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19397929236548528450146769 14548446927411396337610077)
                ·
                  refine ⟨5455667597779273626603779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14548446927411396337610077 5455667597779273626603779)
                  ·
                    refine ⟨8183501396668910439905669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5455667597779273626603779 8183501396668910439905669)
                    ·
                      refine ⟨1534406511875420707482313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8183501396668910439905669 1534406511875420707482313)
                      ·
                        rfl

theorem cell23_2988246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2988246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988246 prefixEnd_2988246 := by exact prefixLift 2988246
  have htrace : WordTrace (prefixWord ++ tailWord_2988246) baseStart_2988246 baseEnd_2988246 := by
    simpa [prefixWord, tailWord_2988246, baseEnd_2988246] using wordTrace_append hprefix tailTrace_2988246
  have hstable : (prefixWord ++ tailWord_2988246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988246).length < 2 ^ (prefixWord ++ tailWord_2988246).sum := by decide
  have hdescent : baseEnd_2988246 < baseStart_2988246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988263 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2988263 : Nat := 118140960795 + 2988263 * 2 ^ 59
def prefixEnd_2988263 : Nat := 4983230072969 + 3 ^ 40 * 2988263 * 2
def baseEnd_2988263 : Nat := 1534415241046547140969735

theorem tailTrace_2988263 : CollatzResearch.WordTrace tailWord_2988263 prefixEnd_2988263 1534415241046547140969735 := by
  unfold tailWord_2988263
  simp only [CollatzResearch.WordTrace]
  refine ⟨108990905573040980534097443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72660603715360653689398295 108990905573040980534097443)
  ·
    refine ⟨163486358359561470801146165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108990905573040980534097443 163486358359561470801146165)
    ·
      refine ⟨15326846096208887887607453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163486358359561470801146165 15326846096208887887607453)
      ·
        refine ⟨5747567286078332957852795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15326846096208887887607453 5747567286078332957852795)
        ·
          refine ⟨8621350929117499436779193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747567286078332957852795 8621350929117499436779193)
          ·
            refine ⟨6466013196838124577584395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8621350929117499436779193 6466013196838124577584395)
            ·
              refine ⟨9699019795257186866376593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6466013196838124577584395 9699019795257186866376593)
              ·
                refine ⟨7274264846442890149782445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9699019795257186866376593 7274264846442890149782445)
                ·
                  refine ⟨2727849317416083806168417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7274264846442890149782445 2727849317416083806168417)
                  ·
                    refine ⟨2045886988062062854626313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727849317416083806168417 2045886988062062854626313)
                    ·
                      refine ⟨1534415241046547140969735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045886988062062854626313 1534415241046547140969735)
                      ·
                        rfl

theorem cell23_2988263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2988263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988263 prefixEnd_2988263 := by exact prefixLift 2988263
  have htrace : WordTrace (prefixWord ++ tailWord_2988263) baseStart_2988263 baseEnd_2988263 := by
    simpa [prefixWord, tailWord_2988263, baseEnd_2988263] using wordTrace_append hprefix tailTrace_2988263
  have hstable : (prefixWord ++ tailWord_2988263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988263).length < 2 ^ (prefixWord ++ tailWord_2988263).sum := by decide
  have hdescent : baseEnd_2988263 < baseStart_2988263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988296 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2988296 : Nat := 118140960795 + 2988296 * 2 ^ 59
def prefixEnd_2988296 : Nat := 4983230072969 + 3 ^ 40 * 2988296 * 2
def baseEnd_2988296 : Nat := 1534432185908145511857083

theorem tailTrace_2988296 : CollatzResearch.WordTrace tailWord_2988296 prefixEnd_2988296 1534432185908145511857083 := by
  unfold tailWord_2988296
  simp only [CollatzResearch.WordTrace]
  refine ⟨54496054590960713585024371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72661406121280951446699161 54496054590960713585024371)
  ·
    refine ⟨81744081886441070377536557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54496054590960713585024371 81744081886441070377536557)
    ·
      refine ⟨30654030707415401391576209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81744081886441070377536557 30654030707415401391576209)
      ·
        refine ⟨22990523030561551043682157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30654030707415401391576209 22990523030561551043682157)
        ·
          refine ⟨8621446136460581641380809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22990523030561551043682157 8621446136460581641380809)
          ·
            refine ⟨6466084602345436231035607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8621446136460581641380809 6466084602345436231035607)
            ·
              refine ⟨9699126903518154346553411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6466084602345436231035607 9699126903518154346553411)
              ·
                refine ⟨14548690355277231519830117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9699126903518154346553411 14548690355277231519830117)
                ·
                  refine ⟨2727879441614480909968147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14548690355277231519830117 2727879441614480909968147)
                  ·
                    refine ⟨4091819162421721364952221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2727879441614480909968147 4091819162421721364952221)
                    ·
                      refine ⟨1534432185908145511857083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4091819162421721364952221 1534432185908145511857083)
                      ·
                        rfl

theorem cell23_2988296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2988296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988296 prefixEnd_2988296 := by exact prefixLift 2988296
  have htrace : WordTrace (prefixWord ++ tailWord_2988296) baseStart_2988296 baseEnd_2988296 := by
    simpa [prefixWord, tailWord_2988296, baseEnd_2988296] using wordTrace_append hprefix tailTrace_2988296
  have hstable : (prefixWord ++ tailWord_2988296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988296).length < 2 ^ (prefixWord ++ tailWord_2988296).sum := by decide
  have hdescent : baseEnd_2988296 < baseStart_2988296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988312 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 2, 6]
def baseStart_2988312 : Nat := 118140960795 + 2988312 * 2 ^ 59
def prefixEnd_2988312 : Nat := 4983230072969 + 3 ^ 40 * 2988312 * 2
def baseEnd_2988312 : Nat := 511480133866205816419003

theorem tailTrace_2988312 : CollatzResearch.WordTrace tailWord_2988312 prefixEnd_2988312 511480133866205816419003 := by
  unfold tailWord_2988312
  simp only [CollatzResearch.WordTrace]
  refine ⟨54496346374931730951315595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72661795166575641268420793 54496346374931730951315595)
  ·
    refine ⟨81744519562397596426973393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54496346374931730951315595 81744519562397596426973393)
    ·
      refine ⟨61308389671798197320230045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81744519562397596426973393 61308389671798197320230045)
      ·
        refine ⟨22990646126924323995086267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61308389671798197320230045 22990646126924323995086267)
        ·
          refine ⟨34485969190386485992629401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22990646126924323995086267 34485969190386485992629401)
          ·
            refine ⟨25864476892789864494472051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34485969190386485992629401 25864476892789864494472051)
            ·
              refine ⟨38796715339184796741708077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25864476892789864494472051 38796715339184796741708077)
              ·
                refine ⟨14548768252194298778140529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38796715339184796741708077 14548768252194298778140529)
                ·
                  refine ⟨10911576189145724083605397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14548768252194298778140529 10911576189145724083605397)
                  ·
                    refine ⟨511480133866205816419003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10911576189145724083605397 511480133866205816419003)
                    ·
                      rfl

theorem cell23_2988312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_2988312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988312 prefixEnd_2988312 := by exact prefixLift 2988312
  have htrace : WordTrace (prefixWord ++ tailWord_2988312) baseStart_2988312 baseEnd_2988312 := by
    simpa [prefixWord, tailWord_2988312, baseEnd_2988312] using wordTrace_append hprefix tailTrace_2988312
  have hstable : (prefixWord ++ tailWord_2988312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988312).length < 2 ^ (prefixWord ++ tailWord_2988312).sum := by decide
  have hdescent : baseEnd_2988312 < baseStart_2988312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988332 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_2988332 : Nat := 118140960795 + 2988332 * 2 ^ 59
def prefixEnd_2988332 : Nat := 4983230072969 + 3 ^ 40 * 2988332 * 2
def baseEnd_2988332 : Nat := 1534450671211707371006917

theorem tailTrace_2988332 : CollatzResearch.WordTrace tailWord_2988332 prefixEnd_2988332 1534450671211707371006917 := by
  unfold tailWord_2988332
  simp only [CollatzResearch.WordTrace]
  refine ⟨54496711104895502659179625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72662281473194003545572833 54496711104895502659179625)
  ·
    refine ⟨40872533328671626994384719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54496711104895502659179625 40872533328671626994384719)
    ·
      refine ⟨61308799993007440491577079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40872533328671626994384719 61308799993007440491577079)
      ·
        refine ⟨91963199989511160737365619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61308799993007440491577079 91963199989511160737365619)
        ·
          refine ⟨137944799984266741106048429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91963199989511160737365619 137944799984266741106048429)
          ·
            refine ⟨51729299994100027914768161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137944799984266741106048429 51729299994100027914768161)
            ·
              refine ⟨38796974995575020936076121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51729299994100027914768161 38796974995575020936076121)
              ·
                refine ⟨29097731246681265702057091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38796974995575020936076121 29097731246681265702057091)
                ·
                  refine ⟨43646596870021898553085637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29097731246681265702057091 43646596870021898553085637)
                  ·
                    refine ⟨8183736913129105978703557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43646596870021898553085637 8183736913129105978703557)
                    ·
                      refine ⟨1534450671211707371006917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8183736913129105978703557 1534450671211707371006917)
                      ·
                        rfl

theorem cell23_2988332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_2988332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988332 prefixEnd_2988332 := by exact prefixLift 2988332
  have htrace : WordTrace (prefixWord ++ tailWord_2988332) baseStart_2988332 baseEnd_2988332 := by
    simpa [prefixWord, tailWord_2988332, baseEnd_2988332] using wordTrace_append hprefix tailTrace_2988332
  have hstable : (prefixWord ++ tailWord_2988332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988332).length < 2 ^ (prefixWord ++ tailWord_2988332).sum := by decide
  have hdescent : baseEnd_2988332 < baseStart_2988332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988370 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_2988370 : Nat := 118140960795 + 2988370 * 2 ^ 59
def prefixEnd_2988370 : Nat := 4983230072969 + 3 ^ 40 * 2988370 * 2
def baseEnd_2988370 : Nat := 1534470183476578222331743

theorem tailTrace_2988370 : CollatzResearch.WordTrace tailWord_2988370 prefixEnd_2988370 1534470183476578222331743 := by
  unfold tailWord_2988370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27248702045913334452060641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72663205455768891872161709 27248702045913334452060641)
  ·
    refine ⟨20436526534435000839045481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27248702045913334452060641 20436526534435000839045481)
    ·
      refine ⟨15327394900826250629284111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20436526534435000839045481 15327394900826250629284111)
      ·
        refine ⟨22991092351239375943926167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15327394900826250629284111 22991092351239375943926167)
        ·
          refine ⟨34486638526859063915889251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22991092351239375943926167 34486638526859063915889251)
          ·
            refine ⟨51729957790288595873833877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34486638526859063915889251 51729957790288595873833877)
            ·
              refine ⟨2424841771419777931585963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51729957790288595873833877 2424841771419777931585963)
              ·
                refine ⟨3637262657129666897378945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424841771419777931585963 3637262657129666897378945)
                ·
                  refine ⟨2727946992847250173034209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3637262657129666897378945 2727946992847250173034209)
                  ·
                    refine ⟨2045960244635437629775657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727946992847250173034209 2045960244635437629775657)
                    ·
                      refine ⟨1534470183476578222331743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2045960244635437629775657 1534470183476578222331743)
                      ·
                        rfl

theorem cell23_2988370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_2988370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988370 prefixEnd_2988370 := by exact prefixLift 2988370
  have htrace : WordTrace (prefixWord ++ tailWord_2988370) baseStart_2988370 baseEnd_2988370 := by
    simpa [prefixWord, tailWord_2988370, baseEnd_2988370] using wordTrace_append hprefix tailTrace_2988370
  have hstable : (prefixWord ++ tailWord_2988370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988370).length < 2 ^ (prefixWord ++ tailWord_2988370).sum := by decide
  have hdescent : baseEnd_2988370 < baseStart_2988370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988389 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_2988389 : Nat := 118140960795 + 2988389 * 2 ^ 59
def prefixEnd_2988389 : Nat := 4983230072969 + 3 ^ 40 * 2988389 * 2
def baseEnd_2988389 : Nat := 511493313203004549331385

theorem tailTrace_2988389 : CollatzResearch.WordTrace tailWord_2988389 prefixEnd_2988389 511493313203004549331385 := by
  unfold tailWord_2988389
  simp only [CollatzResearch.WordTrace]
  refine ⟨108995501170584504053184221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72663667447056336035456147 108995501170584504053184221)
  ·
    refine ⟨40873312938969189019944083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108995501170584504053184221 40873312938969189019944083)
    ·
      refine ⟨61309969408453783529916125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40873312938969189019944083 61309969408453783529916125)
      ·
        refine ⟨22991238528170168823718547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61309969408453783529916125 22991238528170168823718547)
        ·
          refine ⟨34486857792255253235577821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22991238528170168823718547 34486857792255253235577821)
          ·
            refine ⟨12932571672095719963341683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34486857792255253235577821 12932571672095719963341683)
            ·
              refine ⟨19398857508143579945012525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12932571672095719963341683 19398857508143579945012525)
              ·
                refine ⟨7274571565553842479379697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19398857508143579945012525 7274571565553842479379697)
                ·
                  refine ⟨5455928674165381859534773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7274571565553842479379697 5455928674165381859534773)
                  ·
                    refine ⟨511493313203004549331385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5455928674165381859534773 511493313203004549331385)
                    ·
                      rfl

theorem cell23_2988389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_2988389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988389 prefixEnd_2988389 := by exact prefixLift 2988389
  have htrace : WordTrace (prefixWord ++ tailWord_2988389) baseStart_2988389 baseEnd_2988389 := by
    simpa [prefixWord, tailWord_2988389, baseEnd_2988389] using wordTrace_append hprefix tailTrace_2988389
  have hstable : (prefixWord ++ tailWord_2988389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988389).length < 2 ^ (prefixWord ++ tailWord_2988389).sum := by decide
  have hdescent : baseEnd_2988389 < baseStart_2988389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988453 : List Nat := [1, 3, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_2988453 : Nat := 118140960795 + 2988453 * 2 ^ 59
def prefixEnd_2988453 : Nat := 4983230072969 + 3 ^ 40 * 2988453 * 2
def baseEnd_2988453 : Nat := 511504267456967132531287

theorem tailTrace_2988453 : CollatzResearch.WordTrace tailWord_2988453 prefixEnd_2988453 511504267456967132531287 := by
  unfold tailWord_2988453
  simp only [CollatzResearch.WordTrace]
  refine ⟨108997835442352642983514013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72665223628235095322342675 108997835442352642983514013)
  ·
    refine ⟨40874188290882241118817755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108997835442352642983514013 40874188290882241118817755)
    ·
      refine ⟨61311282436323361678226633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40874188290882241118817755 61311282436323361678226633)
      ·
        refine ⟨45983461827242521258669975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61311282436323361678226633 45983461827242521258669975)
        ·
          refine ⟨68975192740863781888004963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45983461827242521258669975 68975192740863781888004963)
          ·
            refine ⟨103462789111295672832007445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68975192740863781888004963 103462789111295672832007445)
            ·
              refine ⟨4849818239591984664000349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103462789111295672832007445 4849818239591984664000349)
              ·
                refine ⟨1818681839846994249000131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4849818239591984664000349 1818681839846994249000131)
                ·
                  refine ⟨2728022759770491373500197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818681839846994249000131 2728022759770491373500197)
                  ·
                    refine ⟨511504267456967132531287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2728022759770491373500197 511504267456967132531287)
                    ·
                      rfl

theorem cell23_2988453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_2988453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988453 prefixEnd_2988453 := by exact prefixLift 2988453
  have htrace : WordTrace (prefixWord ++ tailWord_2988453) baseStart_2988453 baseEnd_2988453 := by
    simpa [prefixWord, tailWord_2988453, baseEnd_2988453] using wordTrace_append hprefix tailTrace_2988453
  have hstable : (prefixWord ++ tailWord_2988453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988453).length < 2 ^ (prefixWord ++ tailWord_2988453).sum := by decide
  have hdescent : baseEnd_2988453 < baseStart_2988453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988456 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2988456 : Nat := 118140960795 + 2988456 * 2 ^ 59
def prefixEnd_2988456 : Nat := 4983230072969 + 3 ^ 40 * 2988456 * 2
def baseEnd_2988456 : Nat := 1534514342812864885856347

theorem tailTrace_2988456 : CollatzResearch.WordTrace tailWord_2988456 prefixEnd_2988456 1534514342812864885856347 := by
  unfold tailWord_2988456
  simp only [CollatzResearch.WordTrace]
  refine ⟨54498972430670887247936611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72665296574227849663915481 54498972430670887247936611)
  ·
    refine ⟨81748458646006330871904917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54498972430670887247936611 81748458646006330871904917)
    ·
      refine ⟨3831958999031546759620543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81748458646006330871904917 3831958999031546759620543)
      ·
        refine ⟨5747938498547320139430815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3831958999031546759620543 5747938498547320139430815)
        ·
          refine ⟨8621907747820980209146223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747938498547320139430815 8621907747820980209146223)
          ·
            refine ⟨12932861621731470313719335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621907747820980209146223 12932861621731470313719335)
            ·
              refine ⟨19399292432597205470579003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12932861621731470313719335 19399292432597205470579003)
              ·
                refine ⟨29098938648895808205868505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19399292432597205470579003 29098938648895808205868505)
                ·
                  refine ⟨21824203986671856154401379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29098938648895808205868505 21824203986671856154401379)
                  ·
                    refine ⟨32736305980007784231602069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21824203986671856154401379 32736305980007784231602069)
                    ·
                      refine ⟨1534514342812864885856347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32736305980007784231602069 1534514342812864885856347)
                      ·
                        rfl

theorem cell23_2988456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2988456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988456 prefixEnd_2988456 := by exact prefixLift 2988456
  have htrace : WordTrace (prefixWord ++ tailWord_2988456) baseStart_2988456 baseEnd_2988456 := by
    simpa [prefixWord, tailWord_2988456, baseEnd_2988456] using wordTrace_append hprefix tailTrace_2988456
  have hstable : (prefixWord ++ tailWord_2988456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988456).length < 2 ^ (prefixWord ++ tailWord_2988456).sum := by decide
  have hdescent : baseEnd_2988456 < baseStart_2988456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988499 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 4]
def baseStart_2988499 : Nat := 118140960795 + 2988499 * 2 ^ 59
def prefixEnd_2988499 : Nat := 4983230072969 + 3 ^ 40 * 2988499 * 2
def baseEnd_2988499 : Nat := 1534536422481008217618649

theorem tailTrace_2988499 : CollatzResearch.WordTrace tailWord_2988499 prefixEnd_2988499 1534536422481008217618649 := by
  unfold tailWord_2988499
  simp only [CollatzResearch.WordTrace]
  refine ⟨108999513200185992839688551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72666342133457328559792367 108999513200185992839688551)
  ·
    refine ⟨163499269800278989259532827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108999513200185992839688551 163499269800278989259532827)
    ·
      refine ⟨245248904700418483889299241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163499269800278989259532827 245248904700418483889299241)
      ·
        refine ⟨183936678525313862916974431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245248904700418483889299241 183936678525313862916974431)
        ·
          refine ⟨275905017787970794375461647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183936678525313862916974431 275905017787970794375461647)
          ·
            refine ⟨413857526681956191563192471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275905017787970794375461647 413857526681956191563192471)
            ·
              refine ⟨620786290022934287344788707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413857526681956191563192471 620786290022934287344788707)
              ·
                refine ⟨931179435034401431017183061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620786290022934287344788707 931179435034401431017183061)
                ·
                  refine ⟨5456129502154695884866307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 931179435034401431017183061 5456129502154695884866307)
                  ·
                    refine ⟨8184194253232043827299461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5456129502154695884866307 8184194253232043827299461)
                    ·
                      refine ⟨1534536422481008217618649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8184194253232043827299461 1534536422481008217618649)
                      ·
                        rfl

theorem cell23_2988499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_2988499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988499 prefixEnd_2988499 := by exact prefixLift 2988499
  have htrace : WordTrace (prefixWord ++ tailWord_2988499) baseStart_2988499 baseEnd_2988499 := by
    simpa [prefixWord, tailWord_2988499, baseEnd_2988499] using wordTrace_append hprefix tailTrace_2988499
  have hstable : (prefixWord ++ tailWord_2988499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988499).length < 2 ^ (prefixWord ++ tailWord_2988499).sum := by decide
  have hdescent : baseEnd_2988499 < baseStart_2988499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988529 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2988529 : Nat := 118140960795 + 2988529 * 2 ^ 59
def prefixEnd_2988529 : Nat := 4983230072969 + 3 ^ 40 * 2988529 * 2
def baseEnd_2988529 : Nat := 1534551826900643100243511

theorem tailTrace_2988529 : CollatzResearch.WordTrace tailWord_2988529 prefixEnd_2988529 1534551826900643100243511 := by
  unfold tailWord_2988529
  simp only [CollatzResearch.WordTrace]
  refine ⟨109000607390077307963280641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72667071593384871975520427 109000607390077307963280641)
  ·
    refine ⟨81750455542557980972460481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109000607390077307963280641 81750455542557980972460481)
    ·
      refine ⟨61312841656918485729345361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81750455542557980972460481 61312841656918485729345361)
      ·
        refine ⟨45984631242688864297009021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61312841656918485729345361 45984631242688864297009021)
        ·
          refine ⟨17244236716008324111378383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45984631242688864297009021 17244236716008324111378383)
          ·
            refine ⟨25866355074012486167067575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17244236716008324111378383 25866355074012486167067575)
            ·
              refine ⟨38799532611018729250601363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25866355074012486167067575 38799532611018729250601363)
              ·
                refine ⟨58199298916528093875902045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38799532611018729250601363 58199298916528093875902045)
                ·
                  refine ⟨21824737093698035203463267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58199298916528093875902045 21824737093698035203463267)
                  ·
                    refine ⟨32737105640547052805194901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21824737093698035203463267 32737105640547052805194901)
                    ·
                      refine ⟨1534551826900643100243511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32737105640547052805194901 1534551826900643100243511)
                      ·
                        rfl

theorem cell23_2988529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2988529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988529 prefixEnd_2988529 := by exact prefixLift 2988529
  have htrace : WordTrace (prefixWord ++ tailWord_2988529) baseStart_2988529 baseEnd_2988529 := by
    simpa [prefixWord, tailWord_2988529, baseEnd_2988529] using wordTrace_append hprefix tailTrace_2988529
  have hstable : (prefixWord ++ tailWord_2988529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988529).length < 2 ^ (prefixWord ++ tailWord_2988529).sum := by decide
  have hdescent : baseEnd_2988529 < baseStart_2988529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988536 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_2988536 : Nat := 118140960795 + 2988536 * 2 ^ 59
def prefixEnd_2988536 : Nat := 4983230072969 + 3 ^ 40 * 2988536 * 2
def baseEnd_2988536 : Nat := 1534555421265224572855979

theorem tailTrace_2988536 : CollatzResearch.WordTrace tailWord_2988536 prefixEnd_2988536 1534555421265224572855979 := by
  unfold tailWord_2988536
  simp only [CollatzResearch.WordTrace]
  refine ⟨54500431350525974079392731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72667241800701298772523641 54500431350525974079392731)
  ·
    refine ⟨81750647025788961119089097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54500431350525974079392731 81750647025788961119089097)
    ·
      refine ⟨61312985269341720839316823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81750647025788961119089097 61312985269341720839316823)
      ·
        refine ⟨91969477904012581258975235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61312985269341720839316823 91969477904012581258975235)
        ·
          refine ⟨137954216856018871888462853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91969477904012581258975235 137954216856018871888462853)
          ·
            refine ⟨25866415660503538479086785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137954216856018871888462853 25866415660503538479086785)
            ·
              refine ⟨19399811745377653859315089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25866415660503538479086785 19399811745377653859315089)
              ·
                refine ⟨14549858809033240394486317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19399811745377653859315089 14549858809033240394486317)
                ·
                  refine ⟨5456197053387465147932369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14549858809033240394486317 5456197053387465147932369)
                  ·
                    refine ⟨4092147790040598860949277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5456197053387465147932369 4092147790040598860949277)
                    ·
                      refine ⟨1534555421265224572855979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4092147790040598860949277 1534555421265224572855979)
                      ·
                        rfl

theorem cell23_2988536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_2988536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988536 prefixEnd_2988536 := by exact prefixLift 2988536
  have htrace : WordTrace (prefixWord ++ tailWord_2988536) baseStart_2988536 baseEnd_2988536 := by
    simpa [prefixWord, tailWord_2988536, baseEnd_2988536] using wordTrace_append hprefix tailTrace_2988536
  have hstable : (prefixWord ++ tailWord_2988536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988536).length < 2 ^ (prefixWord ++ tailWord_2988536).sum := by decide
  have hdescent : baseEnd_2988536 < baseStart_2988536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988567 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2988567 : Nat := 118140960795 + 2988567 * 2 ^ 59
def prefixEnd_2988567 : Nat := 4983230072969 + 3 ^ 40 * 2988567 * 2
def baseEnd_2988567 : Nat := 1534571339165513951568337

theorem tailTrace_2988567 : CollatzResearch.WordTrace tailWord_2988567 prefixEnd_2988567 1534571339165513951568337 := by
  unfold tailWord_2988567
  simp only [CollatzResearch.WordTrace]
  refine ⟨109001993363939640453163955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72667995575959760302109303 109001993363939640453163955)
  ·
    refine ⟨163502990045909460679745933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109001993363939640453163955 163502990045909460679745933)
    ·
      refine ⟨61313621267216047754904725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163502990045909460679745933 61313621267216047754904725)
      ·
        refine ⟨2874075996900752238511159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61313621267216047754904725 2874075996900752238511159)
        ·
          refine ⟨4311113995351128357766739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874075996900752238511159 4311113995351128357766739)
          ·
            refine ⟨6466670993026692536650109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4311113995351128357766739 6466670993026692536650109)
            ·
              refine ⟨2425001622385009701243791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6466670993026692536650109 2425001622385009701243791)
              ·
                refine ⟨3637502433577514551865687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425001622385009701243791 3637502433577514551865687)
                ·
                  refine ⟨5456253650366271827798531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3637502433577514551865687 5456253650366271827798531)
                  ·
                    refine ⟨8184380475549407741697797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5456253650366271827798531 8184380475549407741697797)
                    ·
                      refine ⟨1534571339165513951568337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8184380475549407741697797 1534571339165513951568337)
                      ·
                        rfl

theorem cell23_2988567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2988567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988567 prefixEnd_2988567 := by exact prefixLift 2988567
  have htrace : WordTrace (prefixWord ++ tailWord_2988567) baseStart_2988567 baseEnd_2988567 := by
    simpa [prefixWord, tailWord_2988567, baseEnd_2988567] using wordTrace_append hprefix tailTrace_2988567
  have hstable : (prefixWord ++ tailWord_2988567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988567).length < 2 ^ (prefixWord ++ tailWord_2988567).sum := by decide
  have hdescent : baseEnd_2988567 < baseStart_2988567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988584 : List Nat := [2, 1, 5, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2988584 : Nat := 118140960795 + 2988584 * 2 ^ 59
def prefixEnd_2988584 : Nat := 4983230072969 + 3 ^ 40 * 2988584 * 2
def baseEnd_2988584 : Nat := 1534580068336640385055759

theorem tailTrace_2988584 : CollatzResearch.WordTrace tailWord_2988584 prefixEnd_2988584 1534580068336640385055759 := by
  unfold tailWord_2988584
  simp only [CollatzResearch.WordTrace]
  refine ⟨54501306702439026178266403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72668408936585368237688537 54501306702439026178266403)
  ·
    refine ⟨81751960053658539267399605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54501306702439026178266403 81751960053658539267399605)
    ·
      refine ⟨7664246255030488056318713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81751960053658539267399605 7664246255030488056318713)
      ·
        refine ⟨5748184691272866042239035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7664246255030488056318713 5748184691272866042239035)
        ·
          refine ⟨8622277036909299063358553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748184691272866042239035 8622277036909299063358553)
          ·
            refine ⟨6466707777681974297518915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8622277036909299063358553 6466707777681974297518915)
            ·
              refine ⟨9700061666522961446278373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6466707777681974297518915 9700061666522961446278373)
              ·
                refine ⟨1818761562473055271177195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9700061666522961446278373 1818761562473055271177195)
                ·
                  refine ⟨2728142343709582906765793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818761562473055271177195 2728142343709582906765793)
                  ·
                    refine ⟨2046106757782187180074345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2728142343709582906765793 2046106757782187180074345)
                    ·
                      refine ⟨1534580068336640385055759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046106757782187180074345 1534580068336640385055759)
                      ·
                        rfl

theorem cell23_2988584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2988584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988584 prefixEnd_2988584 := by exact prefixLift 2988584
  have htrace : WordTrace (prefixWord ++ tailWord_2988584) baseStart_2988584 baseEnd_2988584 := by
    simpa [prefixWord, tailWord_2988584, baseEnd_2988584] using wordTrace_append hprefix tailTrace_2988584
  have hstable : (prefixWord ++ tailWord_2988584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988584).length < 2 ^ (prefixWord ++ tailWord_2988584).sum := by decide
  have hdescent : baseEnd_2988584 < baseStart_2988584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988586 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2988586 : Nat := 118140960795 + 2988586 * 2 ^ 59
def prefixEnd_2988586 : Nat := 4983230072969 + 3 ^ 40 * 2988586 * 2
def baseEnd_2988586 : Nat := 511527031765983125743583

theorem tailTrace_2988586 : CollatzResearch.WordTrace tailWord_2988586 prefixEnd_2988586 511527031765983125743583 := by
  unfold tailWord_2988586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27250671587717701674526403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72668457567247204465403741 27250671587717701674526403)
  ·
    refine ⟨40876007381576552511789605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27250671587717701674526403 40876007381576552511789605)
    ·
      refine ⟨7664251384045603595960551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40876007381576552511789605 7664251384045603595960551)
      ·
        refine ⟨11496377076068405393940827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7664251384045603595960551 11496377076068405393940827)
        ·
          refine ⟨17244565614102608090911241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11496377076068405393940827 17244565614102608090911241)
          ·
            refine ⟨12933424210576956068183431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17244565614102608090911241 12933424210576956068183431)
            ·
              refine ⟨19400136315865434102275147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12933424210576956068183431 19400136315865434102275147)
              ·
                refine ⟨29100204473798151153412721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19400136315865434102275147 29100204473798151153412721)
                ·
                  refine ⟨21825153355348613365059541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29100204473798151153412721 21825153355348613365059541)
                  ·
                    refine ⟨511527031765983125743583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21825153355348613365059541 511527031765983125743583)
                    ·
                      rfl

theorem cell23_2988586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2988586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988586 prefixEnd_2988586 := by exact prefixLift 2988586
  have htrace : WordTrace (prefixWord ++ tailWord_2988586) baseStart_2988586 baseEnd_2988586 := by
    simpa [prefixWord, tailWord_2988586, baseEnd_2988586] using wordTrace_append hprefix tailTrace_2988586
  have hstable : (prefixWord ++ tailWord_2988586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988586).length < 2 ^ (prefixWord ++ tailWord_2988586).sum := by decide
  have hdescent : baseEnd_2988586 < baseStart_2988586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988590 : List Nat := [4, 1, 3, 1, 4, 1, 1, 8]
def baseStart_2988590 : Nat := 118140960795 + 2988590 * 2 ^ 59
def prefixEnd_2988590 : Nat := 4983230072969 + 3 ^ 40 * 2988590 * 2
def baseEnd_2988590 : Nat := 56836412934095087465953

theorem tailTrace_2988590 : CollatzResearch.WordTrace tailWord_2988590 prefixEnd_2988590 56836412934095087465953 := by
  unfold tailWord_2988590
  simp only [CollatzResearch.WordTrace]
  refine ⟨13625354030357039422656403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72668554828570876920834149 13625354030357039422656403)
  ·
    refine ⟨20438031045535559133984605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13625354030357039422656403 20438031045535559133984605)
    ·
      refine ⟨7664261642075834675244227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20438031045535559133984605 7664261642075834675244227)
      ·
        refine ⟨11496392463113752012866341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7664261642075834675244227 11496392463113752012866341)
        ·
          refine ⟨2155573586833828502412439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11496392463113752012866341 2155573586833828502412439)
          ·
            refine ⟨3233360380250742753618659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155573586833828502412439 3233360380250742753618659)
            ·
              refine ⟨4850040570376114130427989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233360380250742753618659 4850040570376114130427989)
              ·
                refine ⟨56836412934095087465953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4850040570376114130427989 56836412934095087465953)
                ·
                  rfl

theorem cell23_2988590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_2988590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988590 prefixEnd_2988590 := by exact prefixLift 2988590
  have htrace : WordTrace (prefixWord ++ tailWord_2988590) baseStart_2988590 baseEnd_2988590 := by
    simpa [prefixWord, tailWord_2988590, baseEnd_2988590] using wordTrace_append hprefix tailTrace_2988590
  have hstable : (prefixWord ++ tailWord_2988590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988590).length < 2 ^ (prefixWord ++ tailWord_2988590).sum := by decide
  have hdescent : baseEnd_2988590 < baseStart_2988590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988593 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 3, 3, 2]
def baseStart_2988593 : Nat := 118140960795 + 2988593 * 2 ^ 59
def prefixEnd_2988593 : Nat := 4983230072969 + 3 ^ 40 * 2988593 * 2
def baseEnd_2988593 : Nat := 1534584689662530849843217

theorem tailTrace_2988593 : CollatzResearch.WordTrace tailWord_2988593 prefixEnd_2988593 1534584689662530849843217 := by
  unfold tailWord_2988593
  simp only [CollatzResearch.WordTrace]
  refine ⟨109002941661845446893610433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72668627774563631262406955 109002941661845446893610433)
  ·
    refine ⟨81752206246384085170207825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109002941661845446893610433 81752206246384085170207825)
    ·
      refine ⟨61314154684788063877655869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81752206246384085170207825 61314154684788063877655869)
      ·
        refine ⟨22992808006795523954120951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61314154684788063877655869 22992808006795523954120951)
        ·
          refine ⟨34489212010193285931181427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22992808006795523954120951 34489212010193285931181427)
          ·
            refine ⟨51733818015289928896772141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34489212010193285931181427 51733818015289928896772141)
            ·
              refine ⟨19400181755733723336289553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51733818015289928896772141 19400181755733723336289553)
              ·
                refine ⟨14550136316800292502217165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19400181755733723336289553 14550136316800292502217165)
                ·
                  refine ⟨5456301118800109688331437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14550136316800292502217165 5456301118800109688331437)
                  ·
                    refine ⟨2046112919550041133124289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5456301118800109688331437 2046112919550041133124289)
                    ·
                      refine ⟨1534584689662530849843217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046112919550041133124289 1534584689662530849843217)
                      ·
                        rfl

theorem cell23_2988593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_2988593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988593 prefixEnd_2988593 := by exact prefixLift 2988593
  have htrace : WordTrace (prefixWord ++ tailWord_2988593) baseStart_2988593 baseEnd_2988593 := by
    simpa [prefixWord, tailWord_2988593, baseEnd_2988593] using wordTrace_append hprefix tailTrace_2988593
  have hstable : (prefixWord ++ tailWord_2988593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988593).length < 2 ^ (prefixWord ++ tailWord_2988593).sum := by decide
  have hdescent : baseEnd_2988593 < baseStart_2988593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988623 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 1, 4, 2]
def baseStart_2988623 : Nat := 118140960795 + 2988623 * 2 ^ 59
def prefixEnd_2988623 : Nat := 4983230072969 + 3 ^ 40 * 2988623 * 2
def baseEnd_2988623 : Nat := 1534600094082165732468079

theorem tailTrace_2988623 : CollatzResearch.WordTrace tailWord_2988623 prefixEnd_2988623 1534600094082165732468079 := by
  unfold tailWord_2988623
  simp only [CollatzResearch.WordTrace]
  refine ⟨109004035851736762017202523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72669357234491174678135015 109004035851736762017202523)
  ·
    refine ⟨163506053777605143025803785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109004035851736762017202523 163506053777605143025803785)
    ·
      refine ⟨122629540333203857269352839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163506053777605143025803785 122629540333203857269352839)
      ·
        refine ⟨183944310499805785904029259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122629540333203857269352839 183944310499805785904029259)
        ·
          refine ⟨275916465749708678856043889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183944310499805785904029259 275916465749708678856043889)
          ·
            refine ⟨206937349312281509142032917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275916465749708678856043889 206937349312281509142032917)
            ·
              refine ⟨9700188249013195741032793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206937349312281509142032917 9700188249013195741032793)
              ·
                refine ⟨7275141186759896805774595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9700188249013195741032793 7275141186759896805774595)
                ·
                  refine ⟨10912711780139845208661893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7275141186759896805774595 10912711780139845208661893)
                  ·
                    refine ⟨2046133458776220976624105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10912711780139845208661893 2046133458776220976624105)
                    ·
                      refine ⟨1534600094082165732468079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046133458776220976624105 1534600094082165732468079)
                      ·
                        rfl

theorem cell23_2988623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 4, 2].length) (baseStart_2988623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988623 prefixEnd_2988623 := by exact prefixLift 2988623
  have htrace : WordTrace (prefixWord ++ tailWord_2988623) baseStart_2988623 baseEnd_2988623 := by
    simpa [prefixWord, tailWord_2988623, baseEnd_2988623] using wordTrace_append hprefix tailTrace_2988623
  have hstable : (prefixWord ++ tailWord_2988623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988623).length < 2 ^ (prefixWord ++ tailWord_2988623).sum := by decide
  have hdescent : baseEnd_2988623 < baseStart_2988623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988626 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2988626 : Nat := 118140960795 + 2988626 * 2 ^ 59
def prefixEnd_2988626 : Nat := 4983230072969 + 3 ^ 40 * 2988626 * 2
def baseEnd_2988626 : Nat := 1534601634524129220730565

theorem tailTrace_2988626 : CollatzResearch.WordTrace tailWord_2988626 prefixEnd_2988626 1534601634524129220730565 := by
  unfold tailWord_2988626
  simp only [CollatzResearch.WordTrace]
  refine ⟨27251036317681473382390433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72669430180483929019707821 27251036317681473382390433)
  ·
    refine ⟨20438277238261105036792825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27251036317681473382390433 20438277238261105036792825)
    ·
      refine ⟨15328707928695828777594619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20438277238261105036792825 15328707928695828777594619)
      ·
        refine ⟨22993061893043743166391929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15328707928695828777594619 22993061893043743166391929)
        ·
          refine ⟨17244796419782807374793947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22993061893043743166391929 17244796419782807374793947)
          ·
            refine ⟨25867194629674211062190921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17244796419782807374793947 25867194629674211062190921)
            ·
              refine ⟨19400395972255658296643191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25867194629674211062190921 19400395972255658296643191)
              ·
                refine ⟨29100593958383487444964787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19400395972255658296643191 29100593958383487444964787)
                ·
                  refine ⟨43650890937575231167447181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29100593958383487444964787 43650890937575231167447181)
                  ·
                    refine ⟨16369084101590711687792693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43650890937575231167447181 16369084101590711687792693)
                    ·
                      refine ⟨1534601634524129220730565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16369084101590711687792693 1534601634524129220730565)
                      ·
                        rfl

theorem cell23_2988626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2988626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988626 prefixEnd_2988626 := by exact prefixLift 2988626
  have htrace : WordTrace (prefixWord ++ tailWord_2988626) baseStart_2988626 baseEnd_2988626 := by
    simpa [prefixWord, tailWord_2988626, baseEnd_2988626] using wordTrace_append hprefix tailTrace_2988626
  have hstable : (prefixWord ++ tailWord_2988626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988626).length < 2 ^ (prefixWord ++ tailWord_2988626).sum := by decide
  have hdescent : baseEnd_2988626 < baseStart_2988626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988653 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2988653 : Nat := 118140960795 + 2988653 * 2 ^ 59
def prefixEnd_2988653 : Nat := 4983230072969 + 3 ^ 40 * 2988653 * 2
def baseEnd_2988653 : Nat := 1534615498501800615092941

theorem tailTrace_2988653 : CollatzResearch.WordTrace tailWord_2988653 prefixEnd_2988653 1534615498501800615092941 := by
  unfold tailWord_2988653
  simp only [CollatzResearch.WordTrace]
  refine ⟨109005130041628077140794613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72670086694418718093863075 109005130041628077140794613)
  ·
    refine ⟨10219230941402632231949495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109005130041628077140794613 10219230941402632231949495)
    ·
      refine ⟨15328846412103948347924243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10219230941402632231949495 15328846412103948347924243)
      ·
        refine ⟨22993269618155922521886365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15328846412103948347924243 22993269618155922521886365)
        ·
          refine ⟨8622476106808470945707387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22993269618155922521886365 8622476106808470945707387)
          ·
            refine ⟨12933714160212706418561081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8622476106808470945707387 12933714160212706418561081)
            ·
              refine ⟨9700285620159529813920811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12933714160212706418561081 9700285620159529813920811)
              ·
                refine ⟨14550428430239294720881217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9700285620159529813920811 14550428430239294720881217)
                ·
                  refine ⟨10912821322679471040660913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14550428430239294720881217 10912821322679471040660913)
                  ·
                    refine ⟨8184615992009603280495685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10912821322679471040660913 8184615992009603280495685)
                    ·
                      refine ⟨1534615498501800615092941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8184615992009603280495685 1534615498501800615092941)
                      ·
                        rfl

theorem cell23_2988653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2988653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988653 prefixEnd_2988653 := by exact prefixLift 2988653
  have htrace : WordTrace (prefixWord ++ tailWord_2988653) baseStart_2988653 baseEnd_2988653 := by
    simpa [prefixWord, tailWord_2988653, baseEnd_2988653] using wordTrace_append hprefix tailTrace_2988653
  have hstable : (prefixWord ++ tailWord_2988653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988653).length < 2 ^ (prefixWord ++ tailWord_2988653).sum := by decide
  have hdescent : baseEnd_2988653 < baseStart_2988653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988750 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_2988750 : Nat := 118140960795 + 2988750 * 2 ^ 59
def prefixEnd_2988750 : Nat := 4983230072969 + 3 ^ 40 * 2988750 * 2
def baseEnd_2988750 : Nat := 1534665306125286735579995

theorem tailTrace_2988750 : CollatzResearch.WordTrace tailWord_2988750 prefixEnd_2988750 1534665306125286735579995 := by
  unfold tailWord_2988750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13626083490284582838384463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72672445281517775138050469 13626083490284582838384463)
  ·
    refine ⟨20439125235426874257576695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13626083490284582838384463 20439125235426874257576695)
    ·
      refine ⟨30658687853140311386365043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20439125235426874257576695 30658687853140311386365043)
      ·
        refine ⟨45988031779710467079547565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30658687853140311386365043 45988031779710467079547565)
        ·
          refine ⟨17245511917391425154830337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45988031779710467079547565 17245511917391425154830337)
          ·
            refine ⟨12934133938043568866122753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17245511917391425154830337 12934133938043568866122753)
            ·
              refine ⟨9700600453532676649592065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12934133938043568866122753 9700600453532676649592065)
              ·
                refine ⟨7275450340149507487194049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9700600453532676649592065 7275450340149507487194049)
                ·
                  refine ⟨5456587755112130615395537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7275450340149507487194049 5456587755112130615395537)
                  ·
                    refine ⟨4092440816334097961546653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5456587755112130615395537 4092440816334097961546653)
                    ·
                      refine ⟨1534665306125286735579995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4092440816334097961546653 1534665306125286735579995)
                      ·
                        rfl

theorem cell23_2988750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_2988750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988750 prefixEnd_2988750 := by exact prefixLift 2988750
  have htrace : WordTrace (prefixWord ++ tailWord_2988750) baseStart_2988750 baseEnd_2988750 := by
    simpa [prefixWord, tailWord_2988750, baseEnd_2988750] using wordTrace_append hprefix tailTrace_2988750
  have hstable : (prefixWord ++ tailWord_2988750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988750).length < 2 ^ (prefixWord ++ tailWord_2988750).sum := by decide
  have hdescent : baseEnd_2988750 < baseStart_2988750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988753 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 6]
def baseStart_2988753 : Nat := 118140960795 + 2988753 * 2 ^ 59
def prefixEnd_2988753 : Nat := 4983230072969 + 3 ^ 40 * 2988753 * 2
def baseEnd_2988753 : Nat := 170518538507472247093609

theorem tailTrace_2988753 : CollatzResearch.WordTrace tailWord_2988753 prefixEnd_2988753 170518538507472247093609 := by
  unfold tailWord_2988753
  simp only [CollatzResearch.WordTrace]
  refine ⟨109008777341265794219434913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72672518227510529479623275 109008777341265794219434913)
  ·
    refine ⟨81756583005949345664576185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109008777341265794219434913 81756583005949345664576185)
    ·
      refine ⟨61317437254462009248432139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81756583005949345664576185 61317437254462009248432139)
      ·
        refine ⟨91976155881693013872648209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61317437254462009248432139 91976155881693013872648209)
        ·
          refine ⟨68982116911269760404486157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91976155881693013872648209 68982116911269760404486157)
          ·
            refine ⟨25868293841726160151682309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68982116911269760404486157 25868293841726160151682309)
            ·
              refine ⟨4850305095323655028440433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25868293841726160151682309 4850305095323655028440433)
              ·
                refine ⟨3637728821492741271330325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4850305095323655028440433 3637728821492741271330325)
                ·
                  refine ⟨170518538507472247093609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3637728821492741271330325 170518538507472247093609)
                  ·
                    rfl

theorem cell23_2988753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 6].length) (baseStart_2988753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988753 prefixEnd_2988753 := by exact prefixLift 2988753
  have htrace : WordTrace (prefixWord ++ tailWord_2988753) baseStart_2988753 baseEnd_2988753 := by
    simpa [prefixWord, tailWord_2988753, baseEnd_2988753] using wordTrace_append hprefix tailTrace_2988753
  have hstable : (prefixWord ++ tailWord_2988753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988753).length < 2 ^ (prefixWord ++ tailWord_2988753).sum := by decide
  have hdescent : baseEnd_2988753 < baseStart_2988753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988783 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 3, 5]
def baseStart_2988783 : Nat := 118140960795 + 2988783 * 2 ^ 59
def prefixEnd_2988783 : Nat := 4983230072969 + 3 ^ 40 * 2988783 * 2
def baseEnd_2988783 : Nat := 511560750328961702155781

theorem tailTrace_2988783 : CollatzResearch.WordTrace tailWord_2988783 prefixEnd_2988783 511560750328961702155781 := by
  unfold tailWord_2988783
  simp only [CollatzResearch.WordTrace]
  refine ⟨109009871531157109343027003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72673247687438072895351335 109009871531157109343027003)
  ·
    refine ⟨163514807296735664014540505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109009871531157109343027003 163514807296735664014540505)
    ·
      refine ⟨122636105472551748010905379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163514807296735664014540505 122636105472551748010905379)
      ·
        refine ⟨183954158208827622016358069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122636105472551748010905379 183954158208827622016358069)
        ·
          refine ⟨17245702332077589564033569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183954158208827622016358069 17245702332077589564033569)
          ·
            refine ⟨12934276749058192173025177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17245702332077589564033569 12934276749058192173025177)
            ·
              refine ⟨9700707561793644129768883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12934276749058192173025177 9700707561793644129768883)
              ·
                refine ⟨14551061342690466194653325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9700707561793644129768883 14551061342690466194653325)
                ·
                  refine ⟨5456648003508924822994997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14551061342690466194653325 5456648003508924822994997)
                  ·
                    refine ⟨511560750328961702155781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5456648003508924822994997 511560750328961702155781)
                    ·
                      rfl

theorem cell23_2988783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_2988783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988783 prefixEnd_2988783 := by exact prefixLift 2988783
  have htrace : WordTrace (prefixWord ++ tailWord_2988783) baseStart_2988783 baseEnd_2988783 := by
    simpa [prefixWord, tailWord_2988783, baseEnd_2988783] using wordTrace_append hprefix tailTrace_2988783
  have hstable : (prefixWord ++ tailWord_2988783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988783).length < 2 ^ (prefixWord ++ tailWord_2988783).sum := by decide
  have hdescent : baseEnd_2988783 < baseStart_2988783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988833 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2988833 : Nat := 118140960795 + 2988833 * 2 ^ 59
def prefixEnd_2988833 : Nat := 4983230072969 + 3 ^ 40 * 2988833 * 2
def baseEnd_2988833 : Nat := 1534707925019609910842113

theorem tailTrace_2988833 : CollatzResearch.WordTrace tailWord_2988833 prefixEnd_2988833 1534707925019609910842113 := by
  unfold tailWord_2988833
  simp only [CollatzResearch.WordTrace]
  refine ⟨109011695180975967882347153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72674463453983978588231435 109011695180975967882347153)
  ·
    refine ⟨81758771385731975911760365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109011695180975967882347153 81758771385731975911760365)
    ·
      refine ⟨30659539269649490966910137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81758771385731975911760365 30659539269649490966910137)
      ·
        refine ⟨22994654452237118225182603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30659539269649490966910137 22994654452237118225182603)
        ·
          refine ⟨34491981678355677337773905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22994654452237118225182603 34491981678355677337773905)
          ·
            refine ⟨25868986258766758003330429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34491981678355677337773905 25868986258766758003330429)
            ·
              refine ⟨9700869847037534251248911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25868986258766758003330429 9700869847037534251248911)
              ·
                refine ⟨14551304770556301376873367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9700869847037534251248911 14551304770556301376873367)
                ·
                  refine ⟨21826957155834452065310051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14551304770556301376873367 21826957155834452065310051)
                  ·
                    refine ⟨32740435733751678097965077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21826957155834452065310051 32740435733751678097965077)
                    ·
                      refine ⟨1534707925019609910842113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32740435733751678097965077 1534707925019609910842113)
                      ·
                        rfl

theorem cell23_2988833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2988833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988833 prefixEnd_2988833 := by exact prefixLift 2988833
  have htrace : WordTrace (prefixWord ++ tailWord_2988833) baseStart_2988833 baseEnd_2988833 := by
    simpa [prefixWord, tailWord_2988833, baseEnd_2988833] using wordTrace_append hprefix tailTrace_2988833
  have hstable : (prefixWord ++ tailWord_2988833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988833).length < 2 ^ (prefixWord ++ tailWord_2988833).sum := by decide
  have hdescent : baseEnd_2988833 < baseStart_2988833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988837 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 3, 2, 2]
def baseStart_2988837 : Nat := 118140960795 + 2988837 * 2 ^ 59
def prefixEnd_2988837 : Nat := 4983230072969 + 3 ^ 40 * 2988837 * 2
def baseEnd_2988837 : Nat := 1534709978942227895192095

theorem tailTrace_2988837 : CollatzResearch.WordTrace tailWord_2988837 prefixEnd_2988837 1534709978942227895192095 := by
  unfold tailWord_2988837
  simp only [CollatzResearch.WordTrace]
  refine ⟨109011841072961476565492765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72674560715307651043661843 109011841072961476565492765)
  ·
    refine ⟨40879440402360553712059787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109011841072961476565492765 40879440402360553712059787)
    ·
      refine ⟨61319160603540830568089681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40879440402360553712059787 61319160603540830568089681)
      ·
        refine ⟨45989370452655622926067261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61319160603540830568089681 45989370452655622926067261)
        ·
          refine ⟨17246013919745858597275223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45989370452655622926067261 17246013919745858597275223)
          ·
            refine ⟨25869020879618787895912835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17246013919745858597275223 25869020879618787895912835)
            ·
              refine ⟨38803531319428181843869253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25869020879618787895912835 38803531319428181843869253)
              ·
                refine ⟨7275662122392784095725485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38803531319428181843869253 7275662122392784095725485)
                ·
                  refine ⟨2728373295897294035897057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7275662122392784095725485 2728373295897294035897057)
                  ·
                    refine ⟨2046279971922970526922793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2728373295897294035897057 2046279971922970526922793)
                    ·
                      refine ⟨1534709978942227895192095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046279971922970526922793 1534709978942227895192095)
                      ·
                        rfl

theorem cell23_2988837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_2988837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988837 prefixEnd_2988837 := by exact prefixLift 2988837
  have htrace : WordTrace (prefixWord ++ tailWord_2988837) baseStart_2988837 baseEnd_2988837 := by
    simpa [prefixWord, tailWord_2988837, baseEnd_2988837] using wordTrace_append hprefix tailTrace_2988837
  have hstable : (prefixWord ++ tailWord_2988837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988837).length < 2 ^ (prefixWord ++ tailWord_2988837).sum := by decide
  have hdescent : baseEnd_2988837 < baseStart_2988837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988877 : List Nat := [1, 6, 1, 2, 2, 1, 2, 8]
def baseStart_2988877 : Nat := 118140960795 + 2988877 * 2 ^ 59
def prefixEnd_2988877 : Nat := 4983230072969 + 3 ^ 40 * 2988877 * 2
def baseEnd_2988877 : Nat := 56841871043274360692293

theorem tailTrace_2988877 : CollatzResearch.WordTrace tailWord_2988877 prefixEnd_2988877 56841871043274360692293 := by
  unfold tailWord_2988877
  simp only [CollatzResearch.WordTrace]
  refine ⟨109013299992816563396948885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72675533328544375597965923 109013299992816563396948885)
  ·
    refine ⟨5109998437163276409231979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109013299992816563396948885 5109998437163276409231979)
    ·
      refine ⟨7664997655744914613847969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5109998437163276409231979 7664997655744914613847969)
      ·
        refine ⟨5748748241808685960385977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7664997655744914613847969 5748748241808685960385977)
        ·
          refine ⟨4311561181356514470289483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5748748241808685960385977 4311561181356514470289483)
          ·
            refine ⟨6467341772034771705434225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4311561181356514470289483 6467341772034771705434225)
            ·
              refine ⟨4850506329026078779075669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6467341772034771705434225 4850506329026078779075669)
              ·
                refine ⟨56841871043274360692293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4850506329026078779075669 56841871043274360692293)
                ·
                  rfl

theorem cell23_2988877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 8].length) (baseStart_2988877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988877 prefixEnd_2988877 := by exact prefixLift 2988877
  have htrace : WordTrace (prefixWord ++ tailWord_2988877) baseStart_2988877 baseEnd_2988877 := by
    simpa [prefixWord, tailWord_2988877, baseEnd_2988877] using wordTrace_append hprefix tailTrace_2988877
  have hstable : (prefixWord ++ tailWord_2988877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988877).length < 2 ^ (prefixWord ++ tailWord_2988877).sum := by decide
  have hdescent : baseEnd_2988877 < baseStart_2988877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988881 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 2, 4]
def baseStart_2988881 : Nat := 118140960795 + 2988881 * 2 ^ 59
def prefixEnd_2988881 : Nat := 4983230072969 + 3 ^ 40 * 2988881 * 2
def baseEnd_2988881 : Nat := 511577524030341907680631

theorem tailTrace_2988881 : CollatzResearch.WordTrace tailWord_2988881 prefixEnd_2988881 511577524030341907680631 := by
  unfold tailWord_2988881
  simp only [CollatzResearch.WordTrace]
  refine ⟨109013445884802072080094497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72675630589868048053396331 109013445884802072080094497)
  ·
    refine ⟨81760084413601554060070873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109013445884802072080094497 81760084413601554060070873)
    ·
      refine ⟨61320063310201165545053155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81760084413601554060070873 61320063310201165545053155)
      ·
        refine ⟨91980094965301748317579733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61320063310201165545053155 91980094965301748317579733)
        ·
          refine ⟨2155783475749259726193275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91980094965301748317579733 2155783475749259726193275)
          ·
            refine ⟨3233675213623889589289913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155783475749259726193275 3233675213623889589289913)
            ·
              refine ⟨2425256410217917191967435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233675213623889589289913 2425256410217917191967435)
              ·
                refine ⟨3637884615326875787951153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425256410217917191967435 3637884615326875787951153)
                ·
                  refine ⟨2728413461495156840963365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3637884615326875787951153 2728413461495156840963365)
                  ·
                    refine ⟨511577524030341907680631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2728413461495156840963365 511577524030341907680631)
                    ·
                      rfl

theorem cell23_2988881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_2988881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988881 prefixEnd_2988881 := by exact prefixLift 2988881
  have htrace : WordTrace (prefixWord ++ tailWord_2988881) baseStart_2988881 baseEnd_2988881 := by
    simpa [prefixWord, tailWord_2988881, baseEnd_2988881] using wordTrace_append hprefix tailTrace_2988881
  have hstable : (prefixWord ++ tailWord_2988881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988881).length < 2 ^ (prefixWord ++ tailWord_2988881).sum := by decide
  have hdescent : baseEnd_2988881 < baseStart_2988881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988897 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_2988897 : Nat := 118140960795 + 2988897 * 2 ^ 59
def prefixEnd_2988897 : Nat := 4983230072969 + 3 ^ 40 * 2988897 * 2
def baseEnd_2988897 : Nat := 1534740787781497660441819

theorem tailTrace_2988897 : CollatzResearch.WordTrace tailWord_2988897 prefixEnd_2988897 1534740787781497660441819 := by
  unfold tailWord_2988897
  simp only [CollatzResearch.WordTrace]
  refine ⟨109014029452744106812676945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72676019635162737875117963 109014029452744106812676945)
  ·
    refine ⟨81760522089558080109507709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109014029452744106812676945 81760522089558080109507709)
    ·
      refine ⟨30660195783584280041065391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81760522089558080109507709 30660195783584280041065391)
      ·
        refine ⟨45990293675376420061598087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30660195783584280041065391 45990293675376420061598087)
        ·
          refine ⟨68985440513064630092397131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45990293675376420061598087 68985440513064630092397131)
          ·
            refine ⟨103478160769596945138595697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68985440513064630092397131 103478160769596945138595697)
            ·
              refine ⟨77608620577197708853946773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103478160769596945138595697 77608620577197708853946773)
              ·
                refine ⟨3637904089556142602528755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77608620577197708853946773 3637904089556142602528755)
                ·
                  refine ⟨5456856134334213903793133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3637904089556142602528755 5456856134334213903793133)
                  ·
                    refine ⟨2046321050375330213922425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5456856134334213903793133 2046321050375330213922425)
                    ·
                      refine ⟨1534740787781497660441819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046321050375330213922425 1534740787781497660441819)
                      ·
                        rfl

theorem cell23_2988897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_2988897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988897 prefixEnd_2988897 := by exact prefixLift 2988897
  have htrace : WordTrace (prefixWord ++ tailWord_2988897) baseStart_2988897 baseEnd_2988897 := by
    simpa [prefixWord, tailWord_2988897, baseEnd_2988897] using wordTrace_append hprefix tailTrace_2988897
  have hstable : (prefixWord ++ tailWord_2988897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988897).length < 2 ^ (prefixWord ++ tailWord_2988897).sum := by decide
  have hdescent : baseEnd_2988897 < baseStart_2988897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988927 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 4, 2, 2]
def baseStart_2988927 : Nat := 118140960795 + 2988927 * 2 ^ 59
def prefixEnd_2988927 : Nat := 4983230072969 + 3 ^ 40 * 2988927 * 2
def baseEnd_2988927 : Nat := 1534756192201132543066681

theorem tailTrace_2988927 : CollatzResearch.WordTrace tailWord_2988927 prefixEnd_2988927 1534756192201132543066681 := by
  unfold tailWord_2988927
  simp only [CollatzResearch.WordTrace]
  refine ⟨109015123642635421936269035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72676749095090281290846023 109015123642635421936269035)
  ·
    refine ⟨163522685463953132904403553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109015123642635421936269035 163522685463953132904403553)
    ·
      refine ⟨122642014097964849678302665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163522685463953132904403553 122642014097964849678302665)
      ·
        refine ⟨91981510573473637258726999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122642014097964849678302665 91981510573473637258726999)
        ·
          refine ⟨137972265860210455888090499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91981510573473637258726999 137972265860210455888090499)
          ·
            refine ⟨206958398790315683832135749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137972265860210455888090499 206958398790315683832135749)
            ·
              refine ⟨38804699773184190718525453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206958398790315683832135749 38804699773184190718525453)
              ·
                refine ⟨14551762414944071519447045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38804699773184190718525453 14551762414944071519447045)
                ·
                  refine ⟨2728455452802013409896321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14551762414944071519447045 2728455452802013409896321)
                  ·
                    refine ⟨2046341589601510057422241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2728455452802013409896321 2046341589601510057422241)
                    ·
                      refine ⟨1534756192201132543066681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046341589601510057422241 1534756192201132543066681)
                      ·
                        rfl

theorem cell23_2988927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_2988927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988927 prefixEnd_2988927 := by exact prefixLift 2988927
  have htrace : WordTrace (prefixWord ++ tailWord_2988927) baseStart_2988927 baseEnd_2988927 := by
    simpa [prefixWord, tailWord_2988927, baseEnd_2988927] using wordTrace_append hprefix tailTrace_2988927
  have hstable : (prefixWord ++ tailWord_2988927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988927).length < 2 ^ (prefixWord ++ tailWord_2988927).sum := by decide
  have hdescent : baseEnd_2988927 < baseStart_2988927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2988990 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2988990 : Nat := 118140960795 + 2988990 * 2 ^ 59
def prefixEnd_2988990 : Nat := 4983230072969 + 3 ^ 40 * 2988990 * 2
def baseEnd_2988990 : Nat := 1534788541482365796578891

theorem tailTrace_2988990 : CollatzResearch.WordTrace tailWord_2988990 prefixEnd_2988990 1534788541482365796578891 := by
  unfold tailWord_2988990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13627177680175897961976553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72678280960938122463874949 13627177680175897961976553)
  ·
    refine ⟨10220383260131923471482415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13627177680175897961976553 10220383260131923471482415)
    ·
      refine ⟨15330574890197885207223623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10220383260131923471482415 15330574890197885207223623)
      ·
        refine ⟨22995862335296827810835435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15330574890197885207223623 22995862335296827810835435)
        ·
          refine ⟨34493793502945241716253153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22995862335296827810835435 34493793502945241716253153)
          ·
            refine ⟨25870345127208931287189865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34493793502945241716253153 25870345127208931287189865)
            ·
              refine ⟨19402758845406698465392399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25870345127208931287189865 19402758845406698465392399)
              ·
                refine ⟨29104138268110047698088599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19402758845406698465392399 29104138268110047698088599)
                ·
                  refine ⟨43656207402165071547132899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29104138268110047698088599 43656207402165071547132899)
                  ·
                    refine ⟨65484311103247607320699349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43656207402165071547132899 65484311103247607320699349)
                    ·
                      refine ⟨1534788541482365796578891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65484311103247607320699349 1534788541482365796578891)
                      ·
                        rfl

theorem cell23_2988990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2988990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2988990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2988990 prefixEnd_2988990 := by exact prefixLift 2988990
  have htrace : WordTrace (prefixWord ++ tailWord_2988990) baseStart_2988990 baseEnd_2988990 := by
    simpa [prefixWord, tailWord_2988990, baseEnd_2988990] using wordTrace_append hprefix tailTrace_2988990
  have hstable : (prefixWord ++ tailWord_2988990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2988990).length < 2 ^ (prefixWord ++ tailWord_2988990).sum := by decide
  have hdescent : baseEnd_2988990 < baseStart_2988990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2988990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989040 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 6]
def baseStart_2989040 : Nat := 118140960795 + 2989040 * 2 ^ 59
def prefixEnd_2989040 : Nat := 4983230072969 + 3 ^ 40 * 2989040 * 2
def baseEnd_2989040 : Nat := 170534912835010066772629

theorem tailTrace_2989040 : CollatzResearch.WordTrace tailWord_2989040 prefixEnd_2989040 170534912835010066772629 := by
  unfold tailWord_2989040
  simp only [CollatzResearch.WordTrace]
  refine ⟨54509622545613021117566287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72679496727484028156755049 54509622545613021117566287)
  ·
    refine ⟨81764433818419531676349431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54509622545613021117566287 81764433818419531676349431)
    ·
      refine ⟨122646650727629297514524147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81764433818419531676349431 122646650727629297514524147)
      ·
        refine ⟨183969976091443946271786221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122646650727629297514524147 183969976091443946271786221)
        ·
          refine ⟨68988741034291479851919833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183969976091443946271786221 68988741034291479851919833)
          ·
            refine ⟨51741555775718609888939875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68988741034291479851919833 51741555775718609888939875)
            ·
              refine ⟨77612333663577914833409813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51741555775718609888939875 77612333663577914833409813)
              ·
                refine ⟨3638078140480214757816085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77612333663577914833409813 3638078140480214757816085)
                ·
                  refine ⟨170534912835010066772629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3638078140480214757816085 170534912835010066772629)
                  ·
                    rfl

theorem cell23_2989040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 6].length) (baseStart_2989040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989040 prefixEnd_2989040 := by exact prefixLift 2989040
  have htrace : WordTrace (prefixWord ++ tailWord_2989040) baseStart_2989040 baseEnd_2989040 := by
    simpa [prefixWord, tailWord_2989040, baseEnd_2989040] using wordTrace_append hprefix tailTrace_2989040
  have hstable : (prefixWord ++ tailWord_2989040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989040).length < 2 ^ (prefixWord ++ tailWord_2989040).sum := by decide
  have hdescent : baseEnd_2989040 < baseStart_2989040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989057 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 6]
def baseStart_2989057 : Nat := 118140960795 + 2989057 * 2 ^ 59
def prefixEnd_2989057 : Nat := 4983230072969 + 3 ^ 40 * 2989057 * 2
def baseEnd_2989057 : Nat := 170535882742913003826787

theorem tailTrace_2989057 : CollatzResearch.WordTrace tailWord_2989057 prefixEnd_2989057 170535882742913003826787 := by
  unfold tailWord_2989057
  simp only [CollatzResearch.WordTrace]
  refine ⟨109019865132164454138501425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72679910088109636092334283 109019865132164454138501425)
  ·
    refine ⟨81764898849123340603876069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109019865132164454138501425 81764898849123340603876069)
    ·
      refine ⟨15330918534210626363226763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81764898849123340603876069 15330918534210626363226763)
      ·
        refine ⟨22996377801315939544840145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15330918534210626363226763 22996377801315939544840145)
        ·
          refine ⟨17247283350986954658630109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22996377801315939544840145 17247283350986954658630109)
          ·
            refine ⟨6467731256620107996986291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17247283350986954658630109 6467731256620107996986291)
            ·
              refine ⟨9701596884930161995479437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6467731256620107996986291 9701596884930161995479437)
              ·
                refine ⟨3638098831848810748304789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9701596884930161995479437 3638098831848810748304789)
                ·
                  refine ⟨170535882742913003826787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3638098831848810748304789 170535882742913003826787)
                  ·
                    rfl

theorem cell23_2989057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 6].length) (baseStart_2989057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989057 prefixEnd_2989057 := by exact prefixLift 2989057
  have htrace : WordTrace (prefixWord ++ tailWord_2989057) baseStart_2989057 baseEnd_2989057 := by
    simpa [prefixWord, tailWord_2989057, baseEnd_2989057] using wordTrace_append hprefix tailTrace_2989057
  have hstable : (prefixWord ++ tailWord_2989057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989057).length < 2 ^ (prefixWord ++ tailWord_2989057).sum := by decide
  have hdescent : baseEnd_2989057 < baseStart_2989057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989095 : List Nat := [1, 1, 7, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2989095 : Nat := 118140960795 + 2989095 * 2 ^ 59
def prefixEnd_2989095 : Nat := 4983230072969 + 3 ^ 40 * 2989095 * 2
def baseEnd_2989095 : Nat := 511614152317029295255303

theorem tailTrace_2989095 : CollatzResearch.WordTrace tailWord_2989095 prefixEnd_2989095 511614152317029295255303 := by
  unfold tailWord_2989095
  simp only [CollatzResearch.WordTrace]
  refine ⟨109021251106026786628384739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72680834070684524418923159 109021251106026786628384739)
  ·
    refine ⟨163531876659040179942577109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109021251106026786628384739 163531876659040179942577109)
    ·
      refine ⟨3832778359196254217404151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 163531876659040179942577109 3832778359196254217404151)
      ·
        refine ⟨5749167538794381326106227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3832778359196254217404151 5749167538794381326106227)
        ·
          refine ⟨8623751308191571989159341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749167538794381326106227 8623751308191571989159341)
          ·
            refine ⟨3233906740571839495934753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8623751308191571989159341 3233906740571839495934753)
            ·
              refine ⟨2425430055428879621951065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3233906740571839495934753 2425430055428879621951065)
              ·
                refine ⟨1819072541571659716463299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2425430055428879621951065 1819072541571659716463299)
                ·
                  refine ⟨2728608812357489574694949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819072541571659716463299 2728608812357489574694949)
                  ·
                    refine ⟨511614152317029295255303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2728608812357489574694949 511614152317029295255303)
                    ·
                      rfl

theorem cell23_2989095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2989095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989095 prefixEnd_2989095 := by exact prefixLift 2989095
  have htrace : WordTrace (prefixWord ++ tailWord_2989095) baseStart_2989095 baseEnd_2989095 := by
    simpa [prefixWord, tailWord_2989095, baseEnd_2989095] using wordTrace_append hprefix tailTrace_2989095
  have hstable : (prefixWord ++ tailWord_2989095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989095).length < 2 ^ (prefixWord ++ tailWord_2989095).sum := by decide
  have hdescent : baseEnd_2989095 < baseStart_2989095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989100 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_2989100 : Nat := 118140960795 + 2989100 * 2 ^ 59
def prefixEnd_2989100 : Nat := 4983230072969 + 3 ^ 40 * 2989100 * 2
def baseEnd_2989100 : Nat := 511615008118120122067795

theorem tailTrace_2989100 : CollatzResearch.WordTrace tailWord_2989100 prefixEnd_2989100 511615008118120122067795 := by
  unfold tailWord_2989100
  simp only [CollatzResearch.WordTrace]
  refine ⟨54510716735504336241158377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72680955647339114988211169 54510716735504336241158377)
  ·
    refine ⟨40883037551628252180868783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54510716735504336241158377 40883037551628252180868783)
    ·
      refine ⟨61324556327442378271303175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40883037551628252180868783 61324556327442378271303175)
      ·
        refine ⟨91986834491163567406954763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61324556327442378271303175 91986834491163567406954763)
        ·
          refine ⟨137980251736745351110432145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91986834491163567406954763 137980251736745351110432145)
          ·
            refine ⟨103485188802559013332824109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137980251736745351110432145 103485188802559013332824109)
            ·
              refine ⟨38806945800959629999809041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103485188802559013332824109 38806945800959629999809041)
              ·
                refine ⟨29105209350719722499856781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38806945800959629999809041 29105209350719722499856781)
                ·
                  refine ⟨10914453506519895937446293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29105209350719722499856781 10914453506519895937446293)
                  ·
                    refine ⟨511615008118120122067795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10914453506519895937446293 511615008118120122067795)
                    ·
                      rfl

theorem cell23_2989100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_2989100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989100 prefixEnd_2989100 := by exact prefixLift 2989100
  have htrace : WordTrace (prefixWord ++ tailWord_2989100) baseStart_2989100 baseEnd_2989100 := by
    simpa [prefixWord, tailWord_2989100, baseEnd_2989100] using wordTrace_append hprefix tailTrace_2989100
  have hstable : (prefixWord ++ tailWord_2989100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989100).length < 2 ^ (prefixWord ++ tailWord_2989100).sum := by decide
  have hdescent : baseEnd_2989100 < baseStart_2989100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989107 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 2, 6, 2]
def baseStart_2989107 : Nat := 118140960795 + 2989107 * 2 ^ 59
def prefixEnd_2989107 : Nat := 4983230072969 + 3 ^ 40 * 2989107 * 2
def baseEnd_2989107 : Nat := 1534848618718941838815853

theorem tailTrace_2989107 : CollatzResearch.WordTrace tailWord_2989107 prefixEnd_2989107 1534848618718941838815853 := by
  unfold tailWord_2989107
  simp only [CollatzResearch.WordTrace]
  refine ⟨109021688781983312677821575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72681125854655541785214383 109021688781983312677821575)
  ·
    refine ⟨163532533172974969016732363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109021688781983312677821575 163532533172974969016732363)
    ·
      refine ⟨245298799759462453525098545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163532533172974969016732363 245298799759462453525098545)
      ·
        refine ⟨183974099819596840143823909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245298799759462453525098545 183974099819596840143823909)
        ·
          refine ⟨34495143716174407526966983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183974099819596840143823909 34495143716174407526966983)
          ·
            refine ⟨51742715574261611290450475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34495143716174407526966983 51742715574261611290450475)
            ·
              refine ⟨77614073361392416935675713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51742715574261611290450475 77614073361392416935675713)
              ·
                refine ⟨58210555021044312701756785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77614073361392416935675713 58210555021044312701756785)
                ·
                  refine ⟨43657916265783234526317589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58210555021044312701756785 43657916265783234526317589)
                  ·
                    refine ⟨2046464824958589118421137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43657916265783234526317589 2046464824958589118421137)
                    ·
                      refine ⟨1534848618718941838815853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046464824958589118421137 1534848618718941838815853)
                      ·
                        rfl

theorem cell23_2989107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 6, 2].length) (baseStart_2989107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989107 prefixEnd_2989107 := by exact prefixLift 2989107
  have htrace : WordTrace (prefixWord ++ tailWord_2989107) baseStart_2989107 baseEnd_2989107 := by
    simpa [prefixWord, tailWord_2989107, baseEnd_2989107] using wordTrace_append hprefix tailTrace_2989107
  have hstable : (prefixWord ++ tailWord_2989107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989107).length < 2 ^ (prefixWord ++ tailWord_2989107).sum := by decide
  have hdescent : baseEnd_2989107 < baseStart_2989107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989117 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_2989117 : Nat := 118140960795 + 2989117 * 2 ^ 59
def prefixEnd_2989117 : Nat := 4983230072969 + 3 ^ 40 * 2989117 * 2
def baseEnd_2989117 : Nat := 511617917841828933230269

theorem tailTrace_2989117 : CollatzResearch.WordTrace tailWord_2989117 prefixEnd_2989117 511617917841828933230269 := by
  unfold tailWord_2989117
  simp only [CollatzResearch.WordTrace]
  refine ⟨109022053511947084385685605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72681369007964722923790403 109022053511947084385685605)
  ·
    refine ⟨20441635033490078322316051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109022053511947084385685605 20441635033490078322316051)
    ·
      refine ⟨30662452550235117483474077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20441635033490078322316051 30662452550235117483474077)
      ·
        refine ⟨11498419706338169056302779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30662452550235117483474077 11498419706338169056302779)
        ·
          refine ⟨17247629559507253584454169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11498419706338169056302779 17247629559507253584454169)
          ·
            refine ⟨12935722169630440188340627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17247629559507253584454169 12935722169630440188340627)
            ·
              refine ⟨19403583254445660282510941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12935722169630440188340627 19403583254445660282510941)
              ·
                refine ⟨7276343720417122605941603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19403583254445660282510941 7276343720417122605941603)
                ·
                  refine ⟨10914515580625683908912405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7276343720417122605941603 10914515580625683908912405)
                  ·
                    refine ⟨511617917841828933230269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10914515580625683908912405 511617917841828933230269)
                    ·
                      rfl

theorem cell23_2989117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_2989117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989117 prefixEnd_2989117 := by exact prefixLift 2989117
  have htrace : WordTrace (prefixWord ++ tailWord_2989117) baseStart_2989117 baseEnd_2989117 := by
    simpa [prefixWord, tailWord_2989117, baseEnd_2989117] using wordTrace_append hprefix tailTrace_2989117
  have hstable : (prefixWord ++ tailWord_2989117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989117).length < 2 ^ (prefixWord ++ tailWord_2989117).sum := by decide
  have hdescent : baseEnd_2989117 < baseStart_2989117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989130 : List Nat := [3, 1, 2, 1, 1, 2, 2, 11]
def baseStart_2989130 : Nat := 118140960795 + 2989130 * 2 ^ 59
def prefixEnd_2989130 : Nat := 4983230072969 + 3 ^ 40 * 2989130 * 2
def baseEnd_2989130 : Nat := 56846682547185009215861

theorem tailTrace_2989130 : CollatzResearch.WordTrace tailWord_2989130 prefixEnd_2989130 56846682547185009215861 := by
  unfold tailWord_2989130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27255631915224996901477211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72681685107266658403939229 27255631915224996901477211)
  ·
    refine ⟨40883447872837495352215817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27255631915224996901477211 40883447872837495352215817)
    ·
      refine ⟨30662585904628121514161863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40883447872837495352215817 30662585904628121514161863)
      ·
        refine ⟨45993878856942182271242795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30662585904628121514161863 45993878856942182271242795)
        ·
          refine ⟨68990818285413273406864193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45993878856942182271242795 68990818285413273406864193)
          ·
            refine ⟨51743113714059955055148145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68990818285413273406864193 51743113714059955055148145)
            ·
              refine ⟨38807335285544966291361109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51743113714059955055148145 38807335285544966291361109)
              ·
                refine ⟨56846682547185009215861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 38807335285544966291361109 56846682547185009215861)
                ·
                  rfl

theorem cell23_2989130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 11].length) (baseStart_2989130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989130 prefixEnd_2989130 := by exact prefixLift 2989130
  have htrace : WordTrace (prefixWord ++ tailWord_2989130) baseStart_2989130 baseEnd_2989130 := by
    simpa [prefixWord, tailWord_2989130, baseEnd_2989130] using wordTrace_append hprefix tailTrace_2989130
  have hstable : (prefixWord ++ tailWord_2989130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989130).length < 2 ^ (prefixWord ++ tailWord_2989130).sum := by decide
  have hdescent : baseEnd_2989130 < baseStart_2989130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989137 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_2989137 : Nat := 118140960795 + 2989137 * 2 ^ 59
def prefixEnd_2989137 : Nat := 4983230072969 + 3 ^ 40 * 2989137 * 2
def baseEnd_2989137 : Nat := 1534864023138576721440715

theorem tailTrace_2989137 : CollatzResearch.WordTrace tailWord_2989137 prefixEnd_2989137 1534864023138576721440715 := by
  unfold tailWord_2989137
  simp only [CollatzResearch.WordTrace]
  refine ⟨109022782971874627801413665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72681855314583085200942443 109022782971874627801413665)
  ·
    refine ⟨81767087228905970851060249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109022782971874627801413665 81767087228905970851060249)
    ·
      refine ⟨61325315421679478138295187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81767087228905970851060249 61325315421679478138295187)
      ·
        refine ⟨91987973132519217207442781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61325315421679478138295187 91987973132519217207442781)
        ·
          refine ⟨34495489924694706452791043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91987973132519217207442781 34495489924694706452791043)
          ·
            refine ⟨51743234887042059679186565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34495489924694706452791043 51743234887042059679186565)
            ·
              refine ⟨9701856541320386189847481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51743234887042059679186565 9701856541320386189847481)
              ·
                refine ⟨7276392405990289642385611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9701856541320386189847481 7276392405990289642385611)
                ·
                  refine ⟨10914588608985434463578417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7276392405990289642385611 10914588608985434463578417)
                  ·
                    refine ⟨8185941456739075847683813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10914588608985434463578417 8185941456739075847683813)
                    ·
                      refine ⟨1534864023138576721440715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8185941456739075847683813 1534864023138576721440715)
                      ·
                        rfl

theorem cell23_2989137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_2989137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989137 prefixEnd_2989137 := by exact prefixLift 2989137
  have htrace : WordTrace (prefixWord ++ tailWord_2989137) baseStart_2989137 baseEnd_2989137 := by
    simpa [prefixWord, tailWord_2989137, baseEnd_2989137] using wordTrace_append hprefix tailTrace_2989137
  have hstable : (prefixWord ++ tailWord_2989137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989137).length < 2 ^ (prefixWord ++ tailWord_2989137).sum := by decide
  have hdescent : baseEnd_2989137 < baseStart_2989137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989144 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_2989144 : Nat := 118140960795 + 2989144 * 2 ^ 59
def prefixEnd_2989144 : Nat := 4983230072969 + 3 ^ 40 * 2989144 * 2
def baseEnd_2989144 : Nat := 1534867617503158194053183

theorem tailTrace_2989144 : CollatzResearch.WordTrace tailWord_2989144 prefixEnd_2989144 1534867617503158194053183 := by
  unfold tailWord_2989144
  simp only [CollatzResearch.WordTrace]
  refine ⟨54511519141424633998459243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72682025521899511997945657 54511519141424633998459243)
  ·
    refine ⟨81767278712136950997688865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54511519141424633998459243 81767278712136950997688865)
    ·
      refine ⟨61325459034102713248266649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81767278712136950997688865 61325459034102713248266649)
      ·
        refine ⟨45994094275577034936199987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61325459034102713248266649 45994094275577034936199987)
        ·
          refine ⟨68991141413365552404299981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45994094275577034936199987 68991141413365552404299981)
          ·
            refine ⟨25871678030012082151612493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68991141413365552404299981 25871678030012082151612493)
            ·
              refine ⟨9701879261254530806854685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25871678030012082151612493 9701879261254530806854685)
              ·
                refine ⟨3638204722970449052570507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9701879261254530806854685 3638204722970449052570507)
                ·
                  refine ⟨5457307084455673578855761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638204722970449052570507 5457307084455673578855761)
                  ·
                    refine ⟨4092980313341755184141821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5457307084455673578855761 4092980313341755184141821)
                    ·
                      refine ⟨1534867617503158194053183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4092980313341755184141821 1534867617503158194053183)
                      ·
                        rfl

theorem cell23_2989144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_2989144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989144 prefixEnd_2989144 := by exact prefixLift 2989144
  have htrace : WordTrace (prefixWord ++ tailWord_2989144) baseStart_2989144 baseEnd_2989144 := by
    simpa [prefixWord, tailWord_2989144, baseEnd_2989144] using wordTrace_append hprefix tailTrace_2989144
  have hstable : (prefixWord ++ tailWord_2989144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989144).length < 2 ^ (prefixWord ++ tailWord_2989144).sum := by decide
  have hdescent : baseEnd_2989144 < baseStart_2989144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989184 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 3, 3, 2]
def baseStart_2989184 : Nat := 118140960795 + 2989184 * 2 ^ 59
def prefixEnd_2989184 : Nat := 4983230072969 + 3 ^ 40 * 2989184 * 2
def baseEnd_2989184 : Nat := 1534888156729338037552999

theorem tailTrace_2989184 : CollatzResearch.WordTrace tailWord_2989184 prefixEnd_2989184 1534888156729338037552999 := by
  unfold tailWord_2989184
  simp only [CollatzResearch.WordTrace]
  refine ⟨54512248601352177414187303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72682998135136236552249737 54512248601352177414187303)
  ·
    refine ⟨81768372902028266121280955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54512248601352177414187303 81768372902028266121280955)
    ·
      refine ⟨122652559353042399181921433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81768372902028266121280955 122652559353042399181921433)
      ·
        refine ⟨91989419514781799386441075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122652559353042399181921433 91989419514781799386441075)
        ·
          refine ⟨137984129272172699079661613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91989419514781799386441075 137984129272172699079661613)
          ·
            refine ⟨51744048477064762154873105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137984129272172699079661613 51744048477064762154873105)
            ·
              refine ⟨38808036357798571616154829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51744048477064762154873105 38808036357798571616154829)
              ·
                refine ⟨14553013634174464356058061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38808036357798571616154829 14553013634174464356058061)
                ·
                  refine ⟨5457380112815424133521773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14553013634174464356058061 5457380112815424133521773)
                  ·
                    refine ⟨2046517542305784050070665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5457380112815424133521773 2046517542305784050070665)
                    ·
                      refine ⟨1534888156729338037552999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046517542305784050070665 1534888156729338037552999)
                      ·
                        rfl

theorem cell23_2989184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_2989184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989184 prefixEnd_2989184 := by exact prefixLift 2989184
  have htrace : WordTrace (prefixWord ++ tailWord_2989184) baseStart_2989184 baseEnd_2989184 := by
    simpa [prefixWord, tailWord_2989184, baseEnd_2989184] using wordTrace_append hprefix tailTrace_2989184
  have hstable : (prefixWord ++ tailWord_2989184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989184).length < 2 ^ (prefixWord ++ tailWord_2989184).sum := by decide
  have hdescent : baseEnd_2989184 < baseStart_2989184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989192 : List Nat := [2, 1, 3, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2989192 : Nat := 118140960795 + 2989192 * 2 ^ 59
def prefixEnd_2989192 : Nat := 4983230072969 + 3 ^ 40 * 2989192 * 2
def baseEnd_2989192 : Nat := 1534892264574574006252963

theorem tailTrace_2989192 : CollatzResearch.WordTrace tailWord_2989192 prefixEnd_2989192 1534892264574574006252963 := by
  unfold tailWord_2989192
  simp only [CollatzResearch.WordTrace]
  refine ⟨54512394493337686097332915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72683192657783581463110553 54512394493337686097332915)
  ·
    refine ⟨81768591740006529145999373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54512394493337686097332915 81768591740006529145999373)
    ·
      refine ⟨30663221902502448429749765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81768591740006529145999373 30663221902502448429749765)
      ·
        refine ⟨5749354106719209080578081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30663221902502448429749765 5749354106719209080578081)
        ·
          refine ⟨4312015580039406810433561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5749354106719209080578081 4312015580039406810433561)
          ·
            refine ⟨3234011685029555107825171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4312015580039406810433561 3234011685029555107825171)
            ·
              refine ⟨4851017527544332661737757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234011685029555107825171 4851017527544332661737757)
              ·
                refine ⟨1819131572829124748151659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4851017527544332661737757 1819131572829124748151659)
                ·
                  refine ⟨2728697359243687122227489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819131572829124748151659 2728697359243687122227489)
                  ·
                    refine ⟨2046523019432765341670617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2728697359243687122227489 2046523019432765341670617)
                    ·
                      refine ⟨1534892264574574006252963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046523019432765341670617 1534892264574574006252963)
                      ·
                        rfl

theorem cell23_2989192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2989192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989192 prefixEnd_2989192 := by exact prefixLift 2989192
  have htrace : WordTrace (prefixWord ++ tailWord_2989192) baseStart_2989192 baseEnd_2989192 := by
    simpa [prefixWord, tailWord_2989192, baseEnd_2989192] using wordTrace_append hprefix tailTrace_2989192
  have hstable : (prefixWord ++ tailWord_2989192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989192).length < 2 ^ (prefixWord ++ tailWord_2989192).sum := by decide
  have hdescent : baseEnd_2989192 < baseStart_2989192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989217 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2989217 : Nat := 118140960795 + 2989217 * 2 ^ 59
def prefixEnd_2989217 : Nat := 4983230072969 + 3 ^ 40 * 2989217 * 2
def baseEnd_2989217 : Nat := 1534905101590936408440347

theorem tailTrace_2989217 : CollatzResearch.WordTrace tailWord_2989217 prefixEnd_2989217 1534905101590936408440347 := by
  unfold tailWord_2989217
  simp only [CollatzResearch.WordTrace]
  refine ⟨109025700811584801464325905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72683800541056534309550603 109025700811584801464325905)
  ·
    refine ⟨81769275608688601098244429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109025700811584801464325905 81769275608688601098244429)
    ·
      refine ⟨30663478353258225411841661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81769275608688601098244429 30663478353258225411841661)
      ·
        refine ⟨11498804382471834529440623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30663478353258225411841661 11498804382471834529440623)
        ·
          refine ⟨17248206573707751794160935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11498804382471834529440623 17248206573707751794160935)
          ·
            refine ⟨25872309860561627691241403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17248206573707751794160935 25872309860561627691241403)
            ·
              refine ⟨38808464790842441536862105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25872309860561627691241403 38808464790842441536862105)
              ·
                refine ⟨29106348593131831152646579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38808464790842441536862105 29106348593131831152646579)
                ·
                  refine ⟨43659522889697746728969869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29106348593131831152646579 43659522889697746728969869)
                  ·
                    refine ⟨16372321083636655023363701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43659522889697746728969869 16372321083636655023363701)
                    ·
                      refine ⟨1534905101590936408440347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16372321083636655023363701 1534905101590936408440347)
                      ·
                        rfl

theorem cell23_2989217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2989217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989217 prefixEnd_2989217 := by exact prefixLift 2989217
  have htrace : WordTrace (prefixWord ++ tailWord_2989217) baseStart_2989217 baseEnd_2989217 := by
    simpa [prefixWord, tailWord_2989217, baseEnd_2989217] using wordTrace_append hprefix tailTrace_2989217
  have hstable : (prefixWord ++ tailWord_2989217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989217).length < 2 ^ (prefixWord ++ tailWord_2989217).sum := by decide
  have hdescent : baseEnd_2989217 < baseStart_2989217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989271 : List Nat := [1, 1, 3, 2, 1, 2, 6, 2, 5]
def baseStart_2989271 : Nat := 118140960795 + 2989271 * 2 ^ 59
def prefixEnd_2989271 : Nat := 4983230072969 + 3 ^ 40 * 2989271 * 2
def baseEnd_2989271 : Nat := 170548092171808799685011

theorem tailTrace_2989271 : CollatzResearch.WordTrace tailWord_2989271 prefixEnd_2989271 170548092171808799685011 := by
  unfold tailWord_2989271
  simp only [CollatzResearch.WordTrace]
  refine ⟨109027670353389168686791667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72685113568926112457861111 109027670353389168686791667)
  ·
    refine ⟨163541505530083753030187501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109027670353389168686791667 163541505530083753030187501)
    ·
      refine ⟨61328064573781407386320313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163541505530083753030187501 61328064573781407386320313)
      ·
        refine ⟨45996048430336055539740235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61328064573781407386320313 45996048430336055539740235)
        ·
          refine ⟨68994072645504083309610353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45996048430336055539740235 68994072645504083309610353)
          ·
            refine ⟨51745554484128062482207765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68994072645504083309610353 51745554484128062482207765)
            ·
              refine ⟨2425572866443502928853489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51745554484128062482207765 2425572866443502928853489)
              ·
                refine ⟨1819179649832627196640117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2425572866443502928853489 1819179649832627196640117)
                ·
                  refine ⟨170548092171808799685011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1819179649832627196640117 170548092171808799685011)
                  ·
                    rfl

theorem cell23_2989271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 5].length) (baseStart_2989271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989271 prefixEnd_2989271 := by exact prefixLift 2989271
  have htrace : WordTrace (prefixWord ++ tailWord_2989271) baseStart_2989271 baseEnd_2989271 := by
    simpa [prefixWord, tailWord_2989271, baseEnd_2989271] using wordTrace_append hprefix tailTrace_2989271
  have hstable : (prefixWord ++ tailWord_2989271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989271).length < 2 ^ (prefixWord ++ tailWord_2989271).sum := by decide
  have hdescent : baseEnd_2989271 < baseStart_2989271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989317 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_2989317 : Nat := 118140960795 + 2989317 * 2 ^ 59
def prefixEnd_2989317 : Nat := 4983230072969 + 3 ^ 40 * 2989317 * 2
def baseEnd_2989317 : Nat := 1534956449656386017189887

theorem tailTrace_2989317 : CollatzResearch.WordTrace tailWord_2989317 prefixEnd_2989317 1534956449656386017189887 := by
  unfold tailWord_2989317
  simp only [CollatzResearch.WordTrace]
  refine ⟨109029348111222518542966205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72686232074148345695310803 109029348111222518542966205)
  ·
    refine ⟨40886005541708444453612327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109029348111222518542966205 40886005541708444453612327)
    ·
      refine ⟨61329008312562666680418491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40886005541708444453612327 61329008312562666680418491)
      ·
        refine ⟨91993512468844000020627737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61329008312562666680418491 91993512468844000020627737)
        ·
          refine ⟨68995134351633000015470803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91993512468844000020627737 68995134351633000015470803)
          ·
            refine ⟨103492701527449500023206205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68995134351633000015470803 103492701527449500023206205)
            ·
              refine ⟨38809763072793562508702327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103492701527449500023206205 38809763072793562508702327)
              ·
                refine ⟨58214644609190343763053491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38809763072793562508702327 58214644609190343763053491)
                ·
                  refine ⟨87321966913785515644580237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58214644609190343763053491 87321966913785515644580237)
                  ·
                    refine ⟨32745737592669568366717589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87321966913785515644580237 32745737592669568366717589)
                    ·
                      refine ⟨1534956449656386017189887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32745737592669568366717589 1534956449656386017189887)
                      ·
                        rfl

theorem cell23_2989317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_2989317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989317 prefixEnd_2989317 := by exact prefixLift 2989317
  have htrace : WordTrace (prefixWord ++ tailWord_2989317) baseStart_2989317 baseEnd_2989317 := by
    simpa [prefixWord, tailWord_2989317, baseEnd_2989317] using wordTrace_append hprefix tailTrace_2989317
  have hstable : (prefixWord ++ tailWord_2989317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989317).length < 2 ^ (prefixWord ++ tailWord_2989317).sum := by decide
  have hdescent : baseEnd_2989317 < baseStart_2989317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989341 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2989341 : Nat := 118140960795 + 2989341 * 2 ^ 59
def prefixEnd_2989341 : Nat := 4983230072969 + 3 ^ 40 * 2989341 * 2
def baseEnd_2989341 : Nat := 1534968773192093923289777

theorem tailTrace_2989341 : CollatzResearch.WordTrace tailWord_2989341 prefixEnd_2989341 1534968773192093923289777 := by
  unfold tailWord_2989341
  simp only [CollatzResearch.WordTrace]
  refine ⟨109030223463135570641839877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72686815642090380427893251 109030223463135570641839877)
  ·
    refine ⟨20443166899337919495344977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109030223463135570641839877 20443166899337919495344977)
    ·
      refine ⟨15332375174503439621508733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20443166899337919495344977 15332375174503439621508733)
      ·
        refine ⟨5749640690438789858065775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15332375174503439621508733 5749640690438789858065775)
        ·
          refine ⟨8624461035658184787098663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749640690438789858065775 8624461035658184787098663)
          ·
            refine ⟨12936691553487277180647995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8624461035658184787098663 12936691553487277180647995)
            ·
              refine ⟨19405037330230915770971993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12936691553487277180647995 19405037330230915770971993)
              ·
                refine ⟨14553777997673186828228995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19405037330230915770971993 14553777997673186828228995)
                ·
                  refine ⟨21830666996509780242343493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14553777997673186828228995 21830666996509780242343493)
                  ·
                    refine ⟨4093250061845583795439405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21830666996509780242343493 4093250061845583795439405)
                    ·
                      refine ⟨1534968773192093923289777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4093250061845583795439405 1534968773192093923289777)
                      ·
                        rfl

theorem cell23_2989341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2989341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989341 prefixEnd_2989341 := by exact prefixLift 2989341
  have htrace : WordTrace (prefixWord ++ tailWord_2989341) baseStart_2989341 baseEnd_2989341 := by
    simpa [prefixWord, tailWord_2989341, baseEnd_2989341] using wordTrace_append hprefix tailTrace_2989341
  have hstable : (prefixWord ++ tailWord_2989341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989341).length < 2 ^ (prefixWord ++ tailWord_2989341).sum := by decide
  have hdescent : baseEnd_2989341 < baseStart_2989341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989365 : List Nat := [1, 3, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2989365 : Nat := 118140960795 + 2989365 * 2 ^ 59
def prefixEnd_2989365 : Nat := 4983230072969 + 3 ^ 40 * 2989365 * 2
def baseEnd_2989365 : Nat := 511660365575933943129889

theorem tailTrace_2989365 : CollatzResearch.WordTrace tailWord_2989365 prefixEnd_2989365 511660365575933943129889 := by
  unfold tailWord_2989365
  simp only [CollatzResearch.WordTrace]
  refine ⟨109031098815048622740713549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72687399210032415160475699 109031098815048622740713549)
  ·
    refine ⟨40886662055643233527767581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109031098815048622740713549 40886662055643233527767581)
    ·
      refine ⟨15332498270866212572912843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40886662055643233527767581 15332498270866212572912843)
      ·
        refine ⟨22998747406299318859369265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15332498270866212572912843 22998747406299318859369265)
        ·
          refine ⟨17249060554724489144526949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22998747406299318859369265 17249060554724489144526949)
          ·
            refine ⟨3234198854010841714598803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17249060554724489144526949 3234198854010841714598803)
            ·
              refine ⟨4851298281016262571898205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234198854010841714598803 4851298281016262571898205)
              ·
                refine ⟨1819236855381098464461827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4851298281016262571898205 1819236855381098464461827)
                ·
                  refine ⟨2728855283071647696692741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819236855381098464461827 2728855283071647696692741)
                  ·
                    refine ⟨511660365575933943129889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2728855283071647696692741 511660365575933943129889)
                    ·
                      rfl

theorem cell23_2989365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2989365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989365 prefixEnd_2989365 := by exact prefixLift 2989365
  have htrace : WordTrace (prefixWord ++ tailWord_2989365) baseStart_2989365 baseEnd_2989365 := by
    simpa [prefixWord, tailWord_2989365, baseEnd_2989365] using wordTrace_append hprefix tailTrace_2989365
  have hstable : (prefixWord ++ tailWord_2989365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989365).length < 2 ^ (prefixWord ++ tailWord_2989365).sum := by decide
  have hdescent : baseEnd_2989365 < baseStart_2989365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989388 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2989388 : Nat := 118140960795 + 2989388 * 2 ^ 59
def prefixEnd_2989388 : Nat := 4983230072969 + 3 ^ 40 * 2989388 * 2
def baseEnd_2989388 : Nat := 1534992906782855239402061

theorem tailTrace_2989388 : CollatzResearch.WordTrace tailWord_2989388 prefixEnd_2989388 1534992906782855239402061 := by
  unfold tailWord_2989388
  simp only [CollatzResearch.WordTrace]
  refine ⟨54515968846982648834400409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72687958462643531779200545 54515968846982648834400409)
  ·
    refine ⟨40886976635236986625800307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54515968846982648834400409 40886976635236986625800307)
    ·
      refine ⟨61330464952855479938700461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40886976635236986625800307 61330464952855479938700461)
      ·
        refine ⟨22998924357320804977012673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61330464952855479938700461 22998924357320804977012673)
        ·
          refine ⟨17249193267990603732759505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22998924357320804977012673 17249193267990603732759505)
          ·
            refine ⟨12936894950992952799569629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17249193267990603732759505 12936894950992952799569629)
            ·
              refine ⟨4851335606622357299838611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12936894950992952799569629 4851335606622357299838611)
              ·
                refine ⟨7277003409933535949757917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851335606622357299838611 7277003409933535949757917)
                ·
                  refine ⟨2728876278725075981159219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7277003409933535949757917 2728876278725075981159219)
                  ·
                    refine ⟨4093314418087613971738829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2728876278725075981159219 4093314418087613971738829)
                    ·
                      refine ⟨1534992906782855239402061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4093314418087613971738829 1534992906782855239402061)
                      ·
                        rfl

theorem cell23_2989388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2989388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989388 prefixEnd_2989388 := by exact prefixLift 2989388
  have htrace : WordTrace (prefixWord ++ tailWord_2989388) baseStart_2989388 baseEnd_2989388 := by
    simpa [prefixWord, tailWord_2989388, baseEnd_2989388] using wordTrace_append hprefix tailTrace_2989388
  have hstable : (prefixWord ++ tailWord_2989388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989388).length < 2 ^ (prefixWord ++ tailWord_2989388).sum := by decide
  have hdescent : baseEnd_2989388 < baseStart_2989388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989394 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2989394 : Nat := 118140960795 + 2989394 * 2 ^ 59
def prefixEnd_2989394 : Nat := 4983230072969 + 3 ^ 40 * 2989394 * 2
def baseEnd_2989394 : Nat := 1534995987666782215927033

theorem tailTrace_2989394 : CollatzResearch.WordTrace tailWord_2989394 prefixEnd_2989394 1534995987666782215927033 := by
  unfold tailWord_2989394
  simp only [CollatzResearch.WordTrace]
  refine ⟨27258039132985890173379809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72688104354629040462346157 27258039132985890173379809)
  ·
    refine ⟨20443529349739417630034857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27258039132985890173379809 20443529349739417630034857)
    ·
      refine ⟨15332647012304563222526143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20443529349739417630034857 15332647012304563222526143)
      ·
        refine ⟨22998970518456844833789215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15332647012304563222526143 22998970518456844833789215)
        ·
          refine ⟨34498455777685267250683823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22998970518456844833789215 34498455777685267250683823)
          ·
            refine ⟨51747683666527900876025735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34498455777685267250683823 51747683666527900876025735)
            ·
              refine ⟨77621525499791851314038603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51747683666527900876025735 77621525499791851314038603)
              ·
                refine ⟨116432288249687776971057905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77621525499791851314038603 116432288249687776971057905)
                ·
                  refine ⟨87324216187265832728293429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116432288249687776971057905 87324216187265832728293429)
                  ·
                    refine ⟨8186645267556171818277509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87324216187265832728293429 8186645267556171818277509)
                    ·
                      refine ⟨1534995987666782215927033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8186645267556171818277509 1534995987666782215927033)
                      ·
                        rfl

theorem cell23_2989394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2989394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989394 prefixEnd_2989394 := by exact prefixLift 2989394
  have htrace : WordTrace (prefixWord ++ tailWord_2989394) baseStart_2989394 baseEnd_2989394 := by
    simpa [prefixWord, tailWord_2989394, baseEnd_2989394] using wordTrace_append hprefix tailTrace_2989394
  have hstable : (prefixWord ++ tailWord_2989394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989394).length < 2 ^ (prefixWord ++ tailWord_2989394).sum := by decide
  have hdescent : baseEnd_2989394 < baseStart_2989394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989408 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 1, 5]
def baseStart_2989408 : Nat := 118140960795 + 2989408 * 2 ^ 59
def prefixEnd_2989408 : Nat := 4983230072969 + 3 ^ 40 * 2989408 * 2
def baseEnd_2989408 : Nat := 511667725465315053717323

theorem tailTrace_2989408 : CollatzResearch.WordTrace tailWord_2989408 prefixEnd_2989408 511667725465315053717323 := by
  unfold tailWord_2989408
  simp only [CollatzResearch.WordTrace]
  refine ⟨54516333576946420542264439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72688444769261894056352585 54516333576946420542264439)
  ·
    refine ⟨81774500365419630813396659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54516333576946420542264439 81774500365419630813396659)
    ·
      refine ⟨122661750548129446220094989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81774500365419630813396659 122661750548129446220094989)
      ·
        refine ⟨45998156455548542332535621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122661750548129446220094989 45998156455548542332535621)
        ·
          refine ⟨8624654335415351687350429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45998156455548542332535621 8624654335415351687350429)
          ·
            refine ⟨3234245375780756882756411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8624654335415351687350429 3234245375780756882756411)
            ·
              refine ⟨4851368063671135324134617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234245375780756882756411 4851368063671135324134617)
              ·
                refine ⟨3638526047753351493100963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4851368063671135324134617 3638526047753351493100963)
                ·
                  refine ⟨5457789071630027239651445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638526047753351493100963 5457789071630027239651445)
                  ·
                    refine ⟨511667725465315053717323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5457789071630027239651445 511667725465315053717323)
                    ·
                      rfl

theorem cell23_2989408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_2989408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989408 prefixEnd_2989408 := by exact prefixLift 2989408
  have htrace : WordTrace (prefixWord ++ tailWord_2989408) baseStart_2989408 baseEnd_2989408 := by
    simpa [prefixWord, tailWord_2989408, baseEnd_2989408] using wordTrace_append hprefix tailTrace_2989408
  have hstable : (prefixWord ++ tailWord_2989408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989408).length < 2 ^ (prefixWord ++ tailWord_2989408).sum := by decide
  have hdescent : baseEnd_2989408 < baseStart_2989408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989411 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2989411 : Nat := 118140960795 + 2989411 * 2 ^ 59
def prefixEnd_2989411 : Nat := 4983230072969 + 3 ^ 40 * 2989411 * 2
def baseEnd_2989411 : Nat := 1535004716837908649414455

theorem tailTrace_2989411 : CollatzResearch.WordTrace tailWord_2989411 prefixEnd_2989411 1535004716837908649414455 := by
  unfold tailWord_2989411
  simp only [CollatzResearch.WordTrace]
  refine ⟨109032776572881972596888087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72688517715254648397925391 109032776572881972596888087)
  ·
    refine ⟨163549164859322958895332131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109032776572881972596888087 163549164859322958895332131)
    ·
      refine ⟨245323747288984438342998197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163549164859322958895332131 245323747288984438342998197)
      ·
        refine ⟨22999101308342291094656081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 245323747288984438342998197 22999101308342291094656081)
        ·
          refine ⟨17249325981256718320992061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22999101308342291094656081 17249325981256718320992061)
          ·
            refine ⟨6468497242971269370372023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17249325981256718320992061 6468497242971269370372023)
            ·
              refine ⟨9702745864456904055558035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468497242971269370372023 9702745864456904055558035)
              ·
                refine ⟨14554118796685356083337053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9702745864456904055558035 14554118796685356083337053)
                ·
                  refine ⟨5457794548757008531251395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14554118796685356083337053 5457794548757008531251395)
                  ·
                    refine ⟨8186691823135512796877093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5457794548757008531251395 8186691823135512796877093)
                    ·
                      refine ⟨1535004716837908649414455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8186691823135512796877093 1535004716837908649414455)
                      ·
                        rfl

theorem cell23_2989411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2989411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989411 prefixEnd_2989411 := by exact prefixLift 2989411
  have htrace : WordTrace (prefixWord ++ tailWord_2989411) baseStart_2989411 baseEnd_2989411 := by
    simpa [prefixWord, tailWord_2989411, baseEnd_2989411] using wordTrace_append hprefix tailTrace_2989411
  have hstable : (prefixWord ++ tailWord_2989411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989411).length < 2 ^ (prefixWord ++ tailWord_2989411).sum := by decide
  have hdescent : baseEnd_2989411 < baseStart_2989411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989415 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_2989415 : Nat := 118140960795 + 2989415 * 2 ^ 59
def prefixEnd_2989415 : Nat := 4983230072969 + 3 ^ 40 * 2989415 * 2
def baseEnd_2989415 : Nat := 1535006770760526633764437

theorem tailTrace_2989415 : CollatzResearch.WordTrace tailWord_2989415 prefixEnd_2989415 1535006770760526633764437 := by
  unfold tailWord_2989415
  simp only [CollatzResearch.WordTrace]
  refine ⟨109032922464867481280033699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72688614976578320853355799 109032922464867481280033699)
  ·
    refine ⟨163549383697301221920050549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109032922464867481280033699 163549383697301221920050549)
    ·
      refine ⟨15332754721621989555004739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163549383697301221920050549 15332754721621989555004739)
      ·
        refine ⟨22999132082432984332507109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15332754721621989555004739 22999132082432984332507109)
        ·
          refine ⟨4312337265456184562345083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22999132082432984332507109 4312337265456184562345083)
          ·
            refine ⟨6468505898184276843517625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312337265456184562345083 6468505898184276843517625)
            ·
              refine ⟨4851379423638207632638219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6468505898184276843517625 4851379423638207632638219)
              ·
                refine ⟨7277069135457311448957329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851379423638207632638219 7277069135457311448957329)
                ·
                  refine ⟨5457801851592983586717997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7277069135457311448957329 5457801851592983586717997)
                  ·
                    refine ⟨2046675694347368845019249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5457801851592983586717997 2046675694347368845019249)
                    ·
                      refine ⟨1535006770760526633764437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046675694347368845019249 1535006770760526633764437)
                      ·
                        rfl

theorem cell23_2989415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_2989415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989415 prefixEnd_2989415 := by exact prefixLift 2989415
  have htrace : WordTrace (prefixWord ++ tailWord_2989415) baseStart_2989415 baseEnd_2989415 := by
    simpa [prefixWord, tailWord_2989415, baseEnd_2989415] using wordTrace_append hprefix tailTrace_2989415
  have hstable : (prefixWord ++ tailWord_2989415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989415).length < 2 ^ (prefixWord ++ tailWord_2989415).sum := by decide
  have hdescent : baseEnd_2989415 < baseStart_2989415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989421 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2989421 : Nat := 118140960795 + 2989421 * 2 ^ 59
def prefixEnd_2989421 : Nat := 4983230072969 + 3 ^ 40 * 2989421 * 2
def baseEnd_2989421 : Nat := 511669950548151203429803

theorem tailTrace_2989421 : CollatzResearch.WordTrace tailWord_2989421 prefixEnd_2989421 511669950548151203429803 := by
  unfold tailWord_2989421
  simp only [CollatzResearch.WordTrace]
  refine ⟨109033141302845744304752117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72688760868563829536501411 109033141302845744304752117)
  ·
    refine ⟨10221856997141788528570511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109033141302845744304752117 10221856997141788528570511)
    ·
      refine ⟨15332785495712682792855767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10221856997141788528570511 15332785495712682792855767)
      ·
        refine ⟨22999178243569024189283651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15332785495712682792855767 22999178243569024189283651)
        ·
          refine ⟨34498767365353536283925477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22999178243569024189283651 34498767365353536283925477)
          ·
            refine ⟨6468518881003788053236027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34498767365353536283925477 6468518881003788053236027)
            ·
              refine ⟨9702778321505682079854041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468518881003788053236027 9702778321505682079854041)
              ·
                refine ⟨7277083741129261559890531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9702778321505682079854041 7277083741129261559890531)
                ·
                  refine ⟨10915625611693892339835797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7277083741129261559890531 10915625611693892339835797)
                  ·
                    refine ⟨511669950548151203429803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10915625611693892339835797 511669950548151203429803)
                    ·
                      rfl

theorem cell23_2989421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2989421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989421 prefixEnd_2989421 := by exact prefixLift 2989421
  have htrace : WordTrace (prefixWord ++ tailWord_2989421) baseStart_2989421 baseEnd_2989421 := by
    simpa [prefixWord, tailWord_2989421, baseEnd_2989421] using wordTrace_append hprefix tailTrace_2989421
  have hstable : (prefixWord ++ tailWord_2989421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989421).length < 2 ^ (prefixWord ++ tailWord_2989421).sum := by decide
  have hdescent : baseEnd_2989421 < baseStart_2989421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989461 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_2989461 : Nat := 118140960795 + 2989461 * 2 ^ 59
def prefixEnd_2989461 : Nat := 4983230072969 + 3 ^ 40 * 2989461 * 2
def baseEnd_2989461 : Nat := 1535030390870633453789225

theorem tailTrace_2989461 : CollatzResearch.WordTrace tailWord_2989461 prefixEnd_2989461 1535030390870633453789225 := by
  unfold tailWord_2989461
  simp only [CollatzResearch.WordTrace]
  refine ⟨109034600222700831136208237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72689733481800554090805491 109034600222700831136208237)
  ·
    refine ⟨40887975083512811676078089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109034600222700831136208237 40887975083512811676078089)
    ·
      refine ⟨30665981312634608757058567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40887975083512811676078089 30665981312634608757058567)
      ·
        refine ⟨45998971968951913135587851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30665981312634608757058567 45998971968951913135587851)
        ·
          refine ⟨68998457953427869703381777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45998971968951913135587851 68998457953427869703381777)
          ·
            refine ⟨51748843465070902277536333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68998457953427869703381777 51748843465070902277536333)
            ·
              refine ⟨19405816299401588354076125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51748843465070902277536333 19405816299401588354076125)
              ·
                refine ⟨7277181112275595632778547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19405816299401588354076125 7277181112275595632778547)
                ·
                  refine ⟨10915771668413393449167821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7277181112275595632778547 10915771668413393449167821)
                  ·
                    refine ⟨4093414375655022543437933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10915771668413393449167821 4093414375655022543437933)
                    ·
                      refine ⟨1535030390870633453789225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4093414375655022543437933 1535030390870633453789225)
                      ·
                        rfl

theorem cell23_2989461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_2989461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989461 prefixEnd_2989461 := by exact prefixLift 2989461
  have htrace : WordTrace (prefixWord ++ tailWord_2989461) baseStart_2989461 baseEnd_2989461 := by
    simpa [prefixWord, tailWord_2989461, baseEnd_2989461] using wordTrace_append hprefix tailTrace_2989461
  have hstable : (prefixWord ++ tailWord_2989461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989461).length < 2 ^ (prefixWord ++ tailWord_2989461).sum := by decide
  have hdescent : baseEnd_2989461 < baseStart_2989461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989506 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2989506 : Nat := 118140960795 + 2989506 * 2 ^ 59
def prefixEnd_2989506 : Nat := 4983230072969 + 3 ^ 40 * 2989506 * 2
def baseEnd_2989506 : Nat := 511684499166695259242173

theorem tailTrace_2989506 : CollatzResearch.WordTrace tailWord_2989506 prefixEnd_2989506 511684499166695259242173 := by
  unfold tailWord_2989506
  simp only [CollatzResearch.WordTrace]
  refine ⟨27259060376884450955399093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72690827671691869214397581 27259060376884450955399093)
  ·
    refine ⟨2555536910332917277068665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27259060376884450955399093 2555536910332917277068665)
    ·
      refine ⟨1916652682749687957801499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2555536910332917277068665 1916652682749687957801499)
      ·
        refine ⟨2874979024124531936702249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916652682749687957801499 2874979024124531936702249)
        ·
          refine ⟨2156234268093398952526687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2874979024124531936702249 2156234268093398952526687)
          ·
            refine ⟨3234351402140098428790031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156234268093398952526687 3234351402140098428790031)
            ·
              refine ⟨4851527103210147643185047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234351402140098428790031 4851527103210147643185047)
              ·
                refine ⟨7277290654815221464777571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851527103210147643185047 7277290654815221464777571)
                ·
                  refine ⟨10915935982222832197166357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7277290654815221464777571 10915935982222832197166357)
                  ·
                    refine ⟨511684499166695259242173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10915935982222832197166357 511684499166695259242173)
                    ·
                      rfl

theorem cell23_2989506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2989506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989506 prefixEnd_2989506 := by exact prefixLift 2989506
  have htrace : WordTrace (prefixWord ++ tailWord_2989506) baseStart_2989506 baseEnd_2989506 := by
    simpa [prefixWord, tailWord_2989506, baseEnd_2989506] using wordTrace_append hprefix tailTrace_2989506
  have hstable : (prefixWord ++ tailWord_2989506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989506).length < 2 ^ (prefixWord ++ tailWord_2989506).sum := by decide
  have hdescent : baseEnd_2989506 < baseStart_2989506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989551 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 3]
def baseStart_2989551 : Nat := 118140960795 + 2989551 * 2 ^ 59
def prefixEnd_2989551 : Nat := 4983230072969 + 3 ^ 40 * 2989551 * 2
def baseEnd_2989551 : Nat := 1535076604129538101663811

theorem tailTrace_2989551 : CollatzResearch.WordTrace tailWord_2989551 prefixEnd_2989551 1535076604129538101663811 := by
  unfold tailWord_2989551
  simp only [CollatzResearch.WordTrace]
  refine ⟨109037882792374776506984507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72691921861583184337989671 109037882792374776506984507)
  ·
    refine ⟨163556824188562164760476761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109037882792374776506984507 163556824188562164760476761)
    ·
      refine ⟨122667618141421623570357571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163556824188562164760476761 122667618141421623570357571)
      ·
        refine ⟨184001427212132435355536357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122667618141421623570357571 184001427212132435355536357)
        ·
          refine ⟨34500267602274831629163067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184001427212132435355536357 34500267602274831629163067)
          ·
            refine ⟨51750401403412247443744601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34500267602274831629163067 51750401403412247443744601)
            ·
              refine ⟨38812801052559185582808451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51750401403412247443744601 38812801052559185582808451)
              ·
                refine ⟨58219201578838778374212677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38812801052559185582808451 58219201578838778374212677)
                ·
                  refine ⟨10916100296032270945164877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58219201578838778374212677 10916100296032270945164877)
                  ·
                    refine ⟨4093537611012101604436829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10916100296032270945164877 4093537611012101604436829)
                    ·
                      refine ⟨1535076604129538101663811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4093537611012101604436829 1535076604129538101663811)
                      ·
                        rfl

theorem cell23_2989551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_2989551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989551 prefixEnd_2989551 := by exact prefixLift 2989551
  have htrace : WordTrace (prefixWord ++ tailWord_2989551) baseStart_2989551 baseEnd_2989551 := by
    simpa [prefixWord, tailWord_2989551, baseEnd_2989551] using wordTrace_append hprefix tailTrace_2989551
  have hstable : (prefixWord ++ tailWord_2989551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989551).length < 2 ^ (prefixWord ++ tailWord_2989551).sum := by decide
  have hdescent : baseEnd_2989551 < baseStart_2989551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989558 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_2989558 : Nat := 118140960795 + 2989558 * 2 ^ 59
def prefixEnd_2989558 : Nat := 4983230072969 + 3 ^ 40 * 2989558 * 2
def baseEnd_2989558 : Nat := 170564466499346619364031

theorem tailTrace_2989558 : CollatzResearch.WordTrace tailWord_2989558 prefixEnd_2989558 170564466499346619364031 := by
  unfold tailWord_2989558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6814883631459338543905583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72692092068899611134992885 6814883631459338543905583)
  ·
    refine ⟨10222325447189007815858375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6814883631459338543905583 10222325447189007815858375)
    ·
      refine ⟨15333488170783511723787563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10222325447189007815858375 15333488170783511723787563)
      ·
        refine ⟨23000232256175267585681345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15333488170783511723787563 23000232256175267585681345)
        ·
          refine ⟨17250174192131450689261009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23000232256175267585681345 17250174192131450689261009)
          ·
            refine ⟨12937630644098588016945757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17250174192131450689261009 12937630644098588016945757)
            ·
              refine ⟨4851611491536970506354659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12937630644098588016945757 4851611491536970506354659)
              ·
                refine ⟨7277417237305455759531989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851611491536970506354659 7277417237305455759531989)
                ·
                  refine ⟨170564466499346619364031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7277417237305455759531989 170564466499346619364031)
                  ·
                    rfl

theorem cell23_2989558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_2989558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989558 prefixEnd_2989558 := by exact prefixLift 2989558
  have htrace : WordTrace (prefixWord ++ tailWord_2989558) baseStart_2989558 baseEnd_2989558 := by
    simpa [prefixWord, tailWord_2989558, baseEnd_2989558] using wordTrace_append hprefix tailTrace_2989558
  have hstable : (prefixWord ++ tailWord_2989558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989558).length < 2 ^ (prefixWord ++ tailWord_2989558).sum := by decide
  have hdescent : baseEnd_2989558 < baseStart_2989558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989611 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 3]
def baseStart_2989611 : Nat := 118140960795 + 2989611 * 2 ^ 59
def prefixEnd_2989611 : Nat := 4983230072969 + 3 ^ 40 * 2989611 * 2
def baseEnd_2989611 : Nat := 1535107412968807866913535

theorem tailTrace_2989611 : CollatzResearch.WordTrace tailWord_2989611 prefixEnd_2989611 1535107412968807866913535 := by
  unfold tailWord_2989611
  simp only [CollatzResearch.WordTrace]
  refine ⟨109040071172157406754168687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72693380781438271169445791 109040071172157406754168687)
  ·
    refine ⟨163560106758236110131253031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109040071172157406754168687 163560106758236110131253031)
    ·
      refine ⟨245340160137354165196879547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163560106758236110131253031 245340160137354165196879547)
      ·
        refine ⟨368010240206031247795319321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245340160137354165196879547 368010240206031247795319321)
        ·
          refine ⟨276007680154523435846489491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368010240206031247795319321 276007680154523435846489491)
          ·
            refine ⟨414011520231785153769734237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276007680154523435846489491 414011520231785153769734237)
            ·
              refine ⟨155254320086919432663650339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414011520231785153769734237 155254320086919432663650339)
              ·
                refine ⟨232881480130379148995475509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155254320086919432663650339 232881480130379148995475509)
                ·
                  refine ⟨21832638762223045218325829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232881480130379148995475509 21832638762223045218325829)
                  ·
                    refine ⟨4093619767916820978436093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21832638762223045218325829 4093619767916820978436093)
                    ·
                      refine ⟨1535107412968807866913535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4093619767916820978436093 1535107412968807866913535)
                      ·
                        rfl

theorem cell23_2989611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 3].length) (baseStart_2989611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989611 prefixEnd_2989611 := by exact prefixLift 2989611
  have htrace : WordTrace (prefixWord ++ tailWord_2989611) baseStart_2989611 baseEnd_2989611 := by
    simpa [prefixWord, tailWord_2989611, baseEnd_2989611] using wordTrace_append hprefix tailTrace_2989611
  have hstable : (prefixWord ++ tailWord_2989611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989611).length < 2 ^ (prefixWord ++ tailWord_2989611).sum := by decide
  have hdescent : baseEnd_2989611 < baseStart_2989611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989618 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_2989618 : Nat := 118140960795 + 2989618 * 2 ^ 59
def prefixEnd_2989618 : Nat := 4983230072969 + 3 ^ 40 * 2989618 * 2
def baseEnd_2989618 : Nat := 511703669111129779842001

theorem tailTrace_2989618 : CollatzResearch.WordTrace tailWord_2989618 prefixEnd_2989618 511703669111129779842001 := by
  unfold tailWord_2989618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27260081620783011737418377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72693550988754697966449005 27260081620783011737418377)
  ·
    refine ⟨20445061215587258803063783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27260081620783011737418377 20445061215587258803063783)
    ·
      refine ⟨30667591823380888204595675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20445061215587258803063783 30667591823380888204595675)
      ·
        refine ⟨46001387735071332306893513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30667591823380888204595675 46001387735071332306893513)
        ·
          refine ⟨34501040801303499230170135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46001387735071332306893513 34501040801303499230170135)
          ·
            refine ⟨51751561201955248845255203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34501040801303499230170135 51751561201955248845255203)
            ·
              refine ⟨77627341802932873267882805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51751561201955248845255203 77627341802932873267882805)
              ·
                refine ⟨7277563294024956868864013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77627341802932873267882805 7277563294024956868864013)
                ·
                  refine ⟨2729086235259358825824005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7277563294024956868864013 2729086235259358825824005)
                  ·
                    refine ⟨511703669111129779842001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729086235259358825824005 511703669111129779842001)
                    ·
                      rfl

theorem cell23_2989618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_2989618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989618 prefixEnd_2989618 := by exact prefixLift 2989618
  have htrace : WordTrace (prefixWord ++ tailWord_2989618) baseStart_2989618 baseEnd_2989618 := by
    simpa [prefixWord, tailWord_2989618, baseEnd_2989618] using wordTrace_append hprefix tailTrace_2989618
  have hstable : (prefixWord ++ tailWord_2989618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989618).length < 2 ^ (prefixWord ++ tailWord_2989618).sum := by decide
  have hdescent : baseEnd_2989618 < baseStart_2989618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989625 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 2, 4, 2]
def baseStart_2989625 : Nat := 118140960795 + 2989625 * 2 ^ 59
def prefixEnd_2989625 : Nat := 4983230072969 + 3 ^ 40 * 2989625 * 2
def baseEnd_2989625 : Nat := 1535114601697970812138471

theorem tailTrace_2989625 : CollatzResearch.WordTrace tailWord_2989625 prefixEnd_2989625 1535114601697970812138471 := by
  unfold tailWord_2989625
  simp only [CollatzResearch.WordTrace]
  refine ⟨109040581794106687145178329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72693721196071124763452219 109040581794106687145178329)
  ·
    refine ⟨81780436345580015358883747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109040581794106687145178329 81780436345580015358883747)
    ·
      refine ⟨122670654518370023038325621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81780436345580015358883747 122670654518370023038325621)
      ·
        refine ⟨11500373861097189659843027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122670654518370023038325621 11500373861097189659843027)
        ·
          refine ⟨17250560791645784489764541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11500373861097189659843027 17250560791645784489764541)
          ·
            refine ⟨6468960296867169183661703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17250560791645784489764541 6468960296867169183661703)
            ·
              refine ⟨9703440445300753775492555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468960296867169183661703 9703440445300753775492555)
              ·
                refine ⟨14555160667951130663238833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9703440445300753775492555 14555160667951130663238833)
                ·
                  refine ⟨10916370500963347997429125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14555160667951130663238833 10916370500963347997429125)
                  ·
                    refine ⟨2046819468930627749517961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10916370500963347997429125 2046819468930627749517961)
                    ·
                      refine ⟨1535114601697970812138471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046819468930627749517961 1535114601697970812138471)
                      ·
                        rfl

theorem cell23_2989625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_2989625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989625 prefixEnd_2989625 := by exact prefixLift 2989625
  have htrace : WordTrace (prefixWord ++ tailWord_2989625) baseStart_2989625 baseEnd_2989625 := by
    simpa [prefixWord, tailWord_2989625, baseEnd_2989625] using wordTrace_append hprefix tailTrace_2989625
  have hstable : (prefixWord ++ tailWord_2989625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989625).length < 2 ^ (prefixWord ++ tailWord_2989625).sum := by decide
  have hdescent : baseEnd_2989625 < baseStart_2989625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989652 : List Nat := [2, 4, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_2989652 : Nat := 118140960795 + 2989652 * 2 ^ 59
def prefixEnd_2989652 : Nat := 4983230072969 + 3 ^ 40 * 2989652 * 2
def baseEnd_2989652 : Nat := 511709488558547402166949

theorem tailTrace_2989652 : CollatzResearch.WordTrace tailWord_2989652 prefixEnd_2989652 511709488558547402166949 := by
  unfold tailWord_2989652
  simp only [CollatzResearch.WordTrace]
  refine ⟨54520783282504435378205605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72694377710005913837607473 54520783282504435378205605)
  ·
    refine ⟨10222646865469581633413551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54520783282504435378205605 10222646865469581633413551)
    ·
      refine ⟨15333970298204372450120327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10222646865469581633413551 15333970298204372450120327)
      ·
        refine ⟨23000955447306558675180491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15333970298204372450120327 23000955447306558675180491)
        ·
          refine ⟨34501433170959838012770737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23000955447306558675180491 34501433170959838012770737)
          ·
            refine ⟨25876074878219878509578053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34501433170959838012770737 25876074878219878509578053)
            ·
              refine ⟨4851764039666227220545885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25876074878219878509578053 4851764039666227220545885)
              ·
                refine ⟨1819411514874835207704707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4851764039666227220545885 1819411514874835207704707)
                ·
                  refine ⟨2729117272312252811557061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819411514874835207704707 2729117272312252811557061)
                  ·
                    refine ⟨511709488558547402166949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729117272312252811557061 511709488558547402166949)
                    ·
                      rfl

theorem cell23_2989652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_2989652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989652 prefixEnd_2989652 := by exact prefixLift 2989652
  have htrace : WordTrace (prefixWord ++ tailWord_2989652) baseStart_2989652 baseEnd_2989652 := by
    simpa [prefixWord, tailWord_2989652, baseEnd_2989652] using wordTrace_append hprefix tailTrace_2989652
  have hstable : (prefixWord ++ tailWord_2989652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989652).length < 2 ^ (prefixWord ++ tailWord_2989652).sum := by decide
  have hdescent : baseEnd_2989652 < baseStart_2989652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989708 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_2989708 : Nat := 118140960795 + 2989708 * 2 ^ 59
def prefixEnd_2989708 : Nat := 4983230072969 + 3 ^ 40 * 2989708 * 2
def baseEnd_2989708 : Nat := 511719073530764662466863

theorem tailTrace_2989708 : CollatzResearch.WordTrace tailWord_2989708 prefixEnd_2989708 511719073530764662466863 := by
  unfold tailWord_2989708
  simp only [CollatzResearch.WordTrace]
  refine ⟨54521804526402996160224889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72695739368537328213633185 54521804526402996160224889)
  ·
    refine ⟨40891353394802247120168667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54521804526402996160224889 40891353394802247120168667)
    ·
      refine ⟨61337030092203370680253001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40891353394802247120168667 61337030092203370680253001)
      ·
        refine ⟨46002772569152528010189751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61337030092203370680253001 46002772569152528010189751)
        ·
          refine ⟨69004158853728792015284627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46002772569152528010189751 69004158853728792015284627)
          ·
            refine ⟨103506238280593188022926941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69004158853728792015284627 103506238280593188022926941)
            ·
              refine ⟨38814839355222445508597603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103506238280593188022926941 38814839355222445508597603)
              ·
                refine ⟨58222259032833668262896405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38814839355222445508597603 58222259032833668262896405)
                ·
                  refine ⟨2729168392164078199823269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58222259032833668262896405 2729168392164078199823269)
                  ·
                    refine ⟨511719073530764662466863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729168392164078199823269 511719073530764662466863)
                    ·
                      rfl

theorem cell23_2989708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_2989708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989708 prefixEnd_2989708 := by exact prefixLift 2989708
  have htrace : WordTrace (prefixWord ++ tailWord_2989708) baseStart_2989708 baseEnd_2989708 := by
    simpa [prefixWord, tailWord_2989708, baseEnd_2989708] using wordTrace_append hprefix tailTrace_2989708
  have hstable : (prefixWord ++ tailWord_2989708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989708).length < 2 ^ (prefixWord ++ tailWord_2989708).sum := by decide
  have hdescent : baseEnd_2989708 < baseStart_2989708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989711 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_2989711 : Nat := 118140960795 + 2989711 * 2 ^ 59
def prefixEnd_2989711 : Nat := 4983230072969 + 3 ^ 40 * 2989711 * 2
def baseEnd_2989711 : Nat := 1535158761034257475663075

theorem tailTrace_2989711 : CollatzResearch.WordTrace tailWord_2989711 prefixEnd_2989711 1535158761034257475663075 := by
  unfold tailWord_2989711
  simp only [CollatzResearch.WordTrace]
  refine ⟨109043718471795123832808987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72695812314530082555205991 109043718471795123832808987)
  ·
    refine ⟨163565577707692685749213481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109043718471795123832808987 163565577707692685749213481)
    ·
      refine ⟨122674183280769514311910111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163565577707692685749213481 122674183280769514311910111)
      ·
        refine ⟨184011274921154271467865167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122674183280769514311910111 184011274921154271467865167)
        ·
          refine ⟨276016912381731407201797751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184011274921154271467865167 276016912381731407201797751)
          ·
            refine ⟨414025368572597110802696627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276016912381731407201797751 414025368572597110802696627)
            ·
              refine ⟨621038052858895666204044941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414025368572597110802696627 621038052858895666204044941)
              ·
                refine ⟨232889269822085874826516853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621038052858895666204044941 232889269822085874826516853)
                ·
                  refine ⟨21833369045820550764985955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232889269822085874826516853 21833369045820550764985955)
                  ·
                    refine ⟨32750053568730826147478933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21833369045820550764985955 32750053568730826147478933)
                    ·
                      refine ⟨1535158761034257475663075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32750053568730826147478933 1535158761034257475663075)
                      ·
                        rfl

theorem cell23_2989711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_2989711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989711 prefixEnd_2989711 := by exact prefixLift 2989711
  have htrace : WordTrace (prefixWord ++ tailWord_2989711) baseStart_2989711 baseEnd_2989711 := by
    simpa [prefixWord, tailWord_2989711, baseEnd_2989711] using wordTrace_append hprefix tailTrace_2989711
  have hstable : (prefixWord ++ tailWord_2989711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989711).length < 2 ^ (prefixWord ++ tailWord_2989711).sum := by decide
  have hdescent : baseEnd_2989711 < baseStart_2989711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989725 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2989725 : Nat := 118140960795 + 2989725 * 2 ^ 59
def prefixEnd_2989725 : Nat := 4983230072969 + 3 ^ 40 * 2989725 * 2
def baseEnd_2989725 : Nat := 511721983254473473629337

theorem tailTrace_2989725 : CollatzResearch.WordTrace tailWord_2989725 prefixEnd_2989725 511721983254473473629337 := by
  unfold tailWord_2989725
  simp only [CollatzResearch.WordTrace]
  refine ⟨109044229093744404223818629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72696152729162936149212419 109044229093744404223818629)
  ·
    refine ⟨20445792955077075791965993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109044229093744404223818629 20445792955077075791965993)
    ·
      refine ⟨15334344716307806843974495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20445792955077075791965993 15334344716307806843974495)
      ·
        refine ⟨23001517074461710265961743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15334344716307806843974495 23001517074461710265961743)
        ·
          refine ⟨34502275611692565398942615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23001517074461710265961743 34502275611692565398942615)
          ·
            refine ⟨51753413417538848098413923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34502275611692565398942615 51753413417538848098413923)
            ·
              refine ⟨77630120126308272147620885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51753413417538848098413923 77630120126308272147620885)
              ·
                refine ⟨3638911880920700256919729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77630120126308272147620885 3638911880920700256919729)
                ·
                  refine ⟨2729183910690525192689797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3638911880920700256919729 2729183910690525192689797)
                  ·
                    refine ⟨511721983254473473629337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729183910690525192689797 511721983254473473629337)
                    ·
                      rfl

theorem cell23_2989725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2989725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989725 prefixEnd_2989725 := by exact prefixLift 2989725
  have htrace : WordTrace (prefixWord ++ tailWord_2989725) baseStart_2989725 baseEnd_2989725 := by
    simpa [prefixWord, tailWord_2989725, baseEnd_2989725] using wordTrace_append hprefix tailTrace_2989725
  have hstable : (prefixWord ++ tailWord_2989725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989725).length < 2 ^ (prefixWord ++ tailWord_2989725).sum := by decide
  have hdescent : baseEnd_2989725 < baseStart_2989725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989728 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_2989728 : Nat := 118140960795 + 2989728 * 2 ^ 59
def prefixEnd_2989728 : Nat := 4983230072969 + 3 ^ 40 * 2989728 * 2
def baseEnd_2989728 : Nat := 1535167490205383909150497

theorem tailTrace_2989728 : CollatzResearch.WordTrace tailWord_2989728 prefixEnd_2989728 1535167490205383909150497 := by
  unfold tailWord_2989728
  simp only [CollatzResearch.WordTrace]
  refine ⟨54522169256366767868088919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72696225675155690490785225 54522169256366767868088919)
  ·
    refine ⟨81783253884550151802133379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54522169256366767868088919 81783253884550151802133379)
    ·
      refine ⟨122674880826825227703200069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81783253884550151802133379 122674880826825227703200069)
      ·
        refine ⟨23001540155029730194350013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122674880826825227703200069 23001540155029730194350013)
        ·
          refine ⟨8625577558136148822881255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23001540155029730194350013 8625577558136148822881255)
          ·
            refine ⟨12938366337204223234321883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8625577558136148822881255 12938366337204223234321883)
            ·
              refine ⟨19407549505806334851482825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12938366337204223234321883 19407549505806334851482825)
              ·
                refine ⟨14555662129354751138612119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19407549505806334851482825 14555662129354751138612119)
                ·
                  refine ⟨21833493194032126707918179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14555662129354751138612119 21833493194032126707918179)
                  ·
                    refine ⟨32750239791048190061877269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21833493194032126707918179 32750239791048190061877269)
                    ·
                      refine ⟨1535167490205383909150497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32750239791048190061877269 1535167490205383909150497)
                      ·
                        rfl

theorem cell23_2989728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_2989728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989728 prefixEnd_2989728 := by exact prefixLift 2989728
  have htrace : WordTrace (prefixWord ++ tailWord_2989728) baseStart_2989728 baseEnd_2989728 := by
    simpa [prefixWord, tailWord_2989728, baseEnd_2989728] using wordTrace_append hprefix tailTrace_2989728
  have hstable : (prefixWord ++ tailWord_2989728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989728).length < 2 ^ (prefixWord ++ tailWord_2989728).sum := by decide
  have hdescent : baseEnd_2989728 < baseStart_2989728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989749 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2989749 : Nat := 118140960795 + 2989749 * 2 ^ 59
def prefixEnd_2989749 : Nat := 4983230072969 + 3 ^ 40 * 2989749 * 2
def baseEnd_2989749 : Nat := 1535178273299128326987901

theorem tailTrace_2989749 : CollatzResearch.WordTrace tailWord_2989749 prefixEnd_2989749 1535178273299128326987901 := by
  unfold tailWord_2989749
  simp only [CollatzResearch.WordTrace]
  refine ⟨109045104445657456322692301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72696736297104970881794867 109045104445657456322692301)
  ·
    refine ⟨40891914167121546121009613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109045104445657456322692301 40891914167121546121009613)
    ·
      refine ⟨15334467812670579795378605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40891914167121546121009613 15334467812670579795378605)
      ·
        refine ⟨5750425429751467423266977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15334467812670579795378605 5750425429751467423266977)
        ·
          refine ⟨4312819072313600567450233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5750425429751467423266977 4312819072313600567450233)
          ·
            refine ⟨3234614304235200425587675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4312819072313600567450233 3234614304235200425587675)
            ·
              refine ⟨4851921456352800638381513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234614304235200425587675 4851921456352800638381513)
              ·
                refine ⟨3638941092264600478786135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4851921456352800638381513 3638941092264600478786135)
                ·
                  refine ⟨5458411638396900718179203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638941092264600478786135 5458411638396900718179203)
                  ·
                    refine ⟨8187617457595351077268805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5458411638396900718179203 8187617457595351077268805)
                    ·
                      refine ⟨1535178273299128326987901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8187617457595351077268805 1535178273299128326987901)
                      ·
                        rfl

theorem cell23_2989749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2989749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989749 prefixEnd_2989749 := by exact prefixLift 2989749
  have htrace : WordTrace (prefixWord ++ tailWord_2989749) baseStart_2989749 baseEnd_2989749 := by
    simpa [prefixWord, tailWord_2989749, baseEnd_2989749] using wordTrace_append hprefix tailTrace_2989749
  have hstable : (prefixWord ++ tailWord_2989749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989749).length < 2 ^ (prefixWord ++ tailWord_2989749).sum := by decide
  have hdescent : baseEnd_2989749 < baseStart_2989749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989789 : List Nat := [1, 4, 3, 3, 2, 1, 1, 8]
def baseStart_2989789 : Nat := 118140960795 + 2989789 * 2 ^ 59
def prefixEnd_2989789 : Nat := 4983230072969 + 3 ^ 40 * 2989789 * 2
def baseEnd_2989789 : Nat := 56859215278715117425471

theorem tailTrace_2989789 : CollatzResearch.WordTrace tailWord_2989789 prefixEnd_2989789 56859215278715117425471 := by
  unfold tailWord_2989789
  simp only [CollatzResearch.WordTrace]
  refine ⟨109046563365512543154148421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72697708910341695436098947 109046563365512543154148421)
  ·
    refine ⟨20446230631033601841402829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109046563365512543154148421 20446230631033601841402829)
    ·
      refine ⟨7667336486637600690526061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20446230631033601841402829 7667336486637600690526061)
      ·
        refine ⟨2875251182489100258947273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7667336486637600690526061 2875251182489100258947273)
        ·
          refine ⟨2156438386866825194210455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2875251182489100258947273 2156438386866825194210455)
          ·
            refine ⟨3234657580300237791315683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156438386866825194210455 3234657580300237791315683)
            ·
              refine ⟨4851986370450356686973525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234657580300237791315683 4851986370450356686973525)
              ·
                refine ⟨56859215278715117425471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4851986370450356686973525 56859215278715117425471)
                ·
                  rfl

theorem cell23_2989789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 8].length) (baseStart_2989789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989789 prefixEnd_2989789 := by exact prefixLift 2989789
  have htrace : WordTrace (prefixWord ++ tailWord_2989789) baseStart_2989789 baseEnd_2989789 := by
    simpa [prefixWord, tailWord_2989789, baseEnd_2989789] using wordTrace_append hprefix tailTrace_2989789
  have hstable : (prefixWord ++ tailWord_2989789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989789).length < 2 ^ (prefixWord ++ tailWord_2989789).sum := by decide
  have hdescent : baseEnd_2989789 < baseStart_2989789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989799 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2989799 : Nat := 118140960795 + 2989799 * 2 ^ 59
def prefixEnd_2989799 : Nat := 4983230072969 + 3 ^ 40 * 2989799 * 2
def baseEnd_2989799 : Nat := 1535203947331853131362671

theorem tailTrace_2989799 : CollatzResearch.WordTrace tailWord_2989799 prefixEnd_2989799 1535203947331853131362671 := by
  unfold tailWord_2989799
  simp only [CollatzResearch.WordTrace]
  refine ⟨109046928095476314862012451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72697952063650876574674967 109046928095476314862012451)
  ·
    refine ⟨163570392143214472293018677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109046928095476314862012451 163570392143214472293018677)
    ·
      refine ⟨15334724263426356777470501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163570392143214472293018677 15334724263426356777470501)
      ·
        refine ⟨2875260799392441895775719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15334724263426356777470501 2875260799392441895775719)
        ·
          refine ⟨4312891199088662843663579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875260799392441895775719 4312891199088662843663579)
          ·
            refine ⟨6469336798632994265495369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312891199088662843663579 6469336798632994265495369)
            ·
              refine ⟨4852002598974745699121527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6469336798632994265495369 4852002598974745699121527)
              ·
                refine ⟨7278003898462118548682291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852002598974745699121527 7278003898462118548682291)
                ·
                  refine ⟨10917005847693177823023437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7278003898462118548682291 10917005847693177823023437)
                  ·
                    refine ⟨4093877192884941683633789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10917005847693177823023437 4093877192884941683633789)
                    ·
                      refine ⟨1535203947331853131362671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4093877192884941683633789 1535203947331853131362671)
                      ·
                        rfl

theorem cell23_2989799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2989799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989799 prefixEnd_2989799 := by exact prefixLift 2989799
  have htrace : WordTrace (prefixWord ++ tailWord_2989799) baseStart_2989799 baseEnd_2989799 := by
    simpa [prefixWord, tailWord_2989799, baseEnd_2989799] using wordTrace_append hprefix tailTrace_2989799
  have hstable : (prefixWord ++ tailWord_2989799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989799).length < 2 ^ (prefixWord ++ tailWord_2989799).sum := by decide
  have hdescent : baseEnd_2989799 < baseStart_2989799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989808 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_2989808 : Nat := 118140960795 + 2989808 * 2 ^ 59
def prefixEnd_2989808 : Nat := 4983230072969 + 3 ^ 40 * 2989808 * 2
def baseEnd_2989808 : Nat := 1535208568657743596150129

theorem tailTrace_2989808 : CollatzResearch.WordTrace tailWord_2989808 prefixEnd_2989808 1535208568657743596150129 := by
  unfold tailWord_2989808
  simp only [CollatzResearch.WordTrace]
  refine ⟨54523628176221854699545039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72698170901629139599393385 54523628176221854699545039)
  ·
    refine ⟨81785442264332782049317559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54523628176221854699545039 81785442264332782049317559)
    ·
      refine ⟨122678163396499173073976339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81785442264332782049317559 122678163396499173073976339)
      ·
        refine ⟨184017245094748759610964509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122678163396499173073976339 184017245094748759610964509)
        ·
          refine ⟨69006466910530784854111691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184017245094748759610964509 69006466910530784854111691)
          ·
            refine ⟨103509700365796177281167537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69006466910530784854111691 103509700365796177281167537)
            ·
              refine ⟨77632275274347132960875653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103509700365796177281167537 77632275274347132960875653)
              ·
                refine ⟨14556051613940087430164185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77632275274347132960875653 14556051613940087430164185)
                ·
                  refine ⟨10917038710455065572623139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14556051613940087430164185 10917038710455065572623139)
                  ·
                    refine ⟨16375558065682598358934709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10917038710455065572623139 16375558065682598358934709)
                    ·
                      refine ⟨1535208568657743596150129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16375558065682598358934709 1535208568657743596150129)
                      ·
                        rfl

theorem cell23_2989808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_2989808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989808 prefixEnd_2989808 := by exact prefixLift 2989808
  have htrace : WordTrace (prefixWord ++ tailWord_2989808) baseStart_2989808 baseEnd_2989808 := by
    simpa [prefixWord, tailWord_2989808, baseEnd_2989808] using wordTrace_append hprefix tailTrace_2989808
  have hstable : (prefixWord ++ tailWord_2989808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989808).length < 2 ^ (prefixWord ++ tailWord_2989808).sum := by decide
  have hdescent : baseEnd_2989808 < baseStart_2989808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989818 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_2989818 : Nat := 118140960795 + 2989818 * 2 ^ 59
def prefixEnd_2989818 : Nat := 4983230072969 + 3 ^ 40 * 2989818 * 2
def baseEnd_2989818 : Nat := 1535213703464288557025083

theorem tailTrace_2989818 : CollatzResearch.WordTrace tailWord_2989818 prefixEnd_2989818 1535213703464288557025083 := by
  unfold tailWord_2989818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27261905270601870276738527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72698414054938320737969405 27261905270601870276738527)
  ·
    refine ⟨40892857905902805415107791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27261905270601870276738527 40892857905902805415107791)
    ·
      refine ⟨61339286858854208122661687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40892857905902805415107791 61339286858854208122661687)
      ·
        refine ⟨92008930288281312183992531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61339286858854208122661687 92008930288281312183992531)
        ·
          refine ⟨138013395432421968275988797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92008930288281312183992531 138013395432421968275988797)
          ·
            refine ⟨51755023287158238103495799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138013395432421968275988797 51755023287158238103495799)
            ·
              refine ⟨77632534930737357155243699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51755023287158238103495799 77632534930737357155243699)
              ·
                refine ⟨116448802396106035732865549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77632534930737357155243699 116448802396106035732865549)
                ·
                  refine ⟨43668300898539763399824581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116448802396106035732865549 43668300898539763399824581)
                  ·
                    refine ⟨8187806418476205637467109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43668300898539763399824581 8187806418476205637467109)
                    ·
                      refine ⟨1535213703464288557025083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8187806418476205637467109 1535213703464288557025083)
                      ·
                        rfl

theorem cell23_2989818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_2989818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989818 prefixEnd_2989818 := by exact prefixLift 2989818
  have htrace : WordTrace (prefixWord ++ tailWord_2989818) baseStart_2989818 baseEnd_2989818 := by
    simpa [prefixWord, tailWord_2989818, baseEnd_2989818] using wordTrace_append hprefix tailTrace_2989818
  have hstable : (prefixWord ++ tailWord_2989818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989818).length < 2 ^ (prefixWord ++ tailWord_2989818).sum := by decide
  have hdescent : baseEnd_2989818 < baseStart_2989818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989845 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 7]
def baseStart_2989845 : Nat := 118140960795 + 2989845 * 2 ^ 59
def prefixEnd_2989845 : Nat := 4983230072969 + 3 ^ 40 * 2989845 * 2
def baseEnd_2989845 : Nat := 170580840826884439043051

theorem tailTrace_2989845 : CollatzResearch.WordTrace tailWord_2989845 prefixEnd_2989845 170580840826884439043051 := by
  unfold tailWord_2989845
  simp only [CollatzResearch.WordTrace]
  refine ⟨109048605853309664718186989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72699070568873109812124659 109048605853309664718186989)
  ·
    refine ⟨40893227194991124269320121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109048605853309664718186989 40893227194991124269320121)
    ·
      refine ⟨30669920396243343201990091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40893227194991124269320121 30669920396243343201990091)
      ·
        refine ⟨46004880594365014802985137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30669920396243343201990091 46004880594365014802985137)
        ·
          refine ⟨34503660445773761102238853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46004880594365014802985137 34503660445773761102238853)
          ·
            refine ⟨6469436333582580206669785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34503660445773761102238853 6469436333582580206669785)
            ·
              refine ⟨4852077250186935155002339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6469436333582580206669785 4852077250186935155002339)
              ·
                refine ⟨7278115875280402732503509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852077250186935155002339 7278115875280402732503509)
                ·
                  refine ⟨170580840826884439043051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7278115875280402732503509 170580840826884439043051)
                  ·
                    rfl

theorem cell23_2989845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_2989845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989845 prefixEnd_2989845 := by exact prefixLift 2989845
  have htrace : WordTrace (prefixWord ++ tailWord_2989845) baseStart_2989845 baseEnd_2989845 := by
    simpa [prefixWord, tailWord_2989845, baseEnd_2989845] using wordTrace_append hprefix tailTrace_2989845
  have hstable : (prefixWord ++ tailWord_2989845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989845).length < 2 ^ (prefixWord ++ tailWord_2989845).sum := by decide
  have hdescent : baseEnd_2989845 < baseStart_2989845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989855 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 3]
def baseStart_2989855 : Nat := 118140960795 + 2989855 * 2 ^ 59
def prefixEnd_2989855 : Nat := 4983230072969 + 3 ^ 40 * 2989855 * 2
def baseEnd_2989855 : Nat := 1535232702248504912262413

theorem tailTrace_2989855 : CollatzResearch.WordTrace tailWord_2989855 prefixEnd_2989855 1535232702248504912262413 := by
  unfold tailWord_2989855
  simp only [CollatzResearch.WordTrace]
  refine ⟨109048970583273436426051019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72699313722182290950700679 109048970583273436426051019)
  ·
    refine ⟨163573455874910154639076529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109048970583273436426051019 163573455874910154639076529)
    ·
      refine ⟨122680091906182615979307397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163573455874910154639076529 122680091906182615979307397)
      ·
        refine ⟨23002517232409240496120137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122680091906182615979307397 23002517232409240496120137)
        ·
          refine ⟨17251887924306930372090103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23002517232409240496120137 17251887924306930372090103)
          ·
            refine ⟨25877831886460395558135155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17251887924306930372090103 25877831886460395558135155)
            ·
              refine ⟨38816747829690593337202733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25877831886460395558135155 38816747829690593337202733)
              ·
                refine ⟨14556280436133972501451025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38816747829690593337202733 14556280436133972501451025)
                ·
                  refine ⟨10917210327100479376088269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14556280436133972501451025 10917210327100479376088269)
                  ·
                    refine ⟨4093953872662679766033101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10917210327100479376088269 4093953872662679766033101)
                    ·
                      refine ⟨1535232702248504912262413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4093953872662679766033101 1535232702248504912262413)
                      ·
                        rfl

theorem cell23_2989855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_2989855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989855 prefixEnd_2989855 := by exact prefixLift 2989855
  have htrace : WordTrace (prefixWord ++ tailWord_2989855) baseStart_2989855 baseEnd_2989855 := by
    simpa [prefixWord, tailWord_2989855, baseEnd_2989855] using wordTrace_append hprefix tailTrace_2989855
  have hstable : (prefixWord ++ tailWord_2989855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989855).length < 2 ^ (prefixWord ++ tailWord_2989855).sum := by decide
  have hdescent : baseEnd_2989855 < baseStart_2989855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989856 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 2, 2, 2]
def baseStart_2989856 : Nat := 118140960795 + 2989856 * 2 ^ 59
def prefixEnd_2989856 : Nat := 4983230072969 + 3 ^ 40 * 2989856 * 2
def baseEnd_2989856 : Nat := 1535233215729159408349909

theorem tailTrace_2989856 : CollatzResearch.WordTrace tailWord_2989856 prefixEnd_2989856 1535233215729159408349909 := by
  unfold tailWord_2989856
  simp only [CollatzResearch.WordTrace]
  refine ⟨54524503528134906798418711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72699338037513209064558281 54524503528134906798418711)
  ·
    refine ⟨81786755292202360197628067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54524503528134906798418711 81786755292202360197628067)
    ·
      refine ⟨122680132938303540296442101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81786755292202360197628067 122680132938303540296442101)
      ·
        refine ⟨11501262462965956902791447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122680132938303540296442101 11501262462965956902791447)
        ·
          refine ⟨17251893694448935354187171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11501262462965956902791447 17251893694448935354187171)
          ·
            refine ⟨25877840541673403031280757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17251893694448935354187171 25877840541673403031280757)
            ·
              refine ⟨2426047550781881534182571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25877840541673403031280757 2426047550781881534182571)
              ·
                refine ⟨3639071326172822301273857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426047550781881534182571 3639071326172822301273857)
                ·
                  refine ⟨2729303494629616725955393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3639071326172822301273857 2729303494629616725955393)
                  ·
                    refine ⟨2046977620972212544466545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2729303494629616725955393 2046977620972212544466545)
                    ·
                      refine ⟨1535233215729159408349909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2046977620972212544466545 1535233215729159408349909)
                      ·
                        rfl

theorem cell23_2989856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_2989856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989856 prefixEnd_2989856 := by exact prefixLift 2989856
  have htrace : WordTrace (prefixWord ++ tailWord_2989856) baseStart_2989856 baseEnd_2989856 := by
    simpa [prefixWord, tailWord_2989856, baseEnd_2989856] using wordTrace_append hprefix tailTrace_2989856
  have hstable : (prefixWord ++ tailWord_2989856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989856).length < 2 ^ (prefixWord ++ tailWord_2989856).sum := by decide
  have hdescent : baseEnd_2989856 < baseStart_2989856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989895 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_2989895 : Nat := 118140960795 + 2989895 * 2 ^ 59
def prefixEnd_2989895 : Nat := 4983230072969 + 3 ^ 40 * 2989895 * 2
def baseEnd_2989895 : Nat := 1535253241474684755762229

theorem tailTrace_2989895 : CollatzResearch.WordTrace tailWord_2989895 prefixEnd_2989895 1535253241474684755762229 := by
  unfold tailWord_2989895
  simp only [CollatzResearch.WordTrace]
  refine ⟨109050429503128523257507139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72700286335419015505004759 109050429503128523257507139)
  ·
    refine ⟨163575644254692784886260709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109050429503128523257507139 163575644254692784886260709)
    ·
      refine ⟨30670433297754897166173883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163575644254692784886260709 30670433297754897166173883)
      ·
        refine ⟨46005649946632345749260825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30670433297754897166173883 46005649946632345749260825)
        ·
          refine ⟨34504237459974259311945619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46005649946632345749260825 34504237459974259311945619)
          ·
            refine ⟨51756356189961388967918429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34504237459974259311945619 51756356189961388967918429)
            ·
              refine ⟨19408633571235520862969411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51756356189961388967918429 19408633571235520862969411)
              ·
                refine ⟨29112950356853281294454117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19408633571235520862969411 29112950356853281294454117)
                ·
                  refine ⟨5458678191909990242710147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29112950356853281294454117 5458678191909990242710147)
                  ·
                    refine ⟨8188017287864985364065221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5458678191909990242710147 8188017287864985364065221)
                    ·
                      refine ⟨1535253241474684755762229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8188017287864985364065221 1535253241474684755762229)
                      ·
                        rfl

theorem cell23_2989895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_2989895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989895 prefixEnd_2989895 := by exact prefixLift 2989895
  have htrace : WordTrace (prefixWord ++ tailWord_2989895) baseStart_2989895 baseEnd_2989895 := by
    simpa [prefixWord, tailWord_2989895, baseEnd_2989895] using wordTrace_append hprefix tailTrace_2989895
  have hstable : (prefixWord ++ tailWord_2989895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989895).length < 2 ^ (prefixWord ++ tailWord_2989895).sum := by decide
  have hdescent : baseEnd_2989895 < baseStart_2989895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989932 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_2989932 : Nat := 118140960795 + 2989932 * 2 ^ 59
def prefixEnd_2989932 : Nat := 4983230072969 + 3 ^ 40 * 2989932 * 2
def baseEnd_2989932 : Nat := 1535272240258901110999559

theorem tailTrace_2989932 : CollatzResearch.WordTrace tailWord_2989932 prefixEnd_2989932 1535272240258901110999559 := by
  unfold tailWord_2989932
  simp only [CollatzResearch.WordTrace]
  refine ⟨54525889501997239288302025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72701186002662985717736033 54525889501997239288302025)
  ·
    refine ⟨40894417126497929466226519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54525889501997239288302025 40894417126497929466226519)
    ·
      refine ⟨61341625689746894199339779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40894417126497929466226519 61341625689746894199339779)
      ·
        refine ⟨92012438534620341299009669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61341625689746894199339779 92012438534620341299009669)
        ·
          refine ⟨17252332225241313993564313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92012438534620341299009669 17252332225241313993564313)
          ·
            refine ⟨12939249168930985495173235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17252332225241313993564313 12939249168930985495173235)
            ·
              refine ⟨19408873753396478242759853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12939249168930985495173235 19408873753396478242759853)
              ·
                refine ⟨7278327657523679341034945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19408873753396478242759853 7278327657523679341034945)
                ·
                  refine ⟨5458745743142759505776209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7278327657523679341034945 5458745743142759505776209)
                  ·
                    refine ⟨4094059307357069629332157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5458745743142759505776209 4094059307357069629332157)
                    ·
                      refine ⟨1535272240258901110999559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4094059307357069629332157 1535272240258901110999559)
                      ·
                        rfl

theorem cell23_2989932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_2989932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989932 prefixEnd_2989932 := by exact prefixLift 2989932
  have htrace : WordTrace (prefixWord ++ tailWord_2989932) baseStart_2989932 baseEnd_2989932 := by
    simpa [prefixWord, tailWord_2989932, baseEnd_2989932] using wordTrace_append hprefix tailTrace_2989932
  have hstable : (prefixWord ++ tailWord_2989932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989932).length < 2 ^ (prefixWord ++ tailWord_2989932).sum := by decide
  have hdescent : baseEnd_2989932 < baseStart_2989932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989956 : List Nat := [2, 3, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_2989956 : Nat := 118140960795 + 2989956 * 2 ^ 59
def prefixEnd_2989956 : Nat := 4983230072969 + 3 ^ 40 * 2989956 * 2
def baseEnd_2989956 : Nat := 511761521264869672366483

theorem tailTrace_2989956 : CollatzResearch.WordTrace tailWord_2989956 prefixEnd_2989956 511761521264869672366483 := by
  unfold tailWord_2989956
  simp only [CollatzResearch.WordTrace]
  refine ⟨54526327177953765337738861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72701769570605020450318481 54526327177953765337738861)
  ·
    refine ⟨20447372691732662001652073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54526327177953765337738861 20447372691732662001652073)
    ·
      refine ⟨15335529518799496501239055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20447372691732662001652073 15335529518799496501239055)
      ·
        refine ⟨23003294278199244751858583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15335529518799496501239055 23003294278199244751858583)
        ·
          refine ⟨34504941417298867127787875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23003294278199244751858583 34504941417298867127787875)
          ·
            refine ⟨51757412125948300691681813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34504941417298867127787875 51757412125948300691681813)
            ·
              refine ⟨2426128693403826594922585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51757412125948300691681813 2426128693403826594922585)
              ·
                refine ⟨1819596520052869946191939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426128693403826594922585 1819596520052869946191939)
                ·
                  refine ⟨2729394780079304919287909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819596520052869946191939 2729394780079304919287909)
                  ·
                    refine ⟨511761521264869672366483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729394780079304919287909 511761521264869672366483)
                    ·
                      rfl

theorem cell23_2989956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_2989956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2989956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2989956 prefixEnd_2989956 := by exact prefixLift 2989956
  have htrace : WordTrace (prefixWord ++ tailWord_2989956) baseStart_2989956 baseEnd_2989956 := by
    simpa [prefixWord, tailWord_2989956, baseEnd_2989956] using wordTrace_append hprefix tailTrace_2989956
  have hstable : (prefixWord ++ tailWord_2989956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989956).length < 2 ^ (prefixWord ++ tailWord_2989956).sum := by decide
  have hdescent : baseEnd_2989956 < baseStart_2989956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990002 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_2990002 : Nat := 118140960795 + 2990002 * 2 ^ 59
def prefixEnd_2990002 : Nat := 4983230072969 + 3 ^ 40 * 2990002 * 2
def baseEnd_2990002 : Nat := 1535308183904715837124237

theorem tailTrace_2990002 : CollatzResearch.WordTrace tailWord_2990002 prefixEnd_2990002 1535308183904715837124237 := by
  unfold tailWord_2990002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27263583028435220132913065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72702888075827253687768173 27263583028435220132913065)
  ·
    refine ⟨20447687271326415099684799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27263583028435220132913065 20447687271326415099684799)
    ·
      refine ⟨30671530906989622649527199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20447687271326415099684799 30671530906989622649527199)
      ·
        refine ⟨46007296360484433974290799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30671530906989622649527199 46007296360484433974290799)
        ·
          refine ⟨69010944540726650961436199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46007296360484433974290799 69010944540726650961436199)
          ·
            refine ⟨103516416811089976442154299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69010944540726650961436199 103516416811089976442154299)
            ·
              refine ⟨155274625216634964663231449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103516416811089976442154299 155274625216634964663231449)
              ·
                refine ⟨116455968912476223497423587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155274625216634964663231449 116455968912476223497423587)
                ·
                  refine ⟨174683953368714335246135381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116455968912476223497423587 174683953368714335246135381)
                  ·
                    refine ⟨2047077578539621116165649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 174683953368714335246135381 2047077578539621116165649)
                    ·
                      refine ⟨1535308183904715837124237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047077578539621116165649 1535308183904715837124237)
                      ·
                        rfl

theorem cell23_2990002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_2990002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990002 prefixEnd_2990002 := by exact prefixLift 2990002
  have htrace : WordTrace (prefixWord ++ tailWord_2990002) baseStart_2990002 baseEnd_2990002 := by
    simpa [prefixWord, tailWord_2990002, baseEnd_2990002] using wordTrace_append hprefix tailTrace_2990002
  have hstable : (prefixWord ++ tailWord_2990002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990002).length < 2 ^ (prefixWord ++ tailWord_2990002).sum := by decide
  have hdescent : baseEnd_2990002 < baseStart_2990002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990015 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_2990015 : Nat := 118140960795 + 2990015 * 2 ^ 59
def prefixEnd_2990015 : Nat := 4983230072969 + 3 ^ 40 * 2990015 * 2
def baseEnd_2990015 : Nat := 1535314859153224286261677

theorem tailTrace_2990015 : CollatzResearch.WordTrace tailWord_2990015 prefixEnd_2990015 1535314859153224286261677 := by
  unfold tailWord_2990015
  simp only [CollatzResearch.WordTrace]
  refine ⟨109054806262693783751875499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72703204175129189167916999 109054806262693783751875499)
  ·
    refine ⟨163582209394040675627813249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109054806262693783751875499 163582209394040675627813249)
    ·
      refine ⟨122686657045530506720859937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163582209394040675627813249 122686657045530506720859937)
      ·
        refine ⟨92014992784147880040644953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122686657045530506720859937 92014992784147880040644953)
        ·
          refine ⟨69011244588110910030483715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92014992784147880040644953 69011244588110910030483715)
          ·
            refine ⟨103516866882166365045725573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69011244588110910030483715 103516866882166365045725573)
            ·
              refine ⟨19409412540406193446073545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103516866882166365045725573 19409412540406193446073545)
              ·
                refine ⟨14557059405304645084555159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19409412540406193446073545 14557059405304645084555159)
                ·
                  refine ⟨21835589107956967626832739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14557059405304645084555159 21835589107956967626832739)
                  ·
                    refine ⟨32753383661935451440249109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21835589107956967626832739 32753383661935451440249109)
                    ·
                      refine ⟨1535314859153224286261677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32753383661935451440249109 1535314859153224286261677)
                      ·
                        rfl

theorem cell23_2990015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_2990015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990015 prefixEnd_2990015 := by exact prefixLift 2990015
  have htrace : WordTrace (prefixWord ++ tailWord_2990015) baseStart_2990015 baseEnd_2990015 := by
    simpa [prefixWord, tailWord_2990015, baseEnd_2990015] using wordTrace_append hprefix tailTrace_2990015
  have hstable : (prefixWord ++ tailWord_2990015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990015).length < 2 ^ (prefixWord ++ tailWord_2990015).sum := by decide
  have hdescent : baseEnd_2990015 < baseStart_2990015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990032 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 4]
def baseStart_2990032 : Nat := 118140960795 + 2990032 * 2 ^ 59
def prefixEnd_2990032 : Nat := 4983230072969 + 3 ^ 40 * 2990032 * 2
def baseEnd_2990032 : Nat := 1535323588324350719749099

theorem tailTrace_2990032 : CollatzResearch.WordTrace tailWord_2990032 prefixEnd_2990032 1535323588324350719749099 := by
  unfold tailWord_2990032
  simp only [CollatzResearch.WordTrace]
  refine ⟨54527713151816097827622175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72703617535754797103496233 54527713151816097827622175)
  ·
    refine ⟨81791569727724146741433263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54527713151816097827622175 81791569727724146741433263)
    ·
      refine ⟨122687354591586220112149895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81791569727724146741433263 122687354591586220112149895)
      ·
        refine ⟨184031031887379330168224843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122687354591586220112149895 184031031887379330168224843)
        ·
          refine ⟨276046547831068995252337265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184031031887379330168224843 276046547831068995252337265)
          ·
            refine ⟨207034910873301746439252949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276046547831068995252337265 207034910873301746439252949)
            ·
              refine ⟨4852380723593009682169991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 207034910873301746439252949 4852380723593009682169991)
              ·
                refine ⟨7278571085389514523254987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852380723593009682169991 7278571085389514523254987)
                ·
                  refine ⟨10917856628084271784882481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7278571085389514523254987 10917856628084271784882481)
                  ·
                    refine ⟨8188392471063203838661861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10917856628084271784882481 8188392471063203838661861)
                    ·
                      refine ⟨1535323588324350719749099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8188392471063203838661861 1535323588324350719749099)
                      ·
                        rfl

theorem cell23_2990032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_2990032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990032 prefixEnd_2990032 := by exact prefixLift 2990032
  have htrace : WordTrace (prefixWord ++ tailWord_2990032) baseStart_2990032 baseEnd_2990032 := by
    simpa [prefixWord, tailWord_2990032, baseEnd_2990032] using wordTrace_append hprefix tailTrace_2990032
  have hstable : (prefixWord ++ tailWord_2990032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990032).length < 2 ^ (prefixWord ++ tailWord_2990032).sum := by decide
  have hdescent : baseEnd_2990032 < baseStart_2990032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990036 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_2990036 : Nat := 118140960795 + 2990036 * 2 ^ 59
def prefixEnd_2990036 : Nat := 4983230072969 + 3 ^ 40 * 2990036 * 2
def baseEnd_2990036 : Nat := 1535325642246968704099081

theorem tailTrace_2990036 : CollatzResearch.WordTrace tailWord_2990036 prefixEnd_2990036 1535325642246968704099081 := by
  unfold tailWord_2990036
  simp only [CollatzResearch.WordTrace]
  refine ⟨54527786097808852169194981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72703714797078469558926641 54527786097808852169194981)
  ·
    refine ⟨10223959893339159781724059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54527786097808852169194981 10223959893339159781724059)
    ·
      refine ⟨15335939840008739672586089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10223959893339159781724059 15335939840008739672586089)
      ·
        refine ⟨11501954880006554754439567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15335939840008739672586089 11501954880006554754439567)
        ·
          refine ⟨17252932320009832131659351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11501954880006554754439567 17252932320009832131659351)
          ·
            refine ⟨25879398480014748197489027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17252932320009832131659351 25879398480014748197489027)
            ·
              refine ⟨38819097720022122296233541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25879398480014748197489027 38819097720022122296233541)
              ·
                refine ⟨7278580822504147930543789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38819097720022122296233541 7278580822504147930543789)
                ·
                  refine ⟨2729467808439055473953921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7278580822504147930543789 2729467808439055473953921)
                  ·
                    refine ⟨2047100856329291605465441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2729467808439055473953921 2047100856329291605465441)
                    ·
                      refine ⟨1535325642246968704099081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047100856329291605465441 1535325642246968704099081)
                      ·
                        rfl

theorem cell23_2990036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_2990036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990036 prefixEnd_2990036 := by exact prefixLift 2990036
  have htrace : WordTrace (prefixWord ++ tailWord_2990036) baseStart_2990036 baseEnd_2990036 := by
    simpa [prefixWord, tailWord_2990036, baseEnd_2990036] using wordTrace_append hprefix tailTrace_2990036
  have hstable : (prefixWord ++ tailWord_2990036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990036).length < 2 ^ (prefixWord ++ tailWord_2990036).sum := by decide
  have hdescent : baseEnd_2990036 < baseStart_2990036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990039 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_2990039 : Nat := 118140960795 + 2990039 * 2 ^ 59
def prefixEnd_2990039 : Nat := 4983230072969 + 3 ^ 40 * 2990039 * 2
def baseEnd_2990039 : Nat := 1535327182688932192361567

theorem tailTrace_2990039 : CollatzResearch.WordTrace tailWord_2990039 prefixEnd_2990039 1535327182688932192361567 := by
  unfold tailWord_2990039
  simp only [CollatzResearch.WordTrace]
  refine ⟨109055681614606835850749171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72703787743071223900499447 109055681614606835850749171)
  ·
    refine ⟨163583522421910253776123757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109055681614606835850749171 163583522421910253776123757)
    ·
      refine ⟨61343820908216345166046409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163583522421910253776123757 61343820908216345166046409)
      ·
        refine ⟨46007865681162258874534807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61343820908216345166046409 46007865681162258874534807)
        ·
          refine ⟨69011798521743388311802211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46007865681162258874534807 69011798521743388311802211)
          ·
            refine ⟨103517697782615082467703317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69011798521743388311802211 103517697782615082467703317)
            ·
              refine ⟨4852392083560081990673593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103517697782615082467703317 4852392083560081990673593)
              ·
                refine ⟨3639294062670061493005195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4852392083560081990673593 3639294062670061493005195)
                ·
                  refine ⟨5458941094005092239507793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639294062670061493005195 5458941094005092239507793)
                  ·
                    refine ⟨4094205820503819179630845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5458941094005092239507793 4094205820503819179630845)
                    ·
                      refine ⟨1535327182688932192361567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4094205820503819179630845 1535327182688932192361567)
                      ·
                        rfl

theorem cell23_2990039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_2990039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990039 prefixEnd_2990039 := by exact prefixLift 2990039
  have htrace : WordTrace (prefixWord ++ tailWord_2990039) baseStart_2990039 baseEnd_2990039 := by
    simpa [prefixWord, tailWord_2990039, baseEnd_2990039] using wordTrace_append hprefix tailTrace_2990039
  have hstable : (prefixWord ++ tailWord_2990039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990039).length < 2 ^ (prefixWord ++ tailWord_2990039).sum := by decide
  have hdescent : baseEnd_2990039 < baseStart_2990039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990042 : List Nat := [3, 1, 1, 2, 5, 1, 1, 9]
def baseStart_2990042 : Nat := 118140960795 + 2990042 * 2 ^ 59
def prefixEnd_2990042 : Nat := 4983230072969 + 3 ^ 40 * 2990042 * 2
def baseEnd_2990042 : Nat := 56864026782625765949039

theorem tailTrace_2990042 : CollatzResearch.WordTrace tailWord_2990042 prefixEnd_2990042 56864026782625765949039 := by
  unfold tailWord_2990042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27263947758398991840777095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72703860689063978242072253 27263947758398991840777095)
  ·
    refine ⟨40895921637598487761165643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27263947758398991840777095 40895921637598487761165643)
    ·
      refine ⟨61343882456397731641748465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40895921637598487761165643 61343882456397731641748465)
      ·
        refine ⟨46007911842298298731311349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61343882456397731641748465 46007911842298298731311349)
        ·
          refine ⟨4313241735215465506060439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46007911842298298731311349 4313241735215465506060439)
          ·
            refine ⟨6469862602823198259090659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313241735215465506060439 6469862602823198259090659)
            ·
              refine ⟨9704793904234797388635989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6469862602823198259090659 9704793904234797388635989)
              ·
                refine ⟨56864026782625765949039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9704793904234797388635989 56864026782625765949039)
                ·
                  rfl

theorem cell23_2990042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 9].length) (baseStart_2990042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990042 prefixEnd_2990042 := by exact prefixLift 2990042
  have htrace : WordTrace (prefixWord ++ tailWord_2990042) baseStart_2990042 baseEnd_2990042 := by
    simpa [prefixWord, tailWord_2990042, baseEnd_2990042] using wordTrace_append hprefix tailTrace_2990042
  have hstable : (prefixWord ++ tailWord_2990042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990042).length < 2 ^ (prefixWord ++ tailWord_2990042).sum := by decide
  have hdescent : baseEnd_2990042 < baseStart_2990042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990052 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_2990052 : Nat := 118140960795 + 2990052 * 2 ^ 59
def prefixEnd_2990052 : Nat := 4983230072969 + 3 ^ 40 * 2990052 * 2
def baseEnd_2990052 : Nat := 1535333857937440641499007

theorem tailTrace_2990052 : CollatzResearch.WordTrace tailWord_2990052 prefixEnd_2990052 1535333857937440641499007 := by
  unfold tailWord_2990052
  simp only [CollatzResearch.WordTrace]
  refine ⟨54528077881779869535486205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72704103842373159380648273 54528077881779869535486205)
  ·
    refine ⟨20448029205667451075807327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54528077881779869535486205 20448029205667451075807327)
    ·
      refine ⟨30672043808501176613710991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20448029205667451075807327 30672043808501176613710991)
      ·
        refine ⟨46008065712751764920566487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30672043808501176613710991 46008065712751764920566487)
        ·
          refine ⟨69012098569127647380849731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46008065712751764920566487 69012098569127647380849731)
          ·
            refine ⟨103518147853691471071274597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69012098569127647380849731 103518147853691471071274597)
            ·
              refine ⟨19409652722567150825863987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103518147853691471071274597 19409652722567150825863987)
              ·
                refine ⟨29114479083850726238795981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19409652722567150825863987 29114479083850726238795981)
                ·
                  refine ⟨10917929656444022339548493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29114479083850726238795981 10917929656444022339548493)
                  ·
                    refine ⟨4094223621166508377330685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10917929656444022339548493 4094223621166508377330685)
                    ·
                      refine ⟨1535333857937440641499007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4094223621166508377330685 1535333857937440641499007)
                      ·
                        rfl

theorem cell23_2990052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_2990052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990052 prefixEnd_2990052 := by exact prefixLift 2990052
  have htrace : WordTrace (prefixWord ++ tailWord_2990052) baseStart_2990052 baseEnd_2990052 := by
    simpa [prefixWord, tailWord_2990052, baseEnd_2990052] using wordTrace_append hprefix tailTrace_2990052
  have hstable : (prefixWord ++ tailWord_2990052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990052).length < 2 ^ (prefixWord ++ tailWord_2990052).sum := by decide
  have hdescent : baseEnd_2990052 < baseStart_2990052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990070 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_2990070 : Nat := 118140960795 + 2990070 * 2 ^ 59
def prefixEnd_2990070 : Nat := 4983230072969 + 3 ^ 40 * 2990070 * 2
def baseEnd_2990070 : Nat := 1535343100589221571073925

theorem tailTrace_2990070 : CollatzResearch.WordTrace tailWord_2990070 prefixEnd_2990070 1535343100589221571073925 := by
  unfold tailWord_2990070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816050767343408009070479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72704541518329685430085109 6816050767343408009070479)
  ·
    refine ⟨10224076151015112013605719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6816050767343408009070479 10224076151015112013605719)
    ·
      refine ⟨15336114226522668020408579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10224076151015112013605719 15336114226522668020408579)
      ·
        refine ⟨23004171339784002030612869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15336114226522668020408579 23004171339784002030612869)
        ·
          refine ⟨4313282126209500380739913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23004171339784002030612869 4313282126209500380739913)
          ·
            refine ⟨3234961594657125285554935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4313282126209500380739913 3234961594657125285554935)
            ·
              refine ⟨4852442391985687928332403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234961594657125285554935 4852442391985687928332403)
              ·
                refine ⟨7278663587978531892498605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852442391985687928332403 7278663587978531892498605)
                ·
                  refine ⟨2729498845491949459686977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7278663587978531892498605 2729498845491949459686977)
                  ·
                    refine ⟨2047124134118962094765233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2729498845491949459686977 2047124134118962094765233)
                    ·
                      refine ⟨1535343100589221571073925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047124134118962094765233 1535343100589221571073925)
                      ·
                        rfl

theorem cell23_2990070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_2990070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990070 prefixEnd_2990070 := by exact prefixLift 2990070
  have htrace : WordTrace (prefixWord ++ tailWord_2990070) baseStart_2990070 baseEnd_2990070 := by
    simpa [prefixWord, tailWord_2990070, baseEnd_2990070] using wordTrace_append hprefix tailTrace_2990070
  have hstable : (prefixWord ++ tailWord_2990070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990070).length < 2 ^ (prefixWord ++ tailWord_2990070).sum := by decide
  have hdescent : baseEnd_2990070 < baseStart_2990070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990120 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2990120 : Nat := 118140960795 + 2990120 * 2 ^ 59
def prefixEnd_2990120 : Nat := 4983230072969 + 3 ^ 40 * 2990120 * 2
def baseEnd_2990120 : Nat := 1535368774621946375448695

theorem tailTrace_2990120 : CollatzResearch.WordTrace tailWord_2990120 prefixEnd_2990120 1535368774621946375448695 := by
  unfold tailWord_2990120
  simp only [CollatzResearch.WordTrace]
  refine ⟨54529317963656693342223907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72705757284875591122965209 54529317963656693342223907)
  ·
    refine ⟨81793976945485040013335861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54529317963656693342223907 81793976945485040013335861)
    ·
      refine ⟨7668185338639222501250237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81793976945485040013335861 7668185338639222501250237)
      ·
        refine ⟨2875569501989708437968839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7668185338639222501250237 2875569501989708437968839)
        ·
          refine ⟨4313354252984562656953259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875569501989708437968839 4313354252984562656953259)
          ·
            refine ⟨6470031379476843985429889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313354252984562656953259 6470031379476843985429889)
            ·
              refine ⟨4852523534607632989072417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6470031379476843985429889 4852523534607632989072417)
              ·
                refine ⟨3639392650955724741804313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4852523534607632989072417 3639392650955724741804313)
                ·
                  refine ⟨2729544488216793556353235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3639392650955724741804313 2729544488216793556353235)
                  ·
                    refine ⟨4094316732325190334529853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2729544488216793556353235 4094316732325190334529853)
                    ·
                      refine ⟨1535368774621946375448695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4094316732325190334529853 1535368774621946375448695)
                      ·
                        rfl

theorem cell23_2990120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2990120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990120 prefixEnd_2990120 := by exact prefixLift 2990120
  have htrace : WordTrace (prefixWord ++ tailWord_2990120) baseStart_2990120 baseEnd_2990120 := by
    simpa [prefixWord, tailWord_2990120, baseEnd_2990120] using wordTrace_append hprefix tailTrace_2990120
  have hstable : (prefixWord ++ tailWord_2990120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990120).length < 2 ^ (prefixWord ++ tailWord_2990120).sum := by decide
  have hdescent : baseEnd_2990120 < baseStart_2990120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990236 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2990236 : Nat := 118140960795 + 2990236 * 2 ^ 59
def prefixEnd_2990236 : Nat := 4983230072969 + 3 ^ 40 * 2990236 * 2
def baseEnd_2990236 : Nat := 1535428338377867921598161

theorem tailTrace_2990236 : CollatzResearch.WordTrace tailWord_2990236 prefixEnd_2990236 1535428338377867921598161 := by
  unfold tailWord_2990236
  simp only [CollatzResearch.WordTrace]
  refine ⟨54531433397446569247835281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72708577863262092330447041 54531433397446569247835281)
  ·
    refine ⟨40898575048084926935876461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54531433397446569247835281 40898575048084926935876461)
    ·
      refine ⟨15336965643031847600953673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40898575048084926935876461 15336965643031847600953673)
      ·
        refine ⟨11502724232273885700715255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15336965643031847600953673 11502724232273885700715255)
        ·
          refine ⟨17254086348410828551072883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11502724232273885700715255 17254086348410828551072883)
          ·
            refine ⟨25881129522616242826609325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17254086348410828551072883 25881129522616242826609325)
            ·
              refine ⟨9705423570981091059978497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25881129522616242826609325 9705423570981091059978497)
              ·
                refine ⟨7279067678235818294983873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9705423570981091059978497 7279067678235818294983873)
                ·
                  refine ⟨5459300758676863721237905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7279067678235818294983873 5459300758676863721237905)
                  ·
                    refine ⟨4094475569007647790928429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5459300758676863721237905 4094475569007647790928429)
                    ·
                      refine ⟨1535428338377867921598161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4094475569007647790928429 1535428338377867921598161)
                      ·
                        rfl

theorem cell23_2990236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2990236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990236 prefixEnd_2990236 := by exact prefixLift 2990236
  have htrace : WordTrace (prefixWord ++ tailWord_2990236) baseStart_2990236 baseEnd_2990236 := by
    simpa [prefixWord, tailWord_2990236, baseEnd_2990236] using wordTrace_append hprefix tailTrace_2990236
  have hstable : (prefixWord ++ tailWord_2990236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990236).length < 2 ^ (prefixWord ++ tailWord_2990236).sum := by decide
  have hdescent : baseEnd_2990236 < baseStart_2990236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990239 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 8]
def baseStart_2990239 : Nat := 118140960795 + 2990239 * 2 ^ 59
def prefixEnd_2990239 : Nat := 4983230072969 + 3 ^ 40 * 2990239 * 2
def baseEnd_2990239 : Nat := 170603319868870156651183

theorem tailTrace_2990239 : CollatzResearch.WordTrace tailWord_2990239 prefixEnd_2990239 170603319868870156651183 := by
  unfold tailWord_2990239
  simp only [CollatzResearch.WordTrace]
  refine ⟨109062976213882270008029771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72708650809254846672019847 109062976213882270008029771)
  ·
    refine ⟨163594464320823405012044657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109062976213882270008029771 163594464320823405012044657)
    ·
      refine ⟨122695848240617553759033493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163594464320823405012044657 122695848240617553759033493)
      ·
        refine ⟨5751367886278947832454695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122695848240617553759033493 5751367886278947832454695)
        ·
          refine ⟨8627051829418421748682043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5751367886278947832454695 8627051829418421748682043)
          ·
            refine ⟨12940577744127632623023065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8627051829418421748682043 12940577744127632623023065)
            ·
              refine ⟨9705433308095724467267299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12940577744127632623023065 9705433308095724467267299)
              ·
                refine ⟨14558149962143586700900949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9705433308095724467267299 14558149962143586700900949)
                ·
                  refine ⟨170603319868870156651183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14558149962143586700900949 170603319868870156651183)
                  ·
                    rfl

theorem cell23_2990239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 8].length) (baseStart_2990239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990239 prefixEnd_2990239 := by exact prefixLift 2990239
  have htrace : WordTrace (prefixWord ++ tailWord_2990239) baseStart_2990239 baseEnd_2990239 := by
    simpa [prefixWord, tailWord_2990239, baseEnd_2990239] using wordTrace_append hprefix tailTrace_2990239
  have hstable : (prefixWord ++ tailWord_2990239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990239).length < 2 ^ (prefixWord ++ tailWord_2990239).sum := by decide
  have hdescent : baseEnd_2990239 < baseStart_2990239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990266 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_2990266 : Nat := 118140960795 + 2990266 * 2 ^ 59
def prefixEnd_2990266 : Nat := 4983230072969 + 3 ^ 40 * 2990266 * 2
def baseEnd_2990266 : Nat := 1535443742797502804223023

theorem tailTrace_2990266 : CollatzResearch.WordTrace tailWord_2990266 prefixEnd_2990266 1535443742797502804223023 := by
  unfold tailWord_2990266
  simp only [CollatzResearch.WordTrace]
  refine ⟨27265990246196113404815663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72709307323189635746175101 27265990246196113404815663)
  ·
    refine ⟨40898985369294170107223495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27265990246196113404815663 40898985369294170107223495)
    ·
      refine ⟨61348478053941255160835243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40898985369294170107223495 61348478053941255160835243)
      ·
        refine ⟨92022717080911882741252865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61348478053941255160835243 92022717080911882741252865)
        ·
          refine ⟨69017037810683912055939649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92022717080911882741252865 69017037810683912055939649)
          ·
            refine ⟨51762778358012934041954737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69017037810683912055939649 51762778358012934041954737)
            ·
              refine ⟨38822083768509700531466053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51762778358012934041954737 38822083768509700531466053)
              ·
                refine ⟨7279140706595568849649885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38822083768509700531466053 7279140706595568849649885)
                ·
                  refine ⟨2729677764973338318618707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7279140706595568849649885 2729677764973338318618707)
                  ·
                    refine ⟨4094516647460007477928061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2729677764973338318618707 4094516647460007477928061)
                    ·
                      refine ⟨1535443742797502804223023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4094516647460007477928061 1535443742797502804223023)
                      ·
                        rfl

theorem cell23_2990266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_2990266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990266 prefixEnd_2990266 := by exact prefixLift 2990266
  have htrace : WordTrace (prefixWord ++ tailWord_2990266) baseStart_2990266 baseEnd_2990266 := by
    simpa [prefixWord, tailWord_2990266, baseEnd_2990266] using wordTrace_append hprefix tailTrace_2990266
  have hstable : (prefixWord ++ tailWord_2990266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990266).length < 2 ^ (prefixWord ++ tailWord_2990266).sum := by decide
  have hdescent : baseEnd_2990266 < baseStart_2990266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990283 : List Nat := [1, 1, 1, 1, 3, 2, 4, 5, 1, 1, 3]
def baseStart_2990283 : Nat := 118140960795 + 2990283 * 2 ^ 59
def prefixEnd_2990283 : Nat := 4983230072969 + 3 ^ 40 * 2990283 * 2
def baseEnd_2990283 : Nat := 1535452471968629237710445

theorem tailTrace_2990283 : CollatzResearch.WordTrace tailWord_2990283 prefixEnd_2990283 1535452471968629237710445 := by
  unfold tailWord_2990283
  simp only [CollatzResearch.WordTrace]
  refine ⟨109064581025722865522631503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72709720683815243681754335 109064581025722865522631503)
  ·
    refine ⟨163596871538584298283947255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109064581025722865522631503 163596871538584298283947255)
    ·
      refine ⟨245395307307876447425920883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163596871538584298283947255 245395307307876447425920883)
      ·
        refine ⟨368092960961814671138881325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245395307307876447425920883 368092960961814671138881325)
        ·
          refine ⟨138034860360680501677080497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368092960961814671138881325 138034860360680501677080497)
          ·
            refine ⟨103526145270510376257810373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138034860360680501677080497 103526145270510376257810373)
            ·
              refine ⟨19411152238220695548339445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103526145270510376257810373 19411152238220695548339445)
              ·
                refine ⟨1819795522333190207656823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19411152238220695548339445 1819795522333190207656823)
                ·
                  refine ⟨2729693283499785311485235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819795522333190207656823 2729693283499785311485235)
                  ·
                    refine ⟨4094539925249677967227853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2729693283499785311485235 4094539925249677967227853)
                    ·
                      refine ⟨1535452471968629237710445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4094539925249677967227853 1535452471968629237710445)
                      ·
                        rfl

theorem cell23_2990283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 1, 3].length) (baseStart_2990283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990283 prefixEnd_2990283 := by exact prefixLift 2990283
  have htrace : WordTrace (prefixWord ++ tailWord_2990283) baseStart_2990283 baseEnd_2990283 := by
    simpa [prefixWord, tailWord_2990283, baseEnd_2990283] using wordTrace_append hprefix tailTrace_2990283
  have hstable : (prefixWord ++ tailWord_2990283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990283).length < 2 ^ (prefixWord ++ tailWord_2990283).sum := by decide
  have hdescent : baseEnd_2990283 < baseStart_2990283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990294 : List Nat := [5, 2, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_2990294 : Nat := 118140960795 + 2990294 * 2 ^ 59
def prefixEnd_2990294 : Nat := 4983230072969 + 3 ^ 40 * 2990294 * 2
def baseEnd_2990294 : Nat := 511819373418609564890965

theorem tailTrace_2990294 : CollatzResearch.WordTrace tailWord_2990294 prefixEnd_2990294 511819373418609564890965 := by
  unfold tailWord_2990294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816561389292688400080121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72709988152455342934187957 6816561389292688400080121)
  ·
    refine ⟨5112421041969516300060091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6816561389292688400080121 5112421041969516300060091)
    ·
      refine ⟨7668631562954274450090137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5112421041969516300060091 7668631562954274450090137)
      ·
        refine ⟨5751473672215705837567603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7668631562954274450090137 5751473672215705837567603)
        ·
          refine ⟨8627210508323558756351405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5751473672215705837567603 8627210508323558756351405)
          ·
            refine ⟨3235203940621334533631777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8627210508323558756351405 3235203940621334533631777)
            ·
              refine ⟨2426402955466000900223833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235203940621334533631777 2426402955466000900223833)
              ·
                refine ⟨1819802216599500675167875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426402955466000900223833 1819802216599500675167875)
                ·
                  refine ⟨2729703324899251012751813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819802216599500675167875 2729703324899251012751813)
                  ·
                    refine ⟨511819373418609564890965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729703324899251012751813 511819373418609564890965)
                    ·
                      rfl

theorem cell23_2990294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_2990294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990294 prefixEnd_2990294 := by exact prefixLift 2990294
  have htrace : WordTrace (prefixWord ++ tailWord_2990294) baseStart_2990294 baseEnd_2990294 := by
    simpa [prefixWord, tailWord_2990294, baseEnd_2990294] using wordTrace_append hprefix tailTrace_2990294
  have hstable : (prefixWord ++ tailWord_2990294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990294).length < 2 ^ (prefixWord ++ tailWord_2990294).sum := by decide
  have hdescent : baseEnd_2990294 < baseStart_2990294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990316 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_2990316 : Nat := 118140960795 + 2990316 * 2 ^ 59
def prefixEnd_2990316 : Nat := 4983230072969 + 3 ^ 40 * 2990316 * 2
def baseEnd_2990316 : Nat := 511823138943409202865931

theorem tailTrace_2990316 : CollatzResearch.WordTrace tailWord_2990316 prefixEnd_2990316 511823138943409202865931 := by
  unfold tailWord_2990316
  simp only [CollatzResearch.WordTrace]
  refine ⟨54532892317301656079291401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72710523089735541439055201 54532892317301656079291401)
  ·
    refine ⟨40899669237976242059468551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54532892317301656079291401 40899669237976242059468551)
    ·
      refine ⟨61349503856964363089202827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40899669237976242059468551 61349503856964363089202827)
      ·
        refine ⟨92024255785446544633804241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61349503856964363089202827 92024255785446544633804241)
        ·
          refine ⟨69018191839084908475353181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92024255785446544633804241 69018191839084908475353181)
          ·
            refine ⟨25881821939656840678257443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69018191839084908475353181 25881821939656840678257443)
            ·
              refine ⟨38822732909485261017386165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25881821939656840678257443 38822732909485261017386165)
              ·
                refine ⟨3639631210264243220379953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38822732909485261017386165 3639631210264243220379953)
                ·
                  refine ⟨2729723407698182415284965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3639631210264243220379953 2729723407698182415284965)
                  ·
                    refine ⟨511823138943409202865931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729723407698182415284965 511823138943409202865931)
                    ·
                      rfl

theorem cell23_2990316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_2990316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990316 prefixEnd_2990316 := by exact prefixLift 2990316
  have htrace : WordTrace (prefixWord ++ tailWord_2990316) baseStart_2990316 baseEnd_2990316 := by
    simpa [prefixWord, tailWord_2990316, baseEnd_2990316] using wordTrace_append hprefix tailTrace_2990316
  have hstable : (prefixWord ++ tailWord_2990316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990316).length < 2 ^ (prefixWord ++ tailWord_2990316).sum := by decide
  have hdescent : baseEnd_2990316 < baseStart_2990316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990323 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 3, 2, 2]
def baseStart_2990323 : Nat := 118140960795 + 2990323 * 2 ^ 59
def prefixEnd_2990323 : Nat := 4983230072969 + 3 ^ 40 * 2990323 * 2
def baseEnd_2990323 : Nat := 1535473011194809081210261

theorem tailTrace_2990323 : CollatzResearch.WordTrace tailWord_2990323 prefixEnd_2990323 1535473011194809081210261 := by
  unfold tailWord_2990323
  simp only [CollatzResearch.WordTrace]
  refine ⟨109066039945577952354087623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72710693297051968236058415 109066039945577952354087623)
  ·
    refine ⟨163599059918366928531131435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109066039945577952354087623 163599059918366928531131435)
    ·
      refine ⟨245398589877550392796697153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163599059918366928531131435 245398589877550392796697153)
      ·
        refine ⟨184048942408162794597522865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245398589877550392796697153 184048942408162794597522865)
        ·
          refine ⟨138036706806122095948142149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184048942408162794597522865 138036706806122095948142149)
          ·
            refine ⟨25881882526147892990276653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138036706806122095948142149 25881882526147892990276653)
            ·
              refine ⟨9705705947305459871353745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25881882526147892990276653 9705705947305459871353745)
              ·
                refine ⟨7279279460479094903515309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9705705947305459871353745 7279279460479094903515309)
                ·
                  refine ⟨2729729797679660588818241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7279279460479094903515309 2729729797679660588818241)
                  ·
                    refine ⟨2047297348259745441613681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2729729797679660588818241 2047297348259745441613681)
                    ·
                      refine ⟨1535473011194809081210261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047297348259745441613681 1535473011194809081210261)
                      ·
                        rfl

theorem cell23_2990323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 2, 2].length) (baseStart_2990323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990323 prefixEnd_2990323 := by exact prefixLift 2990323
  have htrace : WordTrace (prefixWord ++ tailWord_2990323) baseStart_2990323 baseEnd_2990323 := by
    simpa [prefixWord, tailWord_2990323, baseEnd_2990323] using wordTrace_append hprefix tailTrace_2990323
  have hstable : (prefixWord ++ tailWord_2990323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990323).length < 2 ^ (prefixWord ++ tailWord_2990323).sum := by decide
  have hdescent : baseEnd_2990323 < baseStart_2990323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990383 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 1, 3, 2]
def baseStart_2990383 : Nat := 118140960795 + 2990383 * 2 ^ 59
def prefixEnd_2990383 : Nat := 4983230072969 + 3 ^ 40 * 2990383 * 2
def baseEnd_2990383 : Nat := 1535503820034078846459985

theorem tailTrace_2990383 : CollatzResearch.WordTrace tailWord_2990383 prefixEnd_2990383 1535503820034078846459985 := by
  unfold tailWord_2990383
  simp only [CollatzResearch.WordTrace]
  refine ⟨109068228325360582601271803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72712152216907055067514535 109068228325360582601271803)
  ·
    refine ⟨163602342488040873901907705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109068228325360582601271803 163602342488040873901907705)
    ·
      refine ⟨122701756866030655426430779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163602342488040873901907705 122701756866030655426430779)
      ·
        refine ⟨184052635299045983139646169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122701756866030655426430779 184052635299045983139646169)
        ·
          refine ⟨138039476474284487354734627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184052635299045983139646169 138039476474284487354734627)
          ·
            refine ⟨207059214711426731032101941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138039476474284487354734627 207059214711426731032101941)
            ·
              refine ⟨19411801379196256034259557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207059214711426731032101941 19411801379196256034259557)
              ·
                refine ⟨3639712758599298006423667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19411801379196256034259557 3639712758599298006423667)
                ·
                  refine ⟨5459569137898947009635501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639712758599298006423667 5459569137898947009635501)
                  ·
                    refine ⟨2047338426712105128613313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5459569137898947009635501 2047338426712105128613313)
                    ·
                      refine ⟨1535503820034078846459985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047338426712105128613313 1535503820034078846459985)
                      ·
                        rfl

theorem cell23_2990383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 3, 2].length) (baseStart_2990383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990383 prefixEnd_2990383 := by exact prefixLift 2990383
  have htrace : WordTrace (prefixWord ++ tailWord_2990383) baseStart_2990383 baseEnd_2990383 := by
    simpa [prefixWord, tailWord_2990383, baseEnd_2990383] using wordTrace_append hprefix tailTrace_2990383
  have hstable : (prefixWord ++ tailWord_2990383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990383).length < 2 ^ (prefixWord ++ tailWord_2990383).sum := by decide
  have hdescent : baseEnd_2990383 < baseStart_2990383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990419 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 7]
def baseStart_2990419 : Nat := 118140960795 + 2990419 * 2 ^ 59
def prefixEnd_2990419 : Nat := 4983230072969 + 3 ^ 40 * 2990419 * 2
def baseEnd_2990419 : Nat := 170613589481960078401091

theorem tailTrace_2990419 : CollatzResearch.WordTrace tailWord_2990419 prefixEnd_2990419 170613589481960078401091 := by
  unfold tailWord_2990419
  simp only [CollatzResearch.WordTrace]
  refine ⟨109069541353230160749582311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72713027568820107166388207 109069541353230160749582311)
  ·
    refine ⟨163604312029845241124373467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109069541353230160749582311 163604312029845241124373467)
    ·
      refine ⟨245406468044767861686560201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163604312029845241124373467 245406468044767861686560201)
      ·
        refine ⟨184054851033575896264920151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245406468044767861686560201 184054851033575896264920151)
        ·
          refine ⟨276082276550363844397380227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184054851033575896264920151 276082276550363844397380227)
          ·
            refine ⟨414123414825545766596070341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276082276550363844397380227 414123414825545766596070341)
            ·
              refine ⟨77648140279789831236763189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 414123414825545766596070341 77648140279789831236763189)
              ·
                refine ⟨7279513151230296678446549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77648140279789831236763189 7279513151230296678446549)
                ·
                  refine ⟨170613589481960078401091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7279513151230296678446549 170613589481960078401091)
                  ·
                    rfl

theorem cell23_2990419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 7].length) (baseStart_2990419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990419 prefixEnd_2990419 := by exact prefixLift 2990419
  have htrace : WordTrace (prefixWord ++ tailWord_2990419) baseStart_2990419 baseEnd_2990419 := by
    simpa [prefixWord, tailWord_2990419, baseEnd_2990419] using wordTrace_append hprefix tailTrace_2990419
  have hstable : (prefixWord ++ tailWord_2990419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990419).length < 2 ^ (prefixWord ++ tailWord_2990419).sum := by decide
  have hdescent : baseEnd_2990419 < baseStart_2990419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990473 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 2, 5, 2]
def baseStart_2990473 : Nat := 118140960795 + 2990473 * 2 ^ 59
def prefixEnd_2990473 : Nat := 4983230072969 + 3 ^ 40 * 2990473 * 2
def baseEnd_2990473 : Nat := 1535550033292983494334571

theorem tailTrace_2990473 : CollatzResearch.WordTrace tailWord_2990473 prefixEnd_2990473 1535550033292983494334571 := by
  unfold tailWord_2990473
  simp only [CollatzResearch.WordTrace]
  refine ⟨109071510895034527972048073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72714340596689685314698715 109071510895034527972048073)
  ·
    refine ⟨81803633171275895979036055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109071510895034527972048073 81803633171275895979036055)
    ·
      refine ⟨122705449756913843968554083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81803633171275895979036055 122705449756913843968554083)
      ·
        refine ⟨184058174635370765952831125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122705449756913843968554083 184058174635370765952831125)
        ·
          refine ⟨8627726936033004654038959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184058174635370765952831125 8627726936033004654038959)
          ·
            refine ⟨12941590404049506981058439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8627726936033004654038959 12941590404049506981058439)
            ·
              refine ⟨19412385606074260471587659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12941590404049506981058439 19412385606074260471587659)
              ·
                refine ⟨29118578409111390707381489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19412385606074260471587659 29118578409111390707381489)
                ·
                  refine ⟨21838933806833543030536117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29118578409111390707381489 21838933806833543030536117)
                  ·
                    refine ⟨2047400044390644659112761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21838933806833543030536117 2047400044390644659112761)
                    ·
                      refine ⟨1535550033292983494334571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047400044390644659112761 1535550033292983494334571)
                      ·
                        rfl

theorem cell23_2990473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 5, 2].length) (baseStart_2990473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990473 prefixEnd_2990473 := by exact prefixLift 2990473
  have htrace : WordTrace (prefixWord ++ tailWord_2990473) baseStart_2990473 baseEnd_2990473 := by
    simpa [prefixWord, tailWord_2990473, baseEnd_2990473] using wordTrace_append hprefix tailTrace_2990473
  have hstable : (prefixWord ++ tailWord_2990473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990473).length < 2 ^ (prefixWord ++ tailWord_2990473).sum := by decide
  have hdescent : baseEnd_2990473 < baseStart_2990473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990476 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2990476 : Nat := 118140960795 + 2990476 * 2 ^ 59
def prefixEnd_2990476 : Nat := 4983230072969 + 3 ^ 40 * 2990476 * 2
def baseEnd_2990476 : Nat := 1535551573734946982597057

theorem tailTrace_2990476 : CollatzResearch.WordTrace tailWord_2990476 prefixEnd_2990476 1535551573734946982597057 := by
  unfold tailWord_2990476
  simp only [CollatzResearch.WordTrace]
  refine ⟨54535810157011829742203641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72714413542682439656271521 54535810157011829742203641)
  ·
    refine ⟨40901857617758872306652731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54535810157011829742203641 40901857617758872306652731)
    ·
      refine ⟨61352786426638308459979097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40901857617758872306652731 61352786426638308459979097)
      ·
        refine ⟨46014589819978731344984323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61352786426638308459979097 46014589819978731344984323)
        ·
          refine ⟨69021884729968097017476485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46014589819978731344984323 69021884729968097017476485)
          ·
            refine ⟨12941603386869018190776841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69021884729968097017476485 12941603386869018190776841)
            ·
              refine ⟨9706202540151763643082631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12941603386869018190776841 9706202540151763643082631)
              ·
                refine ⟨14559303810227645464623947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9706202540151763643082631 14559303810227645464623947)
                ·
                  refine ⟨21838955715341468196935921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14559303810227645464623947 21838955715341468196935921)
                  ·
                    refine ⟨16379216786506101147701941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21838955715341468196935921 16379216786506101147701941)
                    ·
                      refine ⟨1535551573734946982597057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16379216786506101147701941 1535551573734946982597057)
                      ·
                        rfl

theorem cell23_2990476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2990476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990476 prefixEnd_2990476 := by exact prefixLift 2990476
  have htrace : WordTrace (prefixWord ++ tailWord_2990476) baseStart_2990476 baseEnd_2990476 := by
    simpa [prefixWord, tailWord_2990476, baseEnd_2990476] using wordTrace_append hprefix tailTrace_2990476
  have hstable : (prefixWord ++ tailWord_2990476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990476).length < 2 ^ (prefixWord ++ tailWord_2990476).sum := by decide
  have hdescent : baseEnd_2990476 < baseStart_2990476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990503 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2990503 : Nat := 118140960795 + 2990503 * 2 ^ 59
def prefixEnd_2990503 : Nat := 4983230072969 + 3 ^ 40 * 2990503 * 2
def baseEnd_2990503 : Nat := 1535565437712618376959433

theorem tailTrace_2990503 : CollatzResearch.WordTrace tailWord_2990503 prefixEnd_2990503 1535565437712618376959433 := by
  unfold tailWord_2990503
  simp only [CollatzResearch.WordTrace]
  refine ⟨109072605084925843095640163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72715070056617228730426775 109072605084925843095640163)
  ·
    refine ⟨163608907627388764643460245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109072605084925843095640163 163608907627388764643460245)
    ·
      refine ⟨7669167545033848342662199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163608907627388764643460245 7669167545033848342662199)
      ·
        refine ⟨11503751317550772513993299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7669167545033848342662199 11503751317550772513993299)
        ·
          refine ⟨17255626976326158770989949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11503751317550772513993299 17255626976326158770989949)
          ·
            refine ⟨6470860116122309539121231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17255626976326158770989949 6470860116122309539121231)
            ·
              refine ⟨9706290174183464308681847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6470860116122309539121231 9706290174183464308681847)
              ·
                refine ⟨14559435261275196463022771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9706290174183464308681847 14559435261275196463022771)
                ·
                  refine ⟨21839152891912794694534157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14559435261275196463022771 21839152891912794694534157)
                  ·
                    refine ⟨8189682334467298010450309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21839152891912794694534157 8189682334467298010450309)
                    ·
                      refine ⟨1535565437712618376959433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8189682334467298010450309 1535565437712618376959433)
                      ·
                        rfl

theorem cell23_2990503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2990503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990503 prefixEnd_2990503 := by exact prefixLift 2990503
  have htrace : WordTrace (prefixWord ++ tailWord_2990503) baseStart_2990503 baseEnd_2990503 := by
    simpa [prefixWord, tailWord_2990503, baseEnd_2990503] using wordTrace_append hprefix tailTrace_2990503
  have hstable : (prefixWord ++ tailWord_2990503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990503).length < 2 ^ (prefixWord ++ tailWord_2990503).sum := by decide
  have hdescent : baseEnd_2990503 < baseStart_2990503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990581 : List Nat := [1, 3, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2990581 : Nat := 118140960795 + 2990581 * 2 ^ 59
def prefixEnd_2990581 : Nat := 4983230072969 + 3 ^ 40 * 2990581 * 2
def baseEnd_2990581 : Nat := 511868496401223023928025

theorem tailTrace_2990581 : CollatzResearch.WordTrace tailWord_2990581 prefixEnd_2990581 511868496401223023928025 := by
  unfold tailWord_2990581
  simp only [CollatzResearch.WordTrace]
  refine ⟨109075449978643262416979597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72716966652428841611319731 109075449978643262416979597)
  ·
    refine ⟨40903293741991223406367349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109075449978643262416979597 40903293741991223406367349)
    ·
      refine ⟨3834683788311677194346939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40903293741991223406367349 3834683788311677194346939)
      ·
        refine ⟨5752025682467515791520409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3834683788311677194346939 5752025682467515791520409)
        ·
          refine ⟨4314019261850636843640307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5752025682467515791520409 4314019261850636843640307)
          ·
            refine ⟨6471028892775955265460461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314019261850636843640307 6471028892775955265460461)
            ·
              refine ⟨2426635834790983224547673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6471028892775955265460461 2426635834790983224547673)
              ·
                refine ⟨1819976876093237418410755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426635834790983224547673 1819976876093237418410755)
                ·
                  refine ⟨2729965314139856127616133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819976876093237418410755 2729965314139856127616133)
                  ·
                    refine ⟨511868496401223023928025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2729965314139856127616133 511868496401223023928025)
                    ·
                      rfl

theorem cell23_2990581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2990581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990581 prefixEnd_2990581 := by exact prefixLift 2990581
  have htrace : WordTrace (prefixWord ++ tailWord_2990581) baseStart_2990581 baseEnd_2990581 := by
    simpa [prefixWord, tailWord_2990581, baseEnd_2990581] using wordTrace_append hprefix tailTrace_2990581
  have hstable : (prefixWord ++ tailWord_2990581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990581).length < 2 ^ (prefixWord ++ tailWord_2990581).sum := by decide
  have hdescent : baseEnd_2990581 < baseStart_2990581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990586 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_2990586 : Nat := 118140960795 + 2990586 * 2 ^ 59
def prefixEnd_2990586 : Nat := 4983230072969 + 3 ^ 40 * 2990586 * 2
def baseEnd_2990586 : Nat := 511869352202313850740517

theorem tailTrace_2990586 : CollatzResearch.WordTrace tailWord_2990586 prefixEnd_2990586 511869352202313850740517 := by
  unfold tailWord_2990586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27268908085906287067727903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72717088229083432180607741 27268908085906287067727903)
  ·
    refine ⟨40903362128859430601591855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27268908085906287067727903 40903362128859430601591855)
    ·
      refine ⟨61355043193289145902387783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40903362128859430601591855 61355043193289145902387783)
      ·
        refine ⟨92032564789933718853581675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61355043193289145902387783 92032564789933718853581675)
        ·
          refine ⟨138048847184900578280372513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92032564789933718853581675 138048847184900578280372513)
          ·
            refine ⟨103536635388675433710279385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138048847184900578280372513 103536635388675433710279385)
            ·
              refine ⟨77652476541506575282709539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103536635388675433710279385 77652476541506575282709539)
              ·
                refine ⟨116478714812259862924064309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77652476541506575282709539 116478714812259862924064309)
                ·
                  refine ⟨10919879513649362149131029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116478714812259862924064309 10919879513649362149131029)
                  ·
                    refine ⟨511869352202313850740517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10919879513649362149131029 511869352202313850740517)
                    ·
                      rfl

theorem cell23_2990586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_2990586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990586 prefixEnd_2990586 := by exact prefixLift 2990586
  have htrace : WordTrace (prefixWord ++ tailWord_2990586) baseStart_2990586 baseEnd_2990586 := by
    simpa [prefixWord, tailWord_2990586, baseEnd_2990586] using wordTrace_append hprefix tailTrace_2990586
  have hstable : (prefixWord ++ tailWord_2990586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990586).length < 2 ^ (prefixWord ++ tailWord_2990586).sum := by decide
  have hdescent : baseEnd_2990586 < baseStart_2990586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990594 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 6]
def baseStart_2990594 : Nat := 118140960795 + 2990594 * 2 ^ 59
def prefixEnd_2990594 : Nat := 4983230072969 + 3 ^ 40 * 2990594 * 2
def baseEnd_2990594 : Nat := 170623573828019724546835

theorem tailTrace_2990594 : CollatzResearch.WordTrace tailWord_2990594 prefixEnd_2990594 170623573828019724546835 := by
  unfold tailWord_2990594
  simp only [CollatzResearch.WordTrace]
  refine ⟨27268981031899041409300709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72717282751730777091468557 27268981031899041409300709)
  ·
    refine ⟨5112933943481070264243883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27268981031899041409300709 5112933943481070264243883)
    ·
      refine ⟨7669400915221605396365825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5112933943481070264243883 7669400915221605396365825)
      ·
        refine ⟨5752050686416204047274369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7669400915221605396365825 5752050686416204047274369)
        ·
          refine ⟨4314038014812153035455777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5752050686416204047274369 4314038014812153035455777)
          ·
            refine ⟨3235528511109114776591833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4314038014812153035455777 3235528511109114776591833)
            ·
              refine ⟨2426646383331836082443875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235528511109114776591833 2426646383331836082443875)
              ·
                refine ⟨3639969574997754123665813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426646383331836082443875 3639969574997754123665813)
                ·
                  refine ⟨170623573828019724546835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3639969574997754123665813 170623573828019724546835)
                  ·
                    rfl

theorem cell23_2990594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_2990594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990594 prefixEnd_2990594 := by exact prefixLift 2990594
  have htrace : WordTrace (prefixWord ++ tailWord_2990594) baseStart_2990594 baseEnd_2990594 := by
    simpa [prefixWord, tailWord_2990594, baseEnd_2990594] using wordTrace_append hprefix tailTrace_2990594
  have hstable : (prefixWord ++ tailWord_2990594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990594).length < 2 ^ (prefixWord ++ tailWord_2990594).sum := by decide
  have hdescent : baseEnd_2990594 < baseStart_2990594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990627 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 1, 1, 4]
def baseStart_2990627 : Nat := 118140960795 + 2990627 * 2 ^ 59
def prefixEnd_2990627 : Nat := 4983230072969 + 3 ^ 40 * 2990627 * 2
def baseEnd_2990627 : Nat := 1535629109313775891808863

theorem tailTrace_2990627 : CollatzResearch.WordTrace tailWord_2990627 prefixEnd_2990627 1535629109313775891808863 := by
  unfold tailWord_2990627
  simp only [CollatzResearch.WordTrace]
  refine ⟨109077127736476612273154135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72718085157651074848769423 109077127736476612273154135)
  ·
    refine ⟨163615691604714918409731203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109077127736476612273154135 163615691604714918409731203)
    ·
      refine ⟨245423537407072377614596805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163615691604714918409731203 245423537407072377614596805)
      ·
        refine ⟨46016913263826070802736901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245423537407072377614596805 46016913263826070802736901)
        ·
          refine ⟨8628171236967388275513169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46016913263826070802736901 8628171236967388275513169)
          ·
            refine ⟨6471128427725541206634877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8628171236967388275513169 6471128427725541206634877)
            ·
              refine ⟨2426673160397077952488079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6471128427725541206634877 2426673160397077952488079)
              ·
                refine ⟨3640009740595616928732119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426673160397077952488079 3640009740595616928732119)
                ·
                  refine ⟨5460014610893425393098179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640009740595616928732119 5460014610893425393098179)
                  ·
                    refine ⟨8190021916340138089647269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5460014610893425393098179 8190021916340138089647269)
                    ·
                      refine ⟨1535629109313775891808863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8190021916340138089647269 1535629109313775891808863)
                      ·
                        rfl

theorem cell23_2990627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_2990627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990627 prefixEnd_2990627 := by exact prefixLift 2990627
  have htrace : WordTrace (prefixWord ++ tailWord_2990627) baseStart_2990627 baseEnd_2990627 := by
    simpa [prefixWord, tailWord_2990627, baseEnd_2990627] using wordTrace_append hprefix tailTrace_2990627
  have hstable : (prefixWord ++ tailWord_2990627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990627).length < 2 ^ (prefixWord ++ tailWord_2990627).sum := by decide
  have hdescent : baseEnd_2990627 < baseStart_2990627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990638 : List Nat := [4, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_2990638 : Nat := 118140960795 + 2990638 * 2 ^ 59
def prefixEnd_2990638 : Nat := 4983230072969 + 3 ^ 40 * 2990638 * 2
def baseEnd_2990638 : Nat := 1535634757600975348771313

theorem tailTrace_2990638 : CollatzResearch.WordTrace tailWord_2990638 prefixEnd_2990638 1535634757600975348771313 := by
  unfold tailWord_2990638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13634691117429595143975571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72718352626291174101203045 13634691117429595143975571)
  ·
    refine ⟨20452036676144392715963357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13634691117429595143975571 20452036676144392715963357)
    ·
      refine ⟨7669513753554147268486259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20452036676144392715963357 7669513753554147268486259)
      ·
        refine ⟨11504270630331220902729389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7669513753554147268486259 11504270630331220902729389)
        ·
          refine ⟨4314101486374207838523521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11504270630331220902729389 4314101486374207838523521)
          ·
            refine ⟨3235576114780655878892641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4314101486374207838523521 3235576114780655878892641)
            ·
              refine ⟨2426682086085491909169481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235576114780655878892641 2426682086085491909169481)
              ·
                refine ⟨1820011564564118931877111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426682086085491909169481 1820011564564118931877111)
                ·
                  refine ⟨2730017346846178397815667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820011564564118931877111 2730017346846178397815667)
                  ·
                    refine ⟨4095026020269267596723501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2730017346846178397815667 4095026020269267596723501)
                    ·
                      refine ⟨1535634757600975348771313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095026020269267596723501 1535634757600975348771313)
                      ·
                        rfl

theorem cell23_2990638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_2990638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990638 prefixEnd_2990638 := by exact prefixLift 2990638
  have htrace : WordTrace (prefixWord ++ tailWord_2990638) baseStart_2990638 baseEnd_2990638 := by
    simpa [prefixWord, tailWord_2990638, baseEnd_2990638] using wordTrace_append hprefix tailTrace_2990638
  have hstable : (prefixWord ++ tailWord_2990638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990638).length < 2 ^ (prefixWord ++ tailWord_2990638).sum := by decide
  have hdescent : baseEnd_2990638 < baseStart_2990638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990643 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 3]
def baseStart_2990643 : Nat := 118140960795 + 2990643 * 2 ^ 59
def prefixEnd_2990643 : Nat := 4983230072969 + 3 ^ 40 * 2990643 * 2
def baseEnd_2990643 : Nat := 1535637325004247829208789

theorem tailTrace_2990643 : CollatzResearch.WordTrace tailWord_2990643 prefixEnd_2990643 1535637325004247829208789 := by
  unfold tailWord_2990643
  simp only [CollatzResearch.WordTrace]
  refine ⟨109077711304418647005736583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72718474202945764670491055 109077711304418647005736583)
  ·
    refine ⟨163616566956627970508604875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109077711304418647005736583 163616566956627970508604875)
    ·
      refine ⟨245424850434941955762907313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163616566956627970508604875 245424850434941955762907313)
      ·
        refine ⟨184068637826206466822180485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245424850434941955762907313 184068637826206466822180485)
        ·
          refine ⟨34512869592413712529158841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184068637826206466822180485 34512869592413712529158841)
          ·
            refine ⟨25884652194310284396869131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34512869592413712529158841 25884652194310284396869131)
            ·
              refine ⟨38826978291465426595303697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25884652194310284396869131 38826978291465426595303697)
              ·
                refine ⟨29120233718599069946477773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38826978291465426595303697 29120233718599069946477773)
                ·
                  refine ⟨10920087644474651229929165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29120233718599069946477773 10920087644474651229929165)
                  ·
                    refine ⟨4095032866677994211223437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10920087644474651229929165 4095032866677994211223437)
                    ·
                      refine ⟨1535637325004247829208789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095032866677994211223437 1535637325004247829208789)
                      ·
                        rfl

theorem cell23_2990643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_2990643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990643 prefixEnd_2990643 := by exact prefixLift 2990643
  have htrace : WordTrace (prefixWord ++ tailWord_2990643) baseStart_2990643 baseEnd_2990643 := by
    simpa [prefixWord, tailWord_2990643, baseEnd_2990643] using wordTrace_append hprefix tailTrace_2990643
  have hstable : (prefixWord ++ tailWord_2990643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990643).length < 2 ^ (prefixWord ++ tailWord_2990643).sum := by decide
  have hdescent : baseEnd_2990643 < baseStart_2990643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990700 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 3, 4, 2]
def baseStart_2990700 : Nat := 118140960795 + 2990700 * 2 ^ 59
def prefixEnd_2990700 : Nat := 4983230072969 + 3 ^ 40 * 2990700 * 2
def baseEnd_2990700 : Nat := 1535666593401554106196027

theorem tailTrace_2990700 : CollatzResearch.WordTrace tailWord_2990700 prefixEnd_2990700 1535666593401554106196027 := by
  unfold tailWord_2990700
  simp only [CollatzResearch.WordTrace]
  refine ⟨54539895132606072870280777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72719860176808097160374369 54539895132606072870280777)
  ·
    refine ⟨40904921349454554652710583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54539895132606072870280777 40904921349454554652710583)
    ·
      refine ⟨61357382024181831979065875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40904921349454554652710583 61357382024181831979065875)
      ·
        refine ⟨92036073036272747968598813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61357382024181831979065875 92036073036272747968598813)
        ·
          refine ⟨34513527388602280488224555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92036073036272747968598813 34513527388602280488224555)
          ·
            refine ⟨51770291082903420732336833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34513527388602280488224555 51770291082903420732336833)
            ·
              refine ⟨38827718312177565549252625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51770291082903420732336833 38827718312177565549252625)
              ·
                refine ⟨29120788734133174161939469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38827718312177565549252625 29120788734133174161939469)
                ·
                  refine ⟨10920295775299940310727301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29120788734133174161939469 10920295775299940310727301)
                  ·
                    refine ⟨2047555457868738808261369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10920295775299940310727301 2047555457868738808261369)
                    ·
                      refine ⟨1535666593401554106196027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047555457868738808261369 1535666593401554106196027)
                      ·
                        rfl

theorem cell23_2990700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_2990700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990700 prefixEnd_2990700 := by exact prefixLift 2990700
  have htrace : WordTrace (prefixWord ++ tailWord_2990700) baseStart_2990700 baseEnd_2990700 := by
    simpa [prefixWord, tailWord_2990700, baseEnd_2990700] using wordTrace_append hprefix tailTrace_2990700
  have hstable : (prefixWord ++ tailWord_2990700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990700).length < 2 ^ (prefixWord ++ tailWord_2990700).sum := by decide
  have hdescent : baseEnd_2990700 < baseStart_2990700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990703 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 3]
def baseStart_2990703 : Nat := 118140960795 + 2990703 * 2 ^ 59
def prefixEnd_2990703 : Nat := 4983230072969 + 3 ^ 40 * 2990703 * 2
def baseEnd_2990703 : Nat := 1535668133843517594458513

theorem tailTrace_2990703 : CollatzResearch.WordTrace tailWord_2990703 prefixEnd_2990703 1535668133843517594458513 := by
  unfold tailWord_2990703
  simp only [CollatzResearch.WordTrace]
  refine ⟨109079899684201277252920763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72719933122800851501947175 109079899684201277252920763)
  ·
    refine ⟨163619849526301915879381145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109079899684201277252920763 163619849526301915879381145)
    ·
      refine ⟨122714887144726436909535859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163619849526301915879381145 122714887144726436909535859)
      ·
        refine ⟨184072330717089655364303789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122714887144726436909535859 184072330717089655364303789)
        ·
          refine ⟨69027124018908620761613921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184072330717089655364303789 69027124018908620761613921)
          ·
            refine ⟨51770343014181465571210441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69027124018908620761613921 51770343014181465571210441)
            ·
              refine ⟨38827757260636099178407831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51770343014181465571210441 38827757260636099178407831)
              ·
                refine ⟨58241635890954148767611747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38827757260636099178407831 58241635890954148767611747)
                ·
                  refine ⟨87362453836431223151417621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58241635890954148767611747 87362453836431223151417621)
                  ·
                    refine ⟨4095115023582713585222701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87362453836431223151417621 4095115023582713585222701)
                    ·
                      refine ⟨1535668133843517594458513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095115023582713585222701 1535668133843517594458513)
                      ·
                        rfl

theorem cell23_2990703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_2990703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990703 prefixEnd_2990703 := by exact prefixLift 2990703
  have htrace : WordTrace (prefixWord ++ tailWord_2990703) baseStart_2990703 baseEnd_2990703 := by
    simpa [prefixWord, tailWord_2990703, baseEnd_2990703] using wordTrace_append hprefix tailTrace_2990703
  have hstable : (prefixWord ++ tailWord_2990703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990703).length < 2 ^ (prefixWord ++ tailWord_2990703).sum := by decide
  have hdescent : baseEnd_2990703 < baseStart_2990703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990723 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 7]
def baseStart_2990723 : Nat := 118140960795 + 2990723 * 2 ^ 59
def prefixEnd_2990723 : Nat := 4983230072969 + 3 ^ 40 * 2990723 * 2
def baseEnd_2990723 : Nat := 170630933717400835134269

theorem tailTrace_2990723 : CollatzResearch.WordTrace tailWord_2990723 prefixEnd_2990723 170630933717400835134269 := by
  unfold tailWord_2990723
  simp only [CollatzResearch.WordTrace]
  refine ⟨109080629144128820668648823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72720419429419213779099215 109080629144128820668648823)
  ·
    refine ⟨163620943716193231002973235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109080629144128820668648823 163620943716193231002973235)
    ·
      refine ⟨245431415574289846504459853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163620943716193231002973235 245431415574289846504459853)
      ·
        refine ⟨92036780840358692439172445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245431415574289846504459853 92036780840358692439172445)
        ·
          refine ⟨34513792815134509664689667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92036780840358692439172445 34513792815134509664689667)
          ·
            refine ⟨51770689222701764497034501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34513792815134509664689667 51770689222701764497034501)
            ·
              refine ⟨9707004229256580843193969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51770689222701764497034501 9707004229256580843193969)
              ·
                refine ⟨7280253171942435632395477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9707004229256580843193969 7280253171942435632395477)
                ·
                  refine ⟨170630933717400835134269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7280253171942435632395477 170630933717400835134269)
                  ·
                    rfl

theorem cell23_2990723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 7].length) (baseStart_2990723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990723 prefixEnd_2990723 := by exact prefixLift 2990723
  have htrace : WordTrace (prefixWord ++ tailWord_2990723) baseStart_2990723 baseEnd_2990723 := by
    simpa [prefixWord, tailWord_2990723, baseEnd_2990723] using wordTrace_append hprefix tailTrace_2990723
  have hstable : (prefixWord ++ tailWord_2990723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990723).length < 2 ^ (prefixWord ++ tailWord_2990723).sum := by decide
  have hdescent : baseEnd_2990723 < baseStart_2990723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990750 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2990750 : Nat := 118140960795 + 2990750 * 2 ^ 59
def prefixEnd_2990750 : Nat := 4983230072969 + 3 ^ 40 * 2990750 * 2
def baseEnd_2990750 : Nat := 1535692267434278910570797

theorem tailTrace_2990750 : CollatzResearch.WordTrace tailWord_2990750 prefixEnd_2990750 1535692267434278910570797 := by
  unfold tailWord_2990750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13635201739378875534985213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72721075943354002853254469 13635201739378875534985213)
  ·
    refine ⟨5113200652267078325619455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13635201739378875534985213 5113200652267078325619455)
    ·
      refine ⟨7669800978400617488429183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5113200652267078325619455 7669800978400617488429183)
      ·
        refine ⟨11504701467600926232643775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7669800978400617488429183 11504701467600926232643775)
        ·
          refine ⟨17257052201401389348965663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11504701467600926232643775 17257052201401389348965663)
          ·
            refine ⟨25885578302102084023448495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17257052201401389348965663 25885578302102084023448495)
            ·
              refine ⟨38828367453153126035172743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25885578302102084023448495 38828367453153126035172743)
              ·
                refine ⟨58242551179729689052759115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38828367453153126035172743 58242551179729689052759115)
                ·
                  refine ⟨87363826769594533579138673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58242551179729689052759115 87363826769594533579138673)
                  ·
                    refine ⟨65522870077195900184354005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87363826769594533579138673 65522870077195900184354005)
                    ·
                      refine ⟨1535692267434278910570797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65522870077195900184354005 1535692267434278910570797)
                      ·
                        rfl

theorem cell23_2990750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2990750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990750 prefixEnd_2990750 := by exact prefixLift 2990750
  have htrace : WordTrace (prefixWord ++ tailWord_2990750) baseStart_2990750 baseEnd_2990750 := by
    simpa [prefixWord, tailWord_2990750, baseEnd_2990750] using wordTrace_append hprefix tailTrace_2990750
  have hstable : (prefixWord ++ tailWord_2990750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990750).length < 2 ^ (prefixWord ++ tailWord_2990750).sum := by decide
  have hdescent : baseEnd_2990750 < baseStart_2990750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990824 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_2990824 : Nat := 118140960795 + 2990824 * 2 ^ 59
def prefixEnd_2990824 : Nat := 4983230072969 + 3 ^ 40 * 2990824 * 2
def baseEnd_2990824 : Nat := 1535730265002711621045457

theorem tailTrace_2990824 : CollatzResearch.WordTrace tailWord_2990824 prefixEnd_2990824 1535730265002711621045457 := by
  unfold tailWord_2990824
  simp only [CollatzResearch.WordTrace]
  refine ⟨54542156458381457459037763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72722875277841943278717017 54542156458381457459037763)
  ·
    refine ⟨81813234687572186188556645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54542156458381457459037763 81813234687572186188556645)
    ·
      refine ⟨15339981503919784910354371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81813234687572186188556645 15339981503919784910354371)
      ·
        refine ⟨23009972255879677365531557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15339981503919784910354371 23009972255879677365531557)
        ·
          refine ⟨4314369797977439506037167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23009972255879677365531557 4314369797977439506037167)
          ·
            refine ⟨6471554696966159259055751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314369797977439506037167 6471554696966159259055751)
            ·
              refine ⟨9707332045449238888583627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6471554696966159259055751 9707332045449238888583627)
              ·
                refine ⟨14560998068173858332875441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9707332045449238888583627 14560998068173858332875441)
                ·
                  refine ⟨10920748551130393749656581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14560998068173858332875441 10920748551130393749656581)
                  ·
                    refine ⟨2047640353336948828060609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10920748551130393749656581 2047640353336948828060609)
                    ·
                      refine ⟨1535730265002711621045457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047640353336948828060609 1535730265002711621045457)
                      ·
                        rfl

theorem cell23_2990824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_2990824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990824 prefixEnd_2990824 := by exact prefixLift 2990824
  have htrace : WordTrace (prefixWord ++ tailWord_2990824) baseStart_2990824 baseEnd_2990824 := by
    simpa [prefixWord, tailWord_2990824, baseEnd_2990824] using wordTrace_append hprefix tailTrace_2990824
  have hstable : (prefixWord ++ tailWord_2990824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990824).length < 2 ^ (prefixWord ++ tailWord_2990824).sum := by decide
  have hdescent : baseEnd_2990824 < baseStart_2990824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990844 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_2990844 : Nat := 118140960795 + 2990844 * 2 ^ 59
def prefixEnd_2990844 : Nat := 4983230072969 + 3 ^ 40 * 2990844 * 2
def baseEnd_2990844 : Nat := 1535740534615801542795365

theorem tailTrace_2990844 : CollatzResearch.WordTrace tailWord_2990844 prefixEnd_2990844 1535740534615801542795365 := by
  unfold tailWord_2990844
  simp only [CollatzResearch.WordTrace]
  refine ⟨54542521188345229166901793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72723361584460305555869057 54542521188345229166901793)
  ·
    refine ⟨40906890891258921875176345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54542521188345229166901793 40906890891258921875176345)
    ·
      refine ⟨30680168168444191406382259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40906890891258921875176345 30680168168444191406382259)
      ·
        refine ⟨46020252252666287109573389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30680168168444191406382259 46020252252666287109573389)
        ·
          refine ⟨17257594594749857666090021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46020252252666287109573389 17257594594749857666090021)
          ·
            refine ⟨3235798986515598312391879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17257594594749857666090021 3235798986515598312391879)
            ·
              refine ⟨4853698479773397468587819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235798986515598312391879 4853698479773397468587819)
              ·
                refine ⟨7280547719660096202881729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853698479773397468587819 7280547719660096202881729)
                ·
                  refine ⟨5460410789745072152161297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7280547719660096202881729 5460410789745072152161297)
                  ·
                    refine ⟨4095308092308804114120973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5460410789745072152161297 4095308092308804114120973)
                    ·
                      refine ⟨1535740534615801542795365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095308092308804114120973 1535740534615801542795365)
                      ·
                        rfl

theorem cell23_2990844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_2990844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990844 prefixEnd_2990844 := by exact prefixLift 2990844
  have htrace : WordTrace (prefixWord ++ tailWord_2990844) baseStart_2990844 baseEnd_2990844 := by
    simpa [prefixWord, tailWord_2990844, baseEnd_2990844] using wordTrace_append hprefix tailTrace_2990844
  have hstable : (prefixWord ++ tailWord_2990844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990844).length < 2 ^ (prefixWord ++ tailWord_2990844).sum := by decide
  have hdescent : baseEnd_2990844 < baseStart_2990844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990867 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 4, 3, 2]
def baseStart_2990867 : Nat := 118140960795 + 2990867 * 2 ^ 59
def prefixEnd_2990867 : Nat := 4983230072969 + 3 ^ 40 * 2990867 * 2
def baseEnd_2990867 : Nat := 1535752344670854952807759

theorem tailTrace_2990867 : CollatzResearch.WordTrace tailWord_2990867 prefixEnd_2990867 1535752344670854952807759 := by
  unfold tailWord_2990867
  simp only [CollatzResearch.WordTrace]
  refine ⟨109085881255607133261890855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72723920837071422174593903 109085881255607133261890855)
  ·
    refine ⟨163628821883410699892836283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109085881255607133261890855 163628821883410699892836283)
    ·
      refine ⟨245443232825116049839254425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163628821883410699892836283 245443232825116049839254425)
      ·
        refine ⟨184082424618837037379440819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245443232825116049839254425 184082424618837037379440819)
        ·
          refine ⟨276123636928255556069161229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184082424618837037379440819 276123636928255556069161229)
          ·
            refine ⟨103546363848095833525935461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276123636928255556069161229 103546363848095833525935461)
            ·
              refine ⟨19414943221517968786112899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103546363848095833525935461 19414943221517968786112899)
              ·
                refine ⟨29122414832276953179169349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19414943221517968786112899 29122414832276953179169349)
                ·
                  refine ⟨5460452781051928721094253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29122414832276953179169349 5460452781051928721094253)
                  ·
                    refine ⟨2047669792894473270410345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5460452781051928721094253 2047669792894473270410345)
                    ·
                      refine ⟨1535752344670854952807759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047669792894473270410345 1535752344670854952807759)
                      ·
                        rfl

theorem cell23_2990867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 3, 2].length) (baseStart_2990867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990867 prefixEnd_2990867 := by exact prefixLift 2990867
  have htrace : WordTrace (prefixWord ++ tailWord_2990867) baseStart_2990867 baseEnd_2990867 := by
    simpa [prefixWord, tailWord_2990867, baseEnd_2990867] using wordTrace_append hprefix tailTrace_2990867
  have hstable : (prefixWord ++ tailWord_2990867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990867).length < 2 ^ (prefixWord ++ tailWord_2990867).sum := by decide
  have hdescent : baseEnd_2990867 < baseStart_2990867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990874 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_2990874 : Nat := 118140960795 + 2990874 * 2 ^ 59
def prefixEnd_2990874 : Nat := 4983230072969 + 3 ^ 40 * 2990874 * 2
def baseEnd_2990874 : Nat := 1535755939035436425420227

theorem tailTrace_2990874 : CollatzResearch.WordTrace tailWord_2990874 prefixEnd_2990874 1535755939035436425420227 := by
  unfold tailWord_2990874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27271534141645443364348919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72724091044387848971597117 27271534141645443364348919)
  ·
    refine ⟨40907301212468165046523379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27271534141645443364348919 40907301212468165046523379)
    ·
      refine ⟨61360951818702247569785069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40907301212468165046523379 61360951818702247569785069)
      ·
        refine ⟨23010356932013342838669401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61360951818702247569785069 23010356932013342838669401)
        ·
          refine ⟨17257767699010007129002051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23010356932013342838669401 17257767699010007129002051)
          ·
            refine ⟨25886651548515010693503077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17257767699010007129002051 25886651548515010693503077)
            ·
              refine ⟨4853747165346564505031827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25886651548515010693503077 4853747165346564505031827)
              ·
                refine ⟨7280620748019846757547741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853747165346564505031827 7280620748019846757547741)
                ·
                  refine ⟨2730232780507442534080403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7280620748019846757547741 2730232780507442534080403)
                  ·
                    refine ⟨4095349170761163801120605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2730232780507442534080403 4095349170761163801120605)
                    ·
                      refine ⟨1535755939035436425420227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095349170761163801120605 1535755939035436425420227)
                      ·
                        rfl

theorem cell23_2990874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_2990874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990874 prefixEnd_2990874 := by exact prefixLift 2990874
  have htrace : WordTrace (prefixWord ++ tailWord_2990874) baseStart_2990874 baseEnd_2990874 := by
    simpa [prefixWord, tailWord_2990874, baseEnd_2990874] using wordTrace_append hprefix tailTrace_2990874
  have hstable : (prefixWord ++ tailWord_2990874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990874).length < 2 ^ (prefixWord ++ tailWord_2990874).sum := by decide
  have hdescent : baseEnd_2990874 < baseStart_2990874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990894 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2990894 : Nat := 118140960795 + 2990894 * 2 ^ 59
def prefixEnd_2990894 : Nat := 4983230072969 + 3 ^ 40 * 2990894 * 2
def baseEnd_2990894 : Nat := 511922069549508782390045

theorem tailTrace_2990894 : CollatzResearch.WordTrace tailWord_2990894 prefixEnd_2990894 511922069549508782390045 := by
  unfold tailWord_2990894
  simp only [CollatzResearch.WordTrace]
  refine ⟨13635858253313664609140467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72724577351006211248749157 13635858253313664609140467)
  ·
    refine ⟨20453787379970496913710701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13635858253313664609140467 20453787379970496913710701)
    ·
      refine ⟨7670170267488936342641513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20453787379970496913710701 7670170267488936342641513)
      ·
        refine ⟨5752627700616702256981135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7670170267488936342641513 5752627700616702256981135)
        ·
          refine ⟨8628941550925053385471703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752627700616702256981135 8628941550925053385471703)
          ·
            refine ⟨12943412326387580078207555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8628941550925053385471703 12943412326387580078207555)
            ·
              refine ⟨19415118489581370117311333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12943412326387580078207555 19415118489581370117311333)
              ·
                refine ⟨3640334716796506896995875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19415118489581370117311333 3640334716796506896995875)
                ·
                  refine ⟨5460502075194760345493813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640334716796506896995875 5460502075194760345493813)
                  ·
                    refine ⟨511922069549508782390045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5460502075194760345493813 511922069549508782390045)
                    ·
                      rfl

theorem cell23_2990894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2990894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990894 prefixEnd_2990894 := by exact prefixLift 2990894
  have htrace : WordTrace (prefixWord ++ tailWord_2990894) baseStart_2990894 baseEnd_2990894 := by
    simpa [prefixWord, tailWord_2990894, baseEnd_2990894] using wordTrace_append hprefix tailTrace_2990894
  have hstable : (prefixWord ++ tailWord_2990894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990894).length < 2 ^ (prefixWord ++ tailWord_2990894).sum := by decide
  have hdescent : baseEnd_2990894 < baseStart_2990894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990897 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 2, 6, 2]
def baseStart_2990897 : Nat := 118140960795 + 2990897 * 2 ^ 59
def prefixEnd_2990897 : Nat := 4983230072969 + 3 ^ 40 * 2990897 * 2
def baseEnd_2990897 : Nat := 1535767749090489835432621

theorem tailTrace_2990897 : CollatzResearch.WordTrace tailWord_2990897 prefixEnd_2990897 1535767749090489835432621 := by
  unfold tailWord_2990897
  simp only [CollatzResearch.WordTrace]
  refine ⟨109086975445498448385482945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72724650296998965590321963 109086975445498448385482945)
  ·
    refine ⟨81815231584123836289112209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109086975445498448385482945 81815231584123836289112209)
    ·
      refine ⟨61361423688092877216834157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81815231584123836289112209 61361423688092877216834157)
      ·
        refine ⟨23010533883034828956312809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61361423688092877216834157 23010533883034828956312809)
        ·
          refine ⟨17257900412276121717234607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23010533883034828956312809 17257900412276121717234607)
          ·
            refine ⟨25886850618414182575851911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17257900412276121717234607 25886850618414182575851911)
            ·
              refine ⟨38830275927621273863777867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25886850618414182575851911 38830275927621273863777867)
              ·
                refine ⟨58245413891431910795666801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38830275927621273863777867 58245413891431910795666801)
                ·
                  refine ⟨43684060418573933096750101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58245413891431910795666801 43684060418573933096750101)
                  ·
                    refine ⟨2047690332120653113910161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43684060418573933096750101 2047690332120653113910161)
                    ·
                      refine ⟨1535767749090489835432621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047690332120653113910161 1535767749090489835432621)
                      ·
                        rfl

theorem cell23_2990897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_2990897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990897 prefixEnd_2990897 := by exact prefixLift 2990897
  have htrace : WordTrace (prefixWord ++ tailWord_2990897) baseStart_2990897 baseEnd_2990897 := by
    simpa [prefixWord, tailWord_2990897, baseEnd_2990897] using wordTrace_append hprefix tailTrace_2990897
  have hstable : (prefixWord ++ tailWord_2990897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990897).length < 2 ^ (prefixWord ++ tailWord_2990897).sum := by decide
  have hdescent : baseEnd_2990897 < baseStart_2990897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990925 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_2990925 : Nat := 118140960795 + 2990925 * 2 ^ 59
def prefixEnd_2990925 : Nat := 4983230072969 + 3 ^ 40 * 2990925 * 2
def baseEnd_2990925 : Nat := 1535782126548815725882493

theorem tailTrace_2990925 : CollatzResearch.WordTrace tailWord_2990925 prefixEnd_2990925 1535782126548815725882493 := by
  unfold tailWord_2990925
  simp only [CollatzResearch.WordTrace]
  refine ⟨109087996689397009167502229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72725331126264672778334819 109087996689397009167502229)
  ·
    refine ⟨5113499844815484804726667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109087996689397009167502229 5113499844815484804726667)
    ·
      refine ⟨7670249767223227207090001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5113499844815484804726667 7670249767223227207090001)
      ·
        refine ⟨5752687325417420405317501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7670249767223227207090001 5752687325417420405317501)
        ·
          refine ⟨2157257747031532651994063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5752687325417420405317501 2157257747031532651994063)
          ·
            refine ⟨3235886620547298977991095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157257747031532651994063 3235886620547298977991095)
            ·
              refine ⟨4853829930820948466986643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235886620547298977991095 4853829930820948466986643)
              ·
                refine ⟨7280744896231422700479965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853829930820948466986643 7280744896231422700479965)
                ·
                  refine ⟨2730279336086783512679987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7280744896231422700479965 2730279336086783512679987)
                  ·
                    refine ⟨4095419004130175269019981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2730279336086783512679987 4095419004130175269019981)
                    ·
                      refine ⟨1535782126548815725882493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095419004130175269019981 1535782126548815725882493)
                      ·
                        rfl

theorem cell23_2990925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_2990925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990925 prefixEnd_2990925 := by exact prefixLift 2990925
  have htrace : WordTrace (prefixWord ++ tailWord_2990925) baseStart_2990925 baseEnd_2990925 := by
    simpa [prefixWord, tailWord_2990925, baseEnd_2990925] using wordTrace_append hprefix tailTrace_2990925
  have hstable : (prefixWord ++ tailWord_2990925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990925).length < 2 ^ (prefixWord ++ tailWord_2990925).sum := by decide
  have hdescent : baseEnd_2990925 < baseStart_2990925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990931 : List Nat := [1, 1, 1, 2, 1, 1, 3, 8, 1, 2, 2]
def baseStart_2990931 : Nat := 118140960795 + 2990931 * 2 ^ 59
def prefixEnd_2990931 : Nat := 4983230072969 + 3 ^ 40 * 2990931 * 2
def baseEnd_2990931 : Nat := 1535785207432742702407465

theorem tailTrace_2990931 : CollatzResearch.WordTrace tailWord_2990931 prefixEnd_2990931 1535785207432742702407465 := by
  unfold tailWord_2990931
  simp only [CollatzResearch.WordTrace]
  refine ⟨109088215527375272192220647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72725477018250181461480431 109088215527375272192220647)
  ·
    refine ⟨163632323291062908288330971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109088215527375272192220647 163632323291062908288330971)
    ·
      refine ⟨245448484936594362432496457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163632323291062908288330971 245448484936594362432496457)
      ·
        refine ⟨184086363702445771824372343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245448484936594362432496457 184086363702445771824372343)
        ·
          refine ⟨276129545553668657736558515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184086363702445771824372343 276129545553668657736558515)
          ·
            refine ⟨414194318330502986604837773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276129545553668657736558515 414194318330502986604837773)
            ·
              refine ⟨155322869373938619976814165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414194318330502986604837773 155322869373938619976814165)
              ·
                refine ⟨1820189875475843202853291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 155322869373938619976814165 1820189875475843202853291)
                ·
                  refine ⟨2730284813213764804279937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820189875475843202853291 2730284813213764804279937)
                  ·
                    refine ⟨2047713609910323603209953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2730284813213764804279937 2047713609910323603209953)
                    ·
                      refine ⟨1535785207432742702407465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047713609910323603209953 1535785207432742702407465)
                      ·
                        rfl

theorem cell23_2990931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 2, 2].length) (baseStart_2990931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990931 prefixEnd_2990931 := by exact prefixLift 2990931
  have htrace : WordTrace (prefixWord ++ tailWord_2990931) baseStart_2990931 baseEnd_2990931 := by
    simpa [prefixWord, tailWord_2990931, baseEnd_2990931] using wordTrace_append hprefix tailTrace_2990931
  have hstable : (prefixWord ++ tailWord_2990931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990931).length < 2 ^ (prefixWord ++ tailWord_2990931).sum := by decide
  have hdescent : baseEnd_2990931 < baseStart_2990931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990951 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_2990951 : Nat := 118140960795 + 2990951 * 2 ^ 59
def prefixEnd_2990951 : Nat := 4983230072969 + 3 ^ 40 * 2990951 * 2
def baseEnd_2990951 : Nat := 1535795477045832624157373

theorem tailTrace_2990951 : CollatzResearch.WordTrace tailWord_2990951 prefixEnd_2990951 1535795477045832624157373 := by
  unfold tailWord_2990951
  simp only [CollatzResearch.WordTrace]
  refine ⟨109088944987302815607948707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72725963324868543738632471 109088944987302815607948707)
  ·
    refine ⟨163633417480954223411923061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109088944987302815607948707 163633417480954223411923061)
    ·
      refine ⟨15340632888839458444867787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163633417480954223411923061 15340632888839458444867787)
      ·
        refine ⟨23010949333259187667301681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15340632888839458444867787 23010949333259187667301681)
        ·
          refine ⟨17258211999944390750476261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23010949333259187667301681 17258211999944390750476261)
          ·
            refine ⟨3235914749989573265714299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17258211999944390750476261 3235914749989573265714299)
            ·
              refine ⟨4853872124984359898571449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235914749989573265714299 4853872124984359898571449)
              ·
                refine ⟨3640404093738269923928587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4853872124984359898571449 3640404093738269923928587)
                ·
                  refine ⟨5460606140607404885892881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640404093738269923928587 5460606140607404885892881)
                  ·
                    refine ⟨4095454605455553664419661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5460606140607404885892881 4095454605455553664419661)
                    ·
                      refine ⟨1535795477045832624157373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095454605455553664419661 1535795477045832624157373)
                      ·
                        rfl

theorem cell23_2990951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_2990951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990951 prefixEnd_2990951 := by exact prefixLift 2990951
  have htrace : WordTrace (prefixWord ++ tailWord_2990951) baseStart_2990951 baseEnd_2990951 := by
    simpa [prefixWord, tailWord_2990951, baseEnd_2990951] using wordTrace_append hprefix tailTrace_2990951
  have hstable : (prefixWord ++ tailWord_2990951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990951).length < 2 ^ (prefixWord ++ tailWord_2990951).sum := by decide
  have hdescent : baseEnd_2990951 < baseStart_2990951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990960 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_2990960 : Nat := 118140960795 + 2990960 * 2 ^ 59
def prefixEnd_2990960 : Nat := 4983230072969 + 3 ^ 40 * 2990960 * 2
def baseEnd_2990960 : Nat := 1535800098371723088944831

theorem tailTrace_2990960 : CollatzResearch.WordTrace tailWord_2990960 prefixEnd_2990960 1535800098371723088944831 := by
  unfold tailWord_2990960
  simp only [CollatzResearch.WordTrace]
  refine ⟨54544636622135105072513167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72726182162846806763350889 54544636622135105072513167)
  ·
    refine ⟨81816954933202657608769751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54544636622135105072513167 81816954933202657608769751)
    ·
      refine ⟨122725432399803986413154627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81816954933202657608769751 122725432399803986413154627)
      ·
        refine ⟨184088148599705979619731941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122725432399803986413154627 184088148599705979619731941)
        ·
          refine ⟨34516527862444871178699739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184088148599705979619731941 34516527862444871178699739)
          ·
            refine ⟨51774791793667306768049609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34516527862444871178699739 51774791793667306768049609)
            ·
              refine ⟨38831093845250480076037207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51774791793667306768049609 38831093845250480076037207)
              ·
                refine ⟨58246640767875720114055811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38831093845250480076037207 58246640767875720114055811)
                ·
                  refine ⟨87369961151813580171083717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58246640767875720114055811 87369961151813580171083717)
                  ·
                    refine ⟨16381867715965046282078197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87369961151813580171083717 16381867715965046282078197)
                    ·
                      refine ⟨1535800098371723088944831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16381867715965046282078197 1535800098371723088944831)
                      ·
                        rfl

theorem cell23_2990960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_2990960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990960 prefixEnd_2990960 := by exact prefixLift 2990960
  have htrace : WordTrace (prefixWord ++ tailWord_2990960) baseStart_2990960 baseEnd_2990960 := by
    simpa [prefixWord, tailWord_2990960, baseEnd_2990960] using wordTrace_append hprefix tailTrace_2990960
  have hstable : (prefixWord ++ tailWord_2990960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990960).length < 2 ^ (prefixWord ++ tailWord_2990960).sum := by decide
  have hdescent : baseEnd_2990960 < baseStart_2990960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990981 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_2990981 : Nat := 118140960795 + 2990981 * 2 ^ 59
def prefixEnd_2990981 : Nat := 4983230072969 + 3 ^ 40 * 2990981 * 2
def baseEnd_2990981 : Nat := 1535810881465467506782235

theorem tailTrace_2990981 : CollatzResearch.WordTrace tailWord_2990981 prefixEnd_2990981 1535810881465467506782235 := by
  unfold tailWord_2990981
  simp only [CollatzResearch.WordTrace]
  refine ⟨109090039177194130731540797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72726692784796087154360531 109090039177194130731540797)
  ·
    refine ⟨40908764691447799024327799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109090039177194130731540797 40908764691447799024327799)
    ·
      refine ⟨61363147037171698536491699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40908764691447799024327799 61363147037171698536491699)
      ·
        refine ⟨92044720555757547804737549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61363147037171698536491699 92044720555757547804737549)
        ·
          refine ⟨34516770208409080426776581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92044720555757547804737549 34516770208409080426776581)
          ·
            refine ⟨6471894414076702580020609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34516770208409080426776581 6471894414076702580020609)
            ·
              refine ⟨4853920810557526935015457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6471894414076702580020609 4853920810557526935015457)
              ·
                refine ⟨3640440607918145201261593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4853920810557526935015457 3640440607918145201261593)
                ·
                  refine ⟨2730330455938608900946195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3640440607918145201261593 2730330455938608900946195)
                  ·
                    refine ⟨4095495683907913351419293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2730330455938608900946195 4095495683907913351419293)
                    ·
                      refine ⟨1535810881465467506782235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095495683907913351419293 1535810881465467506782235)
                      ·
                        rfl

theorem cell23_2990981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_2990981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990981 prefixEnd_2990981 := by exact prefixLift 2990981
  have htrace : WordTrace (prefixWord ++ tailWord_2990981) baseStart_2990981 baseEnd_2990981 := by
    simpa [prefixWord, tailWord_2990981, baseEnd_2990981] using wordTrace_append hprefix tailTrace_2990981
  have hstable : (prefixWord ++ tailWord_2990981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990981).length < 2 ^ (prefixWord ++ tailWord_2990981).sum := by decide
  have hdescent : baseEnd_2990981 < baseStart_2990981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990997 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2990997 : Nat := 118140960795 + 2990997 * 2 ^ 59
def prefixEnd_2990997 : Nat := 4983230072969 + 3 ^ 40 * 2990997 * 2
def baseEnd_2990997 : Nat := 511939699051979814727387

theorem tailTrace_2990997 : CollatzResearch.WordTrace tailWord_2990997 prefixEnd_2990997 511939699051979814727387 := by
  unfold tailWord_2990997
  simp only [CollatzResearch.WordTrace]
  refine ⟨109090622745136165464123245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72727081830090776976082163 109090622745136165464123245)
  ·
    refine ⟨40908983529426062049046217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109090622745136165464123245 40908983529426062049046217)
    ·
      refine ⟨30681737647069546536784663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40908983529426062049046217 30681737647069546536784663)
      ·
        refine ⟨46022606470604319805176995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30681737647069546536784663 46022606470604319805176995)
        ·
          refine ⟨69033909705906479707765493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46022606470604319805176995 69033909705906479707765493)
          ·
            refine ⟨6471929034928732472603015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69033909705906479707765493 6471929034928732472603015)
            ·
              refine ⟨9707893552393098708904523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6471929034928732472603015 9707893552393098708904523)
              ·
                refine ⟨14561840328589648063356785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9707893552393098708904523 14561840328589648063356785)
                ·
                  refine ⟨10921380246442236047517589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14561840328589648063356785 10921380246442236047517589)
                  ·
                    refine ⟨511939699051979814727387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10921380246442236047517589 511939699051979814727387)
                    ·
                      rfl

theorem cell23_2990997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2990997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990997 prefixEnd_2990997 := by exact prefixLift 2990997
  have htrace : WordTrace (prefixWord ++ tailWord_2990997) baseStart_2990997 baseEnd_2990997 := by
    simpa [prefixWord, tailWord_2990997, baseEnd_2990997] using wordTrace_append hprefix tailTrace_2990997
  have hstable : (prefixWord ++ tailWord_2990997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990997).length < 2 ^ (prefixWord ++ tailWord_2990997).sum := by decide
  have hdescent : baseEnd_2990997 < baseStart_2990997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990998 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2990998 : Nat := 118140960795 + 2990998 * 2 ^ 59
def prefixEnd_2990998 : Nat := 4983230072969 + 3 ^ 40 * 2990998 * 2
def baseEnd_2990998 : Nat := 1535819610636593940269657

theorem tailTrace_2990998 : CollatzResearch.WordTrace tailWord_2990998 prefixEnd_2990998 1535819610636593940269657 := by
  unfold tailWord_2990998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818166201133283914681853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72727106145421695089939765 6818166201133283914681853)
  ·
    refine ⟨2556812325424981468005695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6818166201133283914681853 2556812325424981468005695)
    ·
      refine ⟨3835218488137472202008543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2556812325424981468005695 3835218488137472202008543)
      ·
        refine ⟨5752827732206208303012815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3835218488137472202008543 5752827732206208303012815)
        ·
          refine ⟨8629241598309312454519223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752827732206208303012815 8629241598309312454519223)
          ·
            refine ⟨12943862397463968681778835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8629241598309312454519223 12943862397463968681778835)
            ·
              refine ⟨19415793596195953022668253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12943862397463968681778835 19415793596195953022668253)
              ·
                refine ⟨7280922598573482383500595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19415793596195953022668253 7280922598573482383500595)
                ·
                  refine ⟨10921383897860223575250893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7280922598573482383500595 10921383897860223575250893)
                  ·
                    refine ⟨4095518961697583840719085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10921383897860223575250893 4095518961697583840719085)
                    ·
                      refine ⟨1535819610636593940269657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095518961697583840719085 1535819610636593940269657)
                      ·
                        rfl

theorem cell23_2990998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2990998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2990998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2990998 prefixEnd_2990998 := by exact prefixLift 2990998
  have htrace : WordTrace (prefixWord ++ tailWord_2990998) baseStart_2990998 baseEnd_2990998 := by
    simpa [prefixWord, tailWord_2990998, baseEnd_2990998] using wordTrace_append hprefix tailTrace_2990998
  have hstable : (prefixWord ++ tailWord_2990998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990998).length < 2 ^ (prefixWord ++ tailWord_2990998).sum := by decide
  have hdescent : baseEnd_2990998 < baseStart_2990998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991025 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 1, 3, 2]
def baseStart_2991025 : Nat := 118140960795 + 2991025 * 2 ^ 59
def prefixEnd_2991025 : Nat := 4983230072969 + 3 ^ 40 * 2991025 * 2
def baseEnd_2991025 : Nat := 1535833474614265334632033

theorem tailTrace_2991025 : CollatzResearch.WordTrace tailWord_2991025 prefixEnd_2991025 1535833474614265334632033 := by
  unfold tailWord_2991025
  simp only [CollatzResearch.WordTrace]
  refine ⟨109091643989034726246142529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72727762659356484164095019 109091643989034726246142529)
  ·
    refine ⟨81818732991776044684606897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109091643989034726246142529 81818732991776044684606897)
    ·
      refine ⟨61364049743832033513455173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81818732991776044684606897 61364049743832033513455173)
      ·
        refine ⟨11505759326968506283772845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61364049743832033513455173 11505759326968506283772845)
        ·
          refine ⟨4314659747613189856414817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11505759326968506283772845 4314659747613189856414817)
          ·
            refine ⟨3235994810709892392311113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4314659747613189856414817 3235994810709892392311113)
            ·
              refine ⟨2426996108032419294233335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235994810709892392311113 2426996108032419294233335)
              ·
                refine ⟨3640494162048628941350003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426996108032419294233335 3640494162048628941350003)
                ·
                  refine ⟨5460741243072943412025005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640494162048628941350003 5460741243072943412025005)
                  ·
                    refine ⟨2047777966152353779509377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5460741243072943412025005 2047777966152353779509377)
                    ·
                      refine ⟨1535833474614265334632033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047777966152353779509377 1535833474614265334632033)
                      ·
                        rfl

theorem cell23_2991025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_2991025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991025 prefixEnd_2991025 := by exact prefixLift 2991025
  have htrace : WordTrace (prefixWord ++ tailWord_2991025) baseStart_2991025 baseEnd_2991025 := by
    simpa [prefixWord, tailWord_2991025, baseEnd_2991025] using wordTrace_append hprefix tailTrace_2991025
  have hstable : (prefixWord ++ tailWord_2991025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991025).length < 2 ^ (prefixWord ++ tailWord_2991025).sum := by decide
  have hdescent : baseEnd_2991025 < baseStart_2991025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991054 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_2991054 : Nat := 118140960795 + 2991054 * 2 ^ 59
def prefixEnd_2991054 : Nat := 4983230072969 + 3 ^ 40 * 2991054 * 2
def baseEnd_2991054 : Nat := 1535848365553245721169399

theorem tailTrace_2991054 : CollatzResearch.WordTrace tailWord_2991054 prefixEnd_2991054 1535848365553245721169399 := by
  unfold tailWord_2991054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636587713241208024868527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72728467803953109465965477 13636587713241208024868527)
  ·
    refine ⟨20454881569861812037302791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13636587713241208024868527 20454881569861812037302791)
    ·
      refine ⟨30682322354792718055954187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20454881569861812037302791 30682322354792718055954187)
      ·
        refine ⟨46023483532189077083931281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30682322354792718055954187 46023483532189077083931281)
        ·
          refine ⟨34517612649141807812948461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46023483532189077083931281 34517612649141807812948461)
          ·
            refine ⟨12944104743428177929855673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34517612649141807812948461 12944104743428177929855673)
            ·
              refine ⟨9708078557571133447391755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12944104743428177929855673 9708078557571133447391755)
              ·
                refine ⟨14562117836356700171087633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9708078557571133447391755 14562117836356700171087633)
                ·
                  refine ⟨10921588377267525128315725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14562117836356700171087633 10921588377267525128315725)
                  ·
                    refine ⟨4095595641475321923118397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10921588377267525128315725 4095595641475321923118397)
                    ·
                      refine ⟨1535848365553245721169399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095595641475321923118397 1535848365553245721169399)
                      ·
                        rfl

theorem cell23_2991054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_2991054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991054 prefixEnd_2991054 := by exact prefixLift 2991054
  have htrace : WordTrace (prefixWord ++ tailWord_2991054) baseStart_2991054 baseEnd_2991054 := by
    simpa [prefixWord, tailWord_2991054, baseEnd_2991054] using wordTrace_append hprefix tailTrace_2991054
  have hstable : (prefixWord ++ tailWord_2991054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991054).length < 2 ^ (prefixWord ++ tailWord_2991054).sum := by decide
  have hdescent : baseEnd_2991054 < baseStart_2991054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991106 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2991106 : Nat := 118140960795 + 2991106 * 2 ^ 59
def prefixEnd_2991106 : Nat := 4983230072969 + 3 ^ 40 * 2991106 * 2
def baseEnd_2991106 : Nat := 1535875066547279517719161

theorem tailTrace_2991106 : CollatzResearch.WordTrace tailWord_2991106 prefixEnd_2991106 1535875066547279517719161 := by
  unfold tailWord_2991106
  simp only [CollatzResearch.WordTrace]
  refine ⟨27273649575435319269960293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72729732201160851386560781 27273649575435319269960293)
  ·
    refine ⟨5113809295394122363117555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27273649575435319269960293 5113809295394122363117555)
    ·
      refine ⟨7670713943091183544676333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5113809295394122363117555 7670713943091183544676333)
      ·
        refine ⟨2876517728659193829253625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7670713943091183544676333 2876517728659193829253625)
        ·
          refine ⟨2157388296494395371940219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2876517728659193829253625 2157388296494395371940219)
          ·
            refine ⟨3236082444741593057910329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157388296494395371940219 3236082444741593057910329)
            ·
              refine ⟨2427061833556194793432747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236082444741593057910329 2427061833556194793432747)
              ·
                refine ⟨3640592750334292190149121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427061833556194793432747 3640592750334292190149121)
                ·
                  refine ⟨2730444562750719142611841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3640592750334292190149121 2730444562750719142611841)
                  ·
                    refine ⟨2047833422063039356958881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2730444562750719142611841 2047833422063039356958881)
                    ·
                      refine ⟨1535875066547279517719161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047833422063039356958881 1535875066547279517719161)
                      ·
                        rfl

theorem cell23_2991106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2991106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991106 prefixEnd_2991106 := by exact prefixLift 2991106
  have htrace : WordTrace (prefixWord ++ tailWord_2991106) baseStart_2991106 baseEnd_2991106 := by
    simpa [prefixWord, tailWord_2991106, baseEnd_2991106] using wordTrace_append hprefix tailTrace_2991106
  have hstable : (prefixWord ++ tailWord_2991106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991106).length < 2 ^ (prefixWord ++ tailWord_2991106).sum := by decide
  have hdescent : baseEnd_2991106 < baseStart_2991106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991164 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_2991164 : Nat := 118140960795 + 2991164 * 2 ^ 59
def prefixEnd_2991164 : Nat := 4983230072969 + 3 ^ 40 * 2991164 * 2
def baseEnd_2991164 : Nat := 511968282808413430264631

theorem tailTrace_2991164 : CollatzResearch.WordTrace tailWord_2991164 prefixEnd_2991164 511968282808413430264631 := by
  unfold tailWord_2991164
  simp only [CollatzResearch.WordTrace]
  refine ⟨54548356867765576492726273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72731142490354101990301697 54548356867765576492726273)
  ·
    refine ⟨40911267650824182369544705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54548356867765576492726273 40911267650824182369544705)
    ·
      refine ⟨30683450738118136777158529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40911267650824182369544705 30683450738118136777158529)
      ·
        refine ⟨23012588053588602582868897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30683450738118136777158529 23012588053588602582868897)
        ·
          refine ⟨17259441040191451937151673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23012588053588602582868897 17259441040191451937151673)
          ·
            refine ⟨12944580780143588952863755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17259441040191451937151673 12944580780143588952863755)
            ·
              refine ⟨19416871170215383429295633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12944580780143588952863755 19416871170215383429295633)
              ·
                refine ⟨14562653377661537571971725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19416871170215383429295633 14562653377661537571971725)
                ·
                  refine ⟨5460995016623076589489397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14562653377661537571971725 5460995016623076589489397)
                  ·
                    refine ⟨511968282808413430264631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5460995016623076589489397 511968282808413430264631)
                    ·
                      rfl

theorem cell23_2991164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_2991164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991164 prefixEnd_2991164 := by exact prefixLift 2991164
  have htrace : WordTrace (prefixWord ++ tailWord_2991164) baseStart_2991164 baseEnd_2991164 := by
    simpa [prefixWord, tailWord_2991164, baseEnd_2991164] using wordTrace_append hprefix tailTrace_2991164
  have hstable : (prefixWord ++ tailWord_2991164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991164).length < 2 ^ (prefixWord ++ tailWord_2991164).sum := by decide
  have hdescent : baseEnd_2991164 < baseStart_2991164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991181 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2991181 : Nat := 118140960795 + 2991181 * 2 ^ 59
def prefixEnd_2991181 : Nat := 4983230072969 + 3 ^ 40 * 2991181 * 2
def baseEnd_2991181 : Nat := 511971192532122241427105

theorem tailTrace_2991181 : CollatzResearch.WordTrace tailWord_2991181 prefixEnd_2991181 511971192532122241427105 := by
  unfold tailWord_2991181
  simp only [CollatzResearch.WordTrace]
  refine ⟨109097333776469564888821397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72731555850979709925880931 109097333776469564888821397)
  ·
    refine ⟨5113937520772010854163503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109097333776469564888821397 5113937520772010854163503)
    ·
      refine ⟨7670906281158016281245255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5113937520772010854163503 7670906281158016281245255)
      ·
        refine ⟨11506359421737024421867883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7670906281158016281245255 11506359421737024421867883)
        ·
          refine ⟨17259539132605536632801825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11506359421737024421867883 17259539132605536632801825)
          ·
            refine ⟨12944654349454152474601369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17259539132605536632801825 12944654349454152474601369)
            ·
              refine ⟨9708490762090614355951027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12944654349454152474601369 9708490762090614355951027)
              ·
                refine ⟨14562736143135921533926541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9708490762090614355951027 14562736143135921533926541)
                ·
                  refine ⟨5461026053675970575222453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14562736143135921533926541 5461026053675970575222453)
                  ·
                    refine ⟨511971192532122241427105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5461026053675970575222453 511971192532122241427105)
                    ·
                      rfl

theorem cell23_2991181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2991181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991181 prefixEnd_2991181 := by exact prefixLift 2991181
  have htrace : WordTrace (prefixWord ++ tailWord_2991181) baseStart_2991181 baseEnd_2991181 := by
    simpa [prefixWord, tailWord_2991181, baseEnd_2991181] using wordTrace_append hprefix tailTrace_2991181
  have hstable : (prefixWord ++ tailWord_2991181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991181).length < 2 ^ (prefixWord ++ tailWord_2991181).sum := by decide
  have hdescent : baseEnd_2991181 < baseStart_2991181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991188 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_2991188 : Nat := 118140960795 + 2991188 * 2 ^ 59
def prefixEnd_2991188 : Nat := 4983230072969 + 3 ^ 40 * 2991188 * 2
def baseEnd_2991188 : Nat := 1535917171960948196893783

theorem tailTrace_2991188 : CollatzResearch.WordTrace tailWord_2991188 prefixEnd_2991188 1535917171960948196893783 := by
  unfold tailWord_2991188
  simp only [CollatzResearch.WordTrace]
  refine ⟨54548794543722102542163109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72731726058296136722884145 54548794543722102542163109)
  ·
    refine ⟨10227898976947894226655583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54548794543722102542163109 10227898976947894226655583)
    ·
      refine ⟨15341848465421841339983375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10227898976947894226655583 15341848465421841339983375)
      ·
        refine ⟨23012772698132762009975063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15341848465421841339983375 23012772698132762009975063)
        ·
          refine ⟨34519159047199143014962595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23012772698132762009975063 34519159047199143014962595)
          ·
            refine ⟨51778738570798714522443893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34519159047199143014962595 51778738570798714522443893)
            ·
              refine ⟨4854256741012379486479115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51778738570798714522443893 4854256741012379486479115)
              ·
                refine ⟨7281385111518569229718673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4854256741012379486479115 7281385111518569229718673)
                ·
                  refine ⟨5461038833638926922289005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7281385111518569229718673 5461038833638926922289005)
                  ·
                    refine ⟨2047889562614597595858377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5461038833638926922289005 2047889562614597595858377)
                    ·
                      refine ⟨1535917171960948196893783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2047889562614597595858377 1535917171960948196893783)
                      ·
                        rfl

theorem cell23_2991188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_2991188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991188 prefixEnd_2991188 := by exact prefixLift 2991188
  have htrace : WordTrace (prefixWord ++ tailWord_2991188) baseStart_2991188 baseEnd_2991188 := by
    simpa [prefixWord, tailWord_2991188, baseEnd_2991188] using wordTrace_append hprefix tailTrace_2991188
  have hstable : (prefixWord ++ tailWord_2991188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991188).length < 2 ^ (prefixWord ++ tailWord_2991188).sum := by decide
  have hdescent : baseEnd_2991188 < baseStart_2991188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991204 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_2991204 : Nat := 118140960795 + 2991204 * 2 ^ 59
def prefixEnd_2991204 : Nat := 4983230072969 + 3 ^ 40 * 2991204 * 2
def baseEnd_2991204 : Nat := 1535925387651420134293709

theorem tailTrace_2991204 : CollatzResearch.WordTrace tailWord_2991204 prefixEnd_2991204 1535925387651420134293709 := by
  unfold tailWord_2991204
  simp only [CollatzResearch.WordTrace]
  refine ⟨54549086327693119908454333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72732115103590826544605777 54549086327693119908454333)
  ·
    refine ⟨20455907372884919965670375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54549086327693119908454333 20455907372884919965670375)
    ·
      refine ⟨30683861059327379948505563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20455907372884919965670375 30683861059327379948505563)
      ·
        refine ⟨46025791588991069922758345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30683861059327379948505563 46025791588991069922758345)
        ·
          refine ⟨34519343691743302442068759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46025791588991069922758345 34519343691743302442068759)
          ·
            refine ⟨51779015537614953663103139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34519343691743302442068759 51779015537614953663103139)
            ·
              refine ⟨77668523306422430494654709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51779015537614953663103139 77668523306422430494654709)
              ·
                refine ⟨7281424059977102858873879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77668523306422430494654709 7281424059977102858873879)
                ·
                  refine ⟨10922136089965654288310819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7281424059977102858873879 10922136089965654288310819)
                  ·
                    refine ⟨16383204134948481432466229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10922136089965654288310819 16383204134948481432466229)
                    ·
                      refine ⟨1535925387651420134293709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16383204134948481432466229 1535925387651420134293709)
                      ·
                        rfl

theorem cell23_2991204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_2991204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991204 prefixEnd_2991204 := by exact prefixLift 2991204
  have htrace : WordTrace (prefixWord ++ tailWord_2991204) baseStart_2991204 baseEnd_2991204 := by
    simpa [prefixWord, tailWord_2991204, baseEnd_2991204] using wordTrace_append hprefix tailTrace_2991204
  have hstable : (prefixWord ++ tailWord_2991204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991204).length < 2 ^ (prefixWord ++ tailWord_2991204).sum := by decide
  have hdescent : baseEnd_2991204 < baseStart_2991204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991228 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_2991228 : Nat := 118140960795 + 2991228 * 2 ^ 59
def prefixEnd_2991228 : Nat := 4983230072969 + 3 ^ 40 * 2991228 * 2
def baseEnd_2991228 : Nat := 511979237062376013464533

theorem tailTrace_2991228 : CollatzResearch.WordTrace tailWord_2991228 prefixEnd_2991228 511979237062376013464533 := by
  unfold tailWord_2991228
  simp only [CollatzResearch.WordTrace]
  refine ⟨54549524003649645957891169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72732698671532861277188225 54549524003649645957891169)
  ·
    refine ⟨40912143002737234468418377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54549524003649645957891169 40912143002737234468418377)
    ·
      refine ⟨30684107252052925851313783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40912143002737234468418377 30684107252052925851313783)
      ·
        refine ⟨46026160878079388776970675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30684107252052925851313783 46026160878079388776970675)
        ·
          refine ⟨69039241317119083165456013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46026160878079388776970675 69039241317119083165456013)
          ·
            refine ⟨25889715493919656187046005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69039241317119083165456013 25889715493919656187046005)
            ·
              refine ⟨2427160827554967767535563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25889715493919656187046005 2427160827554967767535563)
              ·
                refine ⟨3640741241332451651303345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427160827554967767535563 3640741241332451651303345)
                ·
                  refine ⟨2730555930999338738477509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3640741241332451651303345 2730555930999338738477509)
                  ·
                    refine ⟨511979237062376013464533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2730555930999338738477509 511979237062376013464533)
                    ·
                      rfl

theorem cell23_2991228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_2991228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991228 prefixEnd_2991228 := by exact prefixLift 2991228
  have htrace : WordTrace (prefixWord ++ tailWord_2991228) baseStart_2991228 baseEnd_2991228 := by
    simpa [prefixWord, tailWord_2991228, baseEnd_2991228] using wordTrace_append hprefix tailTrace_2991228
  have hstable : (prefixWord ++ tailWord_2991228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991228).length < 2 ^ (prefixWord ++ tailWord_2991228).sum := by decide
  have hdescent : baseEnd_2991228 < baseStart_2991228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991241 : List Nat := [1, 2, 1, 1, 4, 5, 2, 7]
def baseStart_2991241 : Nat := 118140960795 + 2991241 * 2 ^ 59
def prefixEnd_2991241 : Nat := 4983230072969 + 3 ^ 40 * 2991241 * 2
def baseEnd_2991241 : Nat := 56886829127245795908557

theorem tailTrace_2991241 : CollatzResearch.WordTrace tailWord_2991241 prefixEnd_2991241 56886829127245795908557 := by
  unfold tailWord_2991241
  simp only [CollatzResearch.WordTrace]
  refine ⟨109099522156252195136005577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72733014770834796757337051 109099522156252195136005577)
  ·
    refine ⟨81824641617189146352004183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109099522156252195136005577 81824641617189146352004183)
    ·
      refine ⟨122736962425783719528006275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81824641617189146352004183 122736962425783719528006275)
      ·
        refine ⟨184105443638675579292009413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122736962425783719528006275 184105443638675579292009413)
        ·
          refine ⟨34519770682251671117251765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184105443638675579292009413 34519770682251671117251765)
          ·
            refine ⟨3236228501461094167242353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34519770682251671117251765 3236228501461094167242353)
            ·
              refine ⟨2427171376095820625431765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236228501461094167242353 2427171376095820625431765)
              ·
                refine ⟨56886829127245795908557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2427171376095820625431765 56886829127245795908557)
                ·
                  rfl

theorem cell23_2991241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 7].length) (baseStart_2991241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991241 prefixEnd_2991241 := by exact prefixLift 2991241
  have htrace : WordTrace (prefixWord ++ tailWord_2991241) baseStart_2991241 baseEnd_2991241 := by
    simpa [prefixWord, tailWord_2991241, baseEnd_2991241] using wordTrace_append hprefix tailTrace_2991241
  have hstable : (prefixWord ++ tailWord_2991241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991241).length < 2 ^ (prefixWord ++ tailWord_2991241).sum := by decide
  have hdescent : baseEnd_2991241 < baseStart_2991241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991251 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 3]
def baseStart_2991251 : Nat := 118140960795 + 2991251 * 2 ^ 59
def prefixEnd_2991251 : Nat := 4983230072969 + 3 ^ 40 * 2991251 * 2
def baseEnd_2991251 : Nat := 1535949521242181450405993

theorem tailTrace_2991251 : CollatzResearch.WordTrace tailWord_2991251 prefixEnd_2991251 1535949521242181450405993 := by
  unfold tailWord_2991251
  simp only [CollatzResearch.WordTrace]
  refine ⟨109099886886215966843869607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72733257924143977895913071 109099886886215966843869607)
  ·
    refine ⟨163649830329323950265804411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109099886886215966843869607 163649830329323950265804411)
    ·
      refine ⟨245474745493985925398706617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163649830329323950265804411 245474745493985925398706617)
      ·
        refine ⟨184106059120489444049029963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245474745493985925398706617 184106059120489444049029963)
        ·
          refine ⟨276159088680734166073544945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184106059120489444049029963 276159088680734166073544945)
          ·
            refine ⟨207119316510550624555158709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276159088680734166073544945 207119316510550624555158709)
            ·
              refine ⟨19417435922864121052046129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207119316510550624555158709 19417435922864121052046129)
              ·
                refine ⟨14563076942148090789034597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19417435922864121052046129 14563076942148090789034597)
                ·
                  refine ⟨2730576926652767022943987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14563076942148090789034597 2730576926652767022943987)
                  ·
                    refine ⟨4095865389979150534415981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2730576926652767022943987 4095865389979150534415981)
                    ·
                      refine ⟨1535949521242181450405993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095865389979150534415981 1535949521242181450405993)
                      ·
                        rfl

theorem cell23_2991251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 3].length) (baseStart_2991251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991251 prefixEnd_2991251 := by exact prefixLift 2991251
  have htrace : WordTrace (prefixWord ++ tailWord_2991251) baseStart_2991251 baseEnd_2991251 := by
    simpa [prefixWord, tailWord_2991251, baseEnd_2991251] using wordTrace_append hprefix tailTrace_2991251
  have hstable : (prefixWord ++ tailWord_2991251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991251).length < 2 ^ (prefixWord ++ tailWord_2991251).sum := by decide
  have hdescent : baseEnd_2991251 < baseStart_2991251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991264 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_2991264 : Nat := 118140960795 + 2991264 * 2 ^ 59
def prefixEnd_2991264 : Nat := 4983230072969 + 3 ^ 40 * 2991264 * 2
def baseEnd_2991264 : Nat := 1535956196490689899543433

theorem tailTrace_2991264 : CollatzResearch.WordTrace tailWord_2991264 prefixEnd_2991264 1535956196490689899543433 := by
  unfold tailWord_2991264
  simp only [CollatzResearch.WordTrace]
  refine ⟨54550180517584435032046423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72733574023445913376061897 54550180517584435032046423)
  ·
    refine ⟨81825270776376652548069635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54550180517584435032046423 81825270776376652548069635)
    ·
      refine ⟨122737906164564978822104453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81825270776376652548069635 122737906164564978822104453)
      ·
        refine ⟨23013357405855933529144585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122737906164564978822104453 23013357405855933529144585)
        ·
          refine ⟨17260018054391950146858439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23013357405855933529144585 17260018054391950146858439)
          ·
            refine ⟨25890027081587925220287659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17260018054391950146858439 25890027081587925220287659)
            ·
              refine ⟨38835040622381887830431489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25890027081587925220287659 38835040622381887830431489)
              ·
                refine ⟨29126280466786415872823617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38835040622381887830431489 29126280466786415872823617)
                ·
                  refine ⟨21844710350089811904617713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29126280466786415872823617 21844710350089811904617713)
                  ·
                    refine ⟨16383532762567358928463285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21844710350089811904617713 16383532762567358928463285)
                    ·
                      refine ⟨1535956196490689899543433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16383532762567358928463285 1535956196490689899543433)
                      ·
                        rfl

theorem cell23_2991264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_2991264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991264 prefixEnd_2991264 := by exact prefixLift 2991264
  have htrace : WordTrace (prefixWord ++ tailWord_2991264) baseStart_2991264 baseEnd_2991264 := by
    simpa [prefixWord, tailWord_2991264, baseEnd_2991264] using wordTrace_append hprefix tailTrace_2991264
  have hstable : (prefixWord ++ tailWord_2991264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991264).length < 2 ^ (prefixWord ++ tailWord_2991264).sum := by decide
  have hdescent : baseEnd_2991264 < baseStart_2991264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991268 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_2991268 : Nat := 118140960795 + 2991268 * 2 ^ 59
def prefixEnd_2991268 : Nat := 4983230072969 + 3 ^ 40 * 2991268 * 2
def baseEnd_2991268 : Nat := 1535958250413307883893415

theorem tailTrace_2991268 : CollatzResearch.WordTrace tailWord_2991268 prefixEnd_2991268 1535958250413307883893415 := by
  unfold tailWord_2991268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54550253463577189373619229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72733671284769585831492305 54550253463577189373619229)
  ·
    refine ⟨20456345048841446015107211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54550253463577189373619229 20456345048841446015107211)
    ·
      refine ⟨30684517573262169022660817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20456345048841446015107211 30684517573262169022660817)
      ·
        refine ⟨23013388179946626766995613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30684517573262169022660817 23013388179946626766995613)
        ·
          refine ⟨8630020567479985037623355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23013388179946626766995613 8630020567479985037623355)
          ·
            refine ⟨12945030851219977556435033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8630020567479985037623355 12945030851219977556435033)
            ·
              refine ⟨9708773138414983167326275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12945030851219977556435033 9708773138414983167326275)
              ·
                refine ⟨14563159707622474750989413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9708773138414983167326275 14563159707622474750989413)
                ·
                  refine ⟨2730592445179214015810515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14563159707622474750989413 2730592445179214015810515)
                  ·
                    refine ⟨4095888667768821023715773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2730592445179214015810515 4095888667768821023715773)
                    ·
                      refine ⟨1535958250413307883893415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4095888667768821023715773 1535958250413307883893415)
                      ·
                        rfl

theorem cell23_2991268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_2991268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991268 prefixEnd_2991268 := by exact prefixLift 2991268
  have htrace : WordTrace (prefixWord ++ tailWord_2991268) baseStart_2991268 baseEnd_2991268 := by
    simpa [prefixWord, tailWord_2991268, baseEnd_2991268] using wordTrace_append hprefix tailTrace_2991268
  have hstable : (prefixWord ++ tailWord_2991268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991268).length < 2 ^ (prefixWord ++ tailWord_2991268).sum := by decide
  have hdescent : baseEnd_2991268 < baseStart_2991268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991361 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2991361 : Nat := 118140960795 + 2991361 * 2 ^ 59
def prefixEnd_2991361 : Nat := 4983230072969 + 3 ^ 40 * 2991361 * 2
def baseEnd_2991361 : Nat := 512002001371392006676829

theorem tailTrace_2991361 : CollatzResearch.WordTrace tailWord_2991361 prefixEnd_2991361 512002001371392006676829 := by
  unfold tailWord_2991361
  simp only [CollatzResearch.WordTrace]
  refine ⟨109103898915817455630373937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72735932610544970420249291 109103898915817455630373937)
  ·
    refine ⟨81827924186863091722780453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109103898915817455630373937 81827924186863091722780453)
    ·
      refine ⟨15342735785036829698021335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81827924186863091722780453 15342735785036829698021335)
      ·
        refine ⟨23014103677555244547032003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15342735785036829698021335 23014103677555244547032003)
        ·
          refine ⟨34521155516332866820548005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23014103677555244547032003 34521155516332866820548005)
          ·
            refine ⟨6472716659312412528852751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34521155516332866820548005 6472716659312412528852751)
            ·
              refine ⟨9709074988968618793279127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6472716659312412528852751 9709074988968618793279127)
              ·
                refine ⟨14563612483452928189918691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9709074988968618793279127 14563612483452928189918691)
                ·
                  refine ⟨21845418725179392284878037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14563612483452928189918691 21845418725179392284878037)
                  ·
                    refine ⟨512002001371392006676829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21845418725179392284878037 512002001371392006676829)
                    ·
                      rfl

theorem cell23_2991361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2991361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991361 prefixEnd_2991361 := by exact prefixLift 2991361
  have htrace : WordTrace (prefixWord ++ tailWord_2991361) baseStart_2991361 baseEnd_2991361 := by
    simpa [prefixWord, tailWord_2991361, baseEnd_2991361] using wordTrace_append hprefix tailTrace_2991361
  have hstable : (prefixWord ++ tailWord_2991361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991361).length < 2 ^ (prefixWord ++ tailWord_2991361).sum := by decide
  have hdescent : baseEnd_2991361 < baseStart_2991361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991381 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_2991381 : Nat := 118140960795 + 2991381 * 2 ^ 59
def prefixEnd_2991381 : Nat := 4983230072969 + 3 ^ 40 * 2991381 * 2
def baseEnd_2991381 : Nat := 1536016273727265941780395

theorem tailTrace_2991381 : CollatzResearch.WordTrace tailWord_2991381 prefixEnd_2991381 1536016273727265941780395 := by
  unfold tailWord_2991381
  simp only [CollatzResearch.WordTrace]
  refine ⟨109104628375744999046101997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72736418917163332697401331 109104628375744999046101997)
  ·
    refine ⟨40914235640904374642288249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109104628375744999046101997 40914235640904374642288249)
    ·
      refine ⟨30685676730678280981716187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40914235640904374642288249 30685676730678280981716187)
      ·
        refine ⟨46028515096017421472574281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30685676730678280981716187 46028515096017421472574281)
        ·
          refine ⟨34521386322013066104430711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46028515096017421472574281 34521386322013066104430711)
          ·
            refine ⟨51782079483019599156646067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34521386322013066104430711 51782079483019599156646067)
            ·
              refine ⟨77673119224529398734969101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51782079483019599156646067 77673119224529398734969101)
              ·
                refine ⟨29127419709198524525613413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77673119224529398734969101 29127419709198524525613413)
                ·
                  refine ⟨5461391195474723348552515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29127419709198524525613413 5461391195474723348552515)
                  ·
                    refine ⟨8192086793212085022828773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5461391195474723348552515 8192086793212085022828773)
                    ·
                      refine ⟨1536016273727265941780395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8192086793212085022828773 1536016273727265941780395)
                      ·
                        rfl

theorem cell23_2991381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_2991381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991381 prefixEnd_2991381 := by exact prefixLift 2991381
  have htrace : WordTrace (prefixWord ++ tailWord_2991381) baseStart_2991381 baseEnd_2991381 := by
    simpa [prefixWord, tailWord_2991381, baseEnd_2991381] using wordTrace_append hprefix tailTrace_2991381
  have hstable : (prefixWord ++ tailWord_2991381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991381).length < 2 ^ (prefixWord ++ tailWord_2991381).sum := by decide
  have hdescent : baseEnd_2991381 < baseStart_2991381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991418 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_2991418 : Nat := 118140960795 + 2991418 * 2 ^ 59
def prefixEnd_2991418 : Nat := 4983230072969 + 3 ^ 40 * 2991418 * 2
def baseEnd_2991418 : Nat := 1536035272511482297017725

theorem tailTrace_2991418 : CollatzResearch.WordTrace tailWord_2991418 prefixEnd_2991418 1536035272511482297017725 := by
  unfold tailWord_2991418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27276494469152738591299727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72737318584407302910132605 27276494469152738591299727)
  ·
    refine ⟨40914741703729107886949591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27276494469152738591299727 40914741703729107886949591)
    ·
      refine ⟨61372112555593661830424387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40914741703729107886949591 61372112555593661830424387)
      ·
        refine ⟨92058168833390492745636581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61372112555593661830424387 92058168833390492745636581)
        ·
          refine ⟨17260906656260717389806859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92058168833390492745636581 17260906656260717389806859)
          ·
            refine ⟨25891359984391076084710289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17260906656260717389806859 25891359984391076084710289)
            ·
              refine ⟨19418519988293307063532717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25891359984391076084710289 19418519988293307063532717)
              ·
                refine ⟨7281944995609990148824769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19418519988293307063532717 7281944995609990148824769)
                ·
                  refine ⟨5461458746707492611618577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7281944995609990148824769 5461458746707492611618577)
                  ·
                    refine ⟨4096094060030619458713933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5461458746707492611618577 4096094060030619458713933)
                    ·
                      refine ⟨1536035272511482297017725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4096094060030619458713933 1536035272511482297017725)
                      ·
                        rfl

theorem cell23_2991418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_2991418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991418 prefixEnd_2991418 := by exact prefixLift 2991418
  have htrace : WordTrace (prefixWord ++ tailWord_2991418) baseStart_2991418 baseEnd_2991418 := by
    simpa [prefixWord, tailWord_2991418, baseEnd_2991418] using wordTrace_append hprefix tailTrace_2991418
  have hstable : (prefixWord ++ tailWord_2991418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991418).length < 2 ^ (prefixWord ++ tailWord_2991418).sum := by decide
  have hdescent : baseEnd_2991418 < baseStart_2991418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991468 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_2991468 : Nat := 118140960795 + 2991468 * 2 ^ 59
def prefixEnd_2991468 : Nat := 4983230072969 + 3 ^ 40 * 2991468 * 2
def baseEnd_2991468 : Nat := 512020315514735700464165

theorem tailTrace_2991468 : CollatzResearch.WordTrace tailWord_2991468 prefixEnd_2991468 512020315514735700464165 := by
  unfold tailWord_2991468
  simp only [CollatzResearch.WordTrace]
  refine ⟨54553900763214906452259529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72738534350953208603012705 54553900763214906452259529)
  ·
    refine ⟨40915425572411179839194647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54553900763214906452259529 40915425572411179839194647)
    ·
      refine ⟨61373138358616769758791971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40915425572411179839194647 61373138358616769758791971)
      ·
        refine ⟨92059707537925154638187957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61373138358616769758791971 92059707537925154638187957)
        ·
          refine ⟨8630597581680483247330121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92059707537925154638187957 8630597581680483247330121)
          ·
            refine ⟨6472948186260362435497591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8630597581680483247330121 6472948186260362435497591)
            ·
              refine ⟨9709422279390543653246387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6472948186260362435497591 9709422279390543653246387)
              ·
                refine ⟨14564133419085815479869581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9709422279390543653246387 14564133419085815479869581)
                ·
                  refine ⟨5461550032157180804951093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14564133419085815479869581 5461550032157180804951093)
                  ·
                    refine ⟨512020315514735700464165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5461550032157180804951093 512020315514735700464165)
                    ·
                      rfl

theorem cell23_2991468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_2991468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991468 prefixEnd_2991468 := by exact prefixLift 2991468
  have htrace : WordTrace (prefixWord ++ tailWord_2991468) baseStart_2991468 baseEnd_2991468 := by
    simpa [prefixWord, tailWord_2991468, baseEnd_2991468] using wordTrace_append hprefix tailTrace_2991468
  have hstable : (prefixWord ++ tailWord_2991468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991468).length < 2 ^ (prefixWord ++ tailWord_2991468).sum := by decide
  have hdescent : baseEnd_2991468 < baseStart_2991468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991481 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 3, 6]
def baseStart_2991481 : Nat := 118140960795 + 2991481 * 2 ^ 59
def prefixEnd_2991481 : Nat := 4983230072969 + 3 ^ 40 * 2991481 * 2
def baseEnd_2991481 : Nat := 512022540597571850176645

theorem tailTrace_2991481 : CollatzResearch.WordTrace tailWord_2991481 prefixEnd_2991481 512022540597571850176645 := by
  unfold tailWord_2991481
  simp only [CollatzResearch.WordTrace]
  refine ⟨109108275675382716124742297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72738850450255144083161531 109108275675382716124742297)
  ·
    refine ⟨81831206756537037093556723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109108275675382716124742297 81831206756537037093556723)
    ·
      refine ⟨122746810134805555640335085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81831206756537037093556723 122746810134805555640335085)
      ·
        refine ⟨46030053800552083365125657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122746810134805555640335085 46030053800552083365125657)
        ·
          refine ⟨34522540350414062523844243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46030053800552083365125657 34522540350414062523844243)
          ·
            refine ⟨51783810525621093785766365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34522540350414062523844243 51783810525621093785766365)
            ·
              refine ⟨19418928947107910169662387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51783810525621093785766365 19418928947107910169662387)
              ·
                refine ⟨29128393420661865254493581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19418928947107910169662387 29128393420661865254493581)
                ·
                  refine ⟨10923147532748199470435093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29128393420661865254493581 10923147532748199470435093)
                  ·
                    refine ⟨512022540597571850176645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10923147532748199470435093 512022540597571850176645)
                    ·
                      rfl

theorem cell23_2991481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_2991481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991481 prefixEnd_2991481 := by exact prefixLift 2991481
  have htrace : WordTrace (prefixWord ++ tailWord_2991481) baseStart_2991481 baseEnd_2991481 := by
    simpa [prefixWord, tailWord_2991481, baseEnd_2991481] using wordTrace_append hprefix tailTrace_2991481
  have hstable : (prefixWord ++ tailWord_2991481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991481).length < 2 ^ (prefixWord ++ tailWord_2991481).sum := by decide
  have hdescent : baseEnd_2991481 < baseStart_2991481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991485 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2991485 : Nat := 118140960795 + 2991485 * 2 ^ 59
def prefixEnd_2991485 : Nat := 4983230072969 + 3 ^ 40 * 2991485 * 2
def baseEnd_2991485 : Nat := 512023225238444511626639

theorem tailTrace_2991485 : CollatzResearch.WordTrace tailWord_2991485 prefixEnd_2991485 512023225238444511626639 := by
  unfold tailWord_2991485
  simp only [CollatzResearch.WordTrace]
  refine ⟨109108421567368224807887909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72738947711578816538591939 109108421567368224807887909)
  ·
    refine ⟨20457829043881542151478983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109108421567368224807887909 20457829043881542151478983)
    ·
      refine ⟨30686743565822313227218475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20457829043881542151478983 30686743565822313227218475)
      ·
        refine ⟨46030115348733469840827713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30686743565822313227218475 46030115348733469840827713)
        ·
          refine ⟨34522586511550102380620785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46030115348733469840827713 34522586511550102380620785)
          ·
            refine ⟨25891939883662576785465589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34522586511550102380620785 25891939883662576785465589)
            ·
              refine ⟨2427369364093366573637399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25891939883662576785465589 2427369364093366573637399)
              ·
                refine ⟨3641054046140049860456099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427369364093366573637399 3641054046140049860456099)
                ·
                  refine ⟨5461581069210074790684149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641054046140049860456099 5461581069210074790684149)
                  ·
                    refine ⟨512023225238444511626639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5461581069210074790684149 512023225238444511626639)
                    ·
                      rfl

theorem cell23_2991485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2991485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991485 prefixEnd_2991485 := by exact prefixLift 2991485
  have htrace : WordTrace (prefixWord ++ tailWord_2991485) baseStart_2991485 baseEnd_2991485 := by
    simpa [prefixWord, tailWord_2991485, baseEnd_2991485] using wordTrace_append hprefix tailTrace_2991485
  have hstable : (prefixWord ++ tailWord_2991485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991485).length < 2 ^ (prefixWord ++ tailWord_2991485).sum := by decide
  have hdescent : baseEnd_2991485 < baseStart_2991485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991488 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 4]
def baseStart_2991488 : Nat := 118140960795 + 2991488 * 2 ^ 59
def prefixEnd_2991488 : Nat := 4983230072969 + 3 ^ 40 * 2991488 * 2
def baseEnd_2991488 : Nat := 1536071216157297023142403

theorem tailTrace_2991488 : CollatzResearch.WordTrace tailWord_2991488 prefixEnd_2991488 1536071216157297023142403 := by
  unfold tailWord_2991488
  simp only [CollatzResearch.WordTrace]
  refine ⟨54554265493178678160123559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72739020657571570880164745 54554265493178678160123559)
  ·
    refine ⟨81831398239768017240185339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54554265493178678160123559 81831398239768017240185339)
    ·
      refine ⟨122747097359652025860278009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81831398239768017240185339 122747097359652025860278009)
      ·
        refine ⟨92060323019739019395208507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122747097359652025860278009 92060323019739019395208507)
        ·
          refine ⟨138090484529608529092812761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92060323019739019395208507 138090484529608529092812761)
          ·
            refine ⟨103567863397206396819609571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138090484529608529092812761 103567863397206396819609571)
            ·
              refine ⟨155351795095809595229414357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103567863397206396819609571 155351795095809595229414357)
              ·
                refine ⟨3641057697558037388189399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 155351795095809595229414357 3641057697558037388189399)
                ·
                  refine ⟨5461586546337056082284099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641057697558037388189399 5461586546337056082284099)
                  ·
                    refine ⟨8192379819505584123426149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5461586546337056082284099 8192379819505584123426149)
                    ·
                      refine ⟨1536071216157297023142403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8192379819505584123426149 1536071216157297023142403)
                      ·
                        rfl

theorem cell23_2991488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_2991488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991488 prefixEnd_2991488 := by exact prefixLift 2991488
  have htrace : WordTrace (prefixWord ++ tailWord_2991488) baseStart_2991488 baseEnd_2991488 := by
    simpa [prefixWord, tailWord_2991488, baseEnd_2991488] using wordTrace_append hprefix tailTrace_2991488
  have hstable : (prefixWord ++ tailWord_2991488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991488).length < 2 ^ (prefixWord ++ tailWord_2991488).sum := by decide
  have hdescent : baseEnd_2991488 < baseStart_2991488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991522 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_2991522 : Nat := 118140960795 + 2991522 * 2 ^ 59
def prefixEnd_2991522 : Nat := 4983230072969 + 3 ^ 40 * 2991522 * 2
def baseEnd_2991522 : Nat := 1536088674499549890117247

theorem tailTrace_2991522 : CollatzResearch.WordTrace tailWord_2991522 prefixEnd_2991522 1536088674499549890117247 := by
  unfold tailWord_2991522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27277442767058545031746205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72739847378822786751323213 27277442767058545031746205)
  ·
    refine ⟨10229041037646954386904827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27277442767058545031746205 10229041037646954386904827)
    ·
      refine ⟨15343561556470431580357241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10229041037646954386904827 15343561556470431580357241)
      ·
        refine ⟨11507671167352823685267931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15343561556470431580357241 11507671167352823685267931)
        ·
          refine ⟨17261506751029235527901897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11507671167352823685267931 17261506751029235527901897)
          ·
            refine ⟨12946130063271926645926423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17261506751029235527901897 12946130063271926645926423)
            ·
              refine ⟨19419195094907889968889635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12946130063271926645926423 19419195094907889968889635)
              ·
                refine ⟨29128792642361834953334453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19419195094907889968889635 29128792642361834953334453)
                ·
                  refine ⟨2730824310221422026875105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29128792642361834953334453 2730824310221422026875105)
                  ·
                    refine ⟨2048118232666066520156329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2730824310221422026875105 2048118232666066520156329)
                    ·
                      refine ⟨1536088674499549890117247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048118232666066520156329 1536088674499549890117247)
                      ·
                        rfl

theorem cell23_2991522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_2991522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991522 prefixEnd_2991522 := by exact prefixLift 2991522
  have htrace : WordTrace (prefixWord ++ tailWord_2991522) baseStart_2991522 baseEnd_2991522 := by
    simpa [prefixWord, tailWord_2991522, baseEnd_2991522] using wordTrace_append hprefix tailTrace_2991522
  have hstable : (prefixWord ++ tailWord_2991522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991522).length < 2 ^ (prefixWord ++ tailWord_2991522).sum := by decide
  have hdescent : baseEnd_2991522 < baseStart_2991522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991538 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_2991538 : Nat := 118140960795 + 2991538 * 2 ^ 59
def prefixEnd_2991538 : Nat := 4983230072969 + 3 ^ 40 * 2991538 * 2
def baseEnd_2991538 : Nat := 1536096890190021827517173

theorem tailTrace_2991538 : CollatzResearch.WordTrace tailWord_2991538 prefixEnd_2991538 1536096890190021827517173 := by
  unfold tailWord_2991538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27277588659044053714891817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72740236424117476573044845 27277588659044053714891817)
  ·
    refine ⟨20458191494283040286168863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27277588659044053714891817 20458191494283040286168863)
    ·
      refine ⟨30687287241424560429253295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20458191494283040286168863 30687287241424560429253295)
      ·
        refine ⟨46030930862136840643879943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30687287241424560429253295 46030930862136840643879943)
        ·
          refine ⟨69046396293205260965819915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46030930862136840643879943 69046396293205260965819915)
          ·
            refine ⟨103569594439807891448729873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69046396293205260965819915 103569594439807891448729873)
            ·
              refine ⟨77677195829855918586547405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103569594439807891448729873 77677195829855918586547405)
              ·
                refine ⟨29128948436195969469955277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77677195829855918586547405 29128948436195969469955277)
                ·
                  refine ⟨10923355663573488551233229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29128948436195969469955277 10923355663573488551233229)
                  ·
                    refine ⟨4096258373840058206712461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10923355663573488551233229 4096258373840058206712461)
                    ·
                      refine ⟨1536096890190021827517173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4096258373840058206712461 1536096890190021827517173)
                      ·
                        rfl

theorem cell23_2991538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_2991538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991538 prefixEnd_2991538 := by exact prefixLift 2991538
  have htrace : WordTrace (prefixWord ++ tailWord_2991538) baseStart_2991538 baseEnd_2991538 := by
    simpa [prefixWord, tailWord_2991538, baseEnd_2991538] using wordTrace_append hprefix tailTrace_2991538
  have hstable : (prefixWord ++ tailWord_2991538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991538).length < 2 ^ (prefixWord ++ tailWord_2991538).sum := by decide
  have hdescent : baseEnd_2991538 < baseStart_2991538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991556 : List Nat := [2, 3, 3, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_2991556 : Nat := 118140960795 + 2991556 * 2 ^ 59
def prefixEnd_2991556 : Nat := 4983230072969 + 3 ^ 40 * 2991556 * 2
def baseEnd_2991556 : Nat := 1536106132841802757092091

theorem tailTrace_2991556 : CollatzResearch.WordTrace tailWord_2991556 prefixEnd_2991556 1536106132841802757092091 := by
  unfold tailWord_2991556
  simp only [CollatzResearch.WordTrace]
  refine ⟨54555505575055501966861261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72740674100074002622481681 54555505575055501966861261)
  ·
    refine ⟨20458314590645813237572973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54555505575055501966861261 20458314590645813237572973)
    ·
      refine ⟨7671867971492179964089865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20458314590645813237572973 7671867971492179964089865)
      ·
        refine ⟨5753900978619134973067399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7671867971492179964089865 5753900978619134973067399)
        ·
          refine ⟨8630851467928702459601099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5753900978619134973067399 8630851467928702459601099)
          ·
            refine ⟨12946277201893053689401649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8630851467928702459601099 12946277201893053689401649)
            ·
              refine ⟨9709707901419790267051237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12946277201893053689401649 9709707901419790267051237)
              ·
                refine ⟨1820570231516210675072107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9709707901419790267051237 1820570231516210675072107)
                ·
                  refine ⟨2730855347274316012608161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820570231516210675072107 2730855347274316012608161)
                  ·
                    refine ⟨2048141510455737009456121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2730855347274316012608161 2048141510455737009456121)
                    ·
                      refine ⟨1536106132841802757092091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048141510455737009456121 1536106132841802757092091)
                      ·
                        rfl

theorem cell23_2991556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_2991556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991556 prefixEnd_2991556 := by exact prefixLift 2991556
  have htrace : WordTrace (prefixWord ++ tailWord_2991556) baseStart_2991556 baseEnd_2991556 := by
    simpa [prefixWord, tailWord_2991556, baseEnd_2991556] using wordTrace_append hprefix tailTrace_2991556
  have hstable : (prefixWord ++ tailWord_2991556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991556).length < 2 ^ (prefixWord ++ tailWord_2991556).sum := by decide
  have hdescent : baseEnd_2991556 < baseStart_2991556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991612 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_2991612 : Nat := 118140960795 + 2991612 * 2 ^ 59
def prefixEnd_2991612 : Nat := 4983230072969 + 3 ^ 40 * 2991612 * 2
def baseEnd_2991612 : Nat := 1536134887758454537991833

theorem tailTrace_2991612 : CollatzResearch.WordTrace tailWord_2991612 prefixEnd_2991612 1536134887758454537991833 := by
  unfold tailWord_2991612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54556526818954062748880545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72742035758605416998507393 54556526818954062748880545)
  ·
    refine ⟨40917395114215547061660409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54556526818954062748880545 40917395114215547061660409)
    ·
      refine ⟨30688046335661660296245307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40917395114215547061660409 30688046335661660296245307)
      ·
        refine ⟨46032069503492490444367961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30688046335661660296245307 46032069503492490444367961)
        ·
          refine ⟨34524052127619367833275971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46032069503492490444367961 34524052127619367833275971)
          ·
            refine ⟨51786078191429051749913957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34524052127619367833275971 51786078191429051749913957)
            ·
              refine ⟨9709889660892947203108867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51786078191429051749913957 9709889660892947203108867)
              ·
                refine ⟨14564834491339420804663301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9709889660892947203108867 14564834491339420804663301)
                ·
                  refine ⟨2730906467126141400874369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14564834491339420804663301 2730906467126141400874369)
                  ·
                    refine ⟨2048179850344606050655777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2730906467126141400874369 2048179850344606050655777)
                    ·
                      refine ⟨1536134887758454537991833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048179850344606050655777 1536134887758454537991833)
                      ·
                        rfl

theorem cell23_2991612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_2991612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991612 prefixEnd_2991612 := by exact prefixLift 2991612
  have htrace : WordTrace (prefixWord ++ tailWord_2991612) baseStart_2991612 baseEnd_2991612 := by
    simpa [prefixWord, tailWord_2991612, baseEnd_2991612] using wordTrace_append hprefix tailTrace_2991612
  have hstable : (prefixWord ++ tailWord_2991612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991612).length < 2 ^ (prefixWord ++ tailWord_2991612).sum := by decide
  have hdescent : baseEnd_2991612 < baseStart_2991612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991669 : List Nat := [1, 3, 3, 1, 1, 5, 2, 2, 5]
def baseStart_2991669 : Nat := 118140960795 + 2991669 * 2 ^ 59
def prefixEnd_2991669 : Nat := 4983230072969 + 3 ^ 40 * 2991669 * 2
def baseEnd_2991669 : Nat := 170684906239528979442119

theorem tailTrace_2991669 : CollatzResearch.WordTrace tailWord_2991669 prefixEnd_2991669 170684906239528979442119 := by
  unfold tailWord_2991669
  simp only [CollatzResearch.WordTrace]
  refine ⟨109115132598701624232586061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72743421732467749488390707 109115132598701624232586061)
  ·
    refine ⟨40918174724513109087219773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109115132598701624232586061 40918174724513109087219773)
    ·
      refine ⟨15344315521692415907707415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40918174724513109087219773 15344315521692415907707415)
      ·
        refine ⟨23016473282538623861561123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15344315521692415907707415 23016473282538623861561123)
        ·
          refine ⟨34524709923807935792341685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23016473282538623861561123 34524709923807935792341685)
          ·
            refine ⟨3236691555356993980532033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34524709923807935792341685 3236691555356993980532033)
            ·
              refine ⟨2427518666517745485399025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236691555356993980532033 2427518666517745485399025)
              ·
                refine ⟨1820638999888309114049269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2427518666517745485399025 1820638999888309114049269)
                ·
                  refine ⟨170684906239528979442119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1820638999888309114049269 170684906239528979442119)
                  ·
                    rfl

theorem cell23_2991669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_2991669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991669 prefixEnd_2991669 := by exact prefixLift 2991669
  have htrace : WordTrace (prefixWord ++ tailWord_2991669) baseStart_2991669 baseEnd_2991669 := by
    simpa [prefixWord, tailWord_2991669, baseEnd_2991669] using wordTrace_append hprefix tailTrace_2991669
  have hstable : (prefixWord ++ tailWord_2991669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991669).length < 2 ^ (prefixWord ++ tailWord_2991669).sum := by decide
  have hdescent : baseEnd_2991669 < baseStart_2991669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991738 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_2991738 : Nat := 118140960795 + 2991738 * 2 ^ 59
def prefixEnd_2991738 : Nat := 4983230072969 + 3 ^ 40 * 2991738 * 2
def baseEnd_2991738 : Nat := 512066528773640348338751

theorem tailTrace_2991738 : CollatzResearch.WordTrace tailWord_2991738 prefixEnd_2991738 512066528773640348338751 := by
  unfold tailWord_2991738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27279412308862912254211967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72745099490301099344565245 27279412308862912254211967)
  ·
    refine ⟨40919118463294368381317951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27279412308862912254211967 40919118463294368381317951)
    ·
      refine ⟨61378677694941552571976927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40919118463294368381317951 61378677694941552571976927)
      ·
        refine ⟨92068016542412328857965391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61378677694941552571976927 92068016542412328857965391)
        ·
          refine ⟨138102024813618493286948087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92068016542412328857965391 138102024813618493286948087)
          ·
            refine ⟨207153037220427739930422131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138102024813618493286948087 207153037220427739930422131)
            ·
              refine ⟨310729555830641609895633197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207153037220427739930422131 310729555830641609895633197)
              ·
                refine ⟨116523583436490603710862449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310729555830641609895633197 116523583436490603710862449)
                ·
                  refine ⟨87392687577367952783146837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116523583436490603710862449 87392687577367952783146837)
                  ·
                    refine ⟨512066528773640348338751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87392687577367952783146837 512066528773640348338751)
                    ·
                      rfl

theorem cell23_2991738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_2991738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991738 prefixEnd_2991738 := by exact prefixLift 2991738
  have htrace : WordTrace (prefixWord ++ tailWord_2991738) baseStart_2991738 baseEnd_2991738 := by
    simpa [prefixWord, tailWord_2991738, baseEnd_2991738] using wordTrace_append hprefix tailTrace_2991738
  have hstable : (prefixWord ++ tailWord_2991738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991738).length < 2 ^ (prefixWord ++ tailWord_2991738).sum := by decide
  have hdescent : baseEnd_2991738 < baseStart_2991738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991769 : List Nat := [1, 2, 1, 2, 1, 2, 2, 7, 1, 1, 3]
def baseStart_2991769 : Nat := 118140960795 + 2991769 * 2 ^ 59
def prefixEnd_2991769 : Nat := 4983230072969 + 3 ^ 40 * 2991769 * 2
def baseEnd_2991769 : Nat := 1536215504221210423728611

theorem tailTrace_2991769 : CollatzResearch.WordTrace tailWord_2991769 prefixEnd_2991769 1536215504221210423728611 := by
  unfold tailWord_2991769
  simp only [CollatzResearch.WordTrace]
  refine ⟨109118779898339341311226361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72745853265559560874150907 109118779898339341311226361)
  ·
    refine ⟨81839084923754505983419771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109118779898339341311226361 81839084923754505983419771)
    ·
      refine ⟨122758627385631758975129657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81839084923754505983419771 122758627385631758975129657)
      ·
        refine ⟨92068970539223819231347243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122758627385631758975129657 92068970539223819231347243)
        ·
          refine ⟨138103455808835728847020865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92068970539223819231347243 138103455808835728847020865)
          ·
            refine ⟨103577591856626796635265649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138103455808835728847020865 103577591856626796635265649)
            ·
              refine ⟨77683193892470097476449237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103577591856626796635265649 77683193892470097476449237)
              ·
                refine ⟨1820699856854767909604279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77683193892470097476449237 1820699856854767909604279)
                ·
                  refine ⟨2731049785282151864406419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820699856854767909604279 2731049785282151864406419)
                  ·
                    refine ⟨4096574677923227796609629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2731049785282151864406419 4096574677923227796609629)
                    ·
                      refine ⟨1536215504221210423728611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4096574677923227796609629 1536215504221210423728611)
                      ·
                        rfl

theorem cell23_2991769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_2991769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991769 prefixEnd_2991769 := by exact prefixLift 2991769
  have htrace : WordTrace (prefixWord ++ tailWord_2991769) baseStart_2991769 baseEnd_2991769 := by
    simpa [prefixWord, tailWord_2991769, baseEnd_2991769] using wordTrace_append hprefix tailTrace_2991769
  have hstable : (prefixWord ++ tailWord_2991769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991769).length < 2 ^ (prefixWord ++ tailWord_2991769).sum := by decide
  have hdescent : baseEnd_2991769 < baseStart_2991769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991785 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 8, 4]
def baseStart_2991785 : Nat := 118140960795 + 2991785 * 2 ^ 59
def prefixEnd_2991785 : Nat := 4983230072969 + 3 ^ 40 * 2991785 * 2
def baseEnd_2991785 : Nat := 512074573303894120376179

theorem tailTrace_2991785 : CollatzResearch.WordTrace tailWord_2991785 prefixEnd_2991785 512074573303894120376179 := by
  unfold tailWord_2991785
  simp only [CollatzResearch.WordTrace]
  refine ⟨109119363466281376043808809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72746242310854250695872539 109119363466281376043808809)
  ·
    refine ⟨81839522599711032032856607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109119363466281376043808809 81839522599711032032856607)
    ·
      refine ⟨122759283899566548049284911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81839522599711032032856607 122759283899566548049284911)
      ·
        refine ⟨184138925849349822073927367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122759283899566548049284911 184138925849349822073927367)
        ·
          refine ⟨276208388774024733110891051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184138925849349822073927367 276208388774024733110891051)
          ·
            refine ⟨414312583161037099666336577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276208388774024733110891051 414312583161037099666336577)
            ·
              refine ⟨310734437370777824749752433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414312583161037099666336577 310734437370777824749752433)
              ·
                refine ⟨233050828028083368562314325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310734437370777824749752433 233050828028083368562314325)
                ·
                  refine ⟨2731064390954101975339621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 233050828028083368562314325 2731064390954101975339621)
                  ·
                    refine ⟨512074573303894120376179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2731064390954101975339621 512074573303894120376179)
                    ·
                      rfl

theorem cell23_2991785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 4].length) (baseStart_2991785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991785 prefixEnd_2991785 := by exact prefixLift 2991785
  have htrace : WordTrace (prefixWord ++ tailWord_2991785) baseStart_2991785 baseEnd_2991785 := by
    simpa [prefixWord, tailWord_2991785, baseEnd_2991785] using wordTrace_append hprefix tailTrace_2991785
  have hstable : (prefixWord ++ tailWord_2991785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991785).length < 2 ^ (prefixWord ++ tailWord_2991785).sum := by decide
  have hdescent : baseEnd_2991785 < baseStart_2991785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991795 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 5]
def baseStart_2991795 : Nat := 118140960795 + 2991795 * 2 ^ 59
def prefixEnd_2991795 : Nat := 4983230072969 + 3 ^ 40 * 2991795 * 2
def baseEnd_2991795 : Nat := 1536228854718227322003491

theorem tailTrace_2991795 : CollatzResearch.WordTrace tailWord_2991795 prefixEnd_2991795 1536228854718227322003491 := by
  unfold tailWord_2991795
  simp only [CollatzResearch.WordTrace]
  refine ⟨109119728196245147751672839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72746485464163431834448559 109119728196245147751672839)
  ·
    refine ⟨163679592294367721627509259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109119728196245147751672839 163679592294367721627509259)
    ·
      refine ⟨245519388441551582441263889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163679592294367721627509259 245519388441551582441263889)
      ·
        refine ⟨184139541331163686830947917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245519388441551582441263889 184139541331163686830947917)
        ·
          refine ⟨69052327999186382561605469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184139541331163686830947917 69052327999186382561605469)
          ·
            refine ⟨25894622999694893460602051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69052327999186382561605469 25894622999694893460602051)
            ·
              refine ⟨38841934499542340190903077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25894622999694893460602051 38841934499542340190903077)
              ·
                refine ⟨7282862718664188785794327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38841934499542340190903077 7282862718664188785794327)
                ·
                  refine ⟨10924294077996283178691491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7282862718664188785794327 10924294077996283178691491)
                  ·
                    refine ⟨16386441116994424768037237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10924294077996283178691491 16386441116994424768037237)
                    ·
                      refine ⟨1536228854718227322003491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16386441116994424768037237 1536228854718227322003491)
                      ·
                        rfl

theorem cell23_2991795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_2991795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991795 prefixEnd_2991795 := by exact prefixLift 2991795
  have htrace : WordTrace (prefixWord ++ tailWord_2991795) baseStart_2991795 baseEnd_2991795 := by
    simpa [prefixWord, tailWord_2991795, baseEnd_2991795] using wordTrace_append hprefix tailTrace_2991795
  have hstable : (prefixWord ++ tailWord_2991795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991795).length < 2 ^ (prefixWord ++ tailWord_2991795).sum := by decide
  have hdescent : baseEnd_2991795 < baseStart_2991795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991805 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2991805 : Nat := 118140960795 + 2991805 * 2 ^ 59
def prefixEnd_2991805 : Nat := 4983230072969 + 3 ^ 40 * 2991805 * 2
def baseEnd_2991805 : Nat := 1536233989524772282878445

theorem tailTrace_2991805 : CollatzResearch.WordTrace tailWord_2991805 prefixEnd_2991805 1536233989524772282878445 := by
  unfold tailWord_2991805
  simp only [CollatzResearch.WordTrace]
  refine ⟨109120092926208919459536869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72746728617472612973024579 109120092926208919459536869)
  ·
    refine ⟨20460017423664172398663163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109120092926208919459536869 20460017423664172398663163)
    ·
      refine ⟨30690026135496258597994745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20460017423664172398663163 30690026135496258597994745)
      ·
        refine ⟨23017519601622193948496059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30690026135496258597994745 23017519601622193948496059)
        ·
          refine ⟨34526279402433290922744089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23017519601622193948496059 34526279402433290922744089)
          ·
            refine ⟨25894709551824968192058067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34526279402433290922744089 25894709551824968192058067)
            ·
              refine ⟨38842064327737452288087101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25894709551824968192058067 38842064327737452288087101)
              ·
                refine ⟨14565774122901544608032663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38842064327737452288087101 14565774122901544608032663)
                ·
                  refine ⟨21848661184352316912048995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14565774122901544608032663 21848661184352316912048995)
                  ·
                    refine ⟨32772991776528475368073493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21848661184352316912048995 32772991776528475368073493)
                    ·
                      refine ⟨1536233989524772282878445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32772991776528475368073493 1536233989524772282878445)
                      ·
                        rfl

theorem cell23_2991805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2991805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991805 prefixEnd_2991805 := by exact prefixLift 2991805
  have htrace : WordTrace (prefixWord ++ tailWord_2991805) baseStart_2991805 baseEnd_2991805 := by
    simpa [prefixWord, tailWord_2991805, baseEnd_2991805] using wordTrace_append hprefix tailTrace_2991805
  have hstable : (prefixWord ++ tailWord_2991805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991805).length < 2 ^ (prefixWord ++ tailWord_2991805).sum := by decide
  have hdescent : baseEnd_2991805 < baseStart_2991805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991822 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2991822 : Nat := 118140960795 + 2991822 * 2 ^ 59
def prefixEnd_2991822 : Nat := 4983230072969 + 3 ^ 40 * 2991822 * 2
def baseEnd_2991822 : Nat := 1536242718695898716365867

theorem tailTrace_2991822 : CollatzResearch.WordTrace tailWord_2991822 prefixEnd_2991822 1536242718695898716365867 := by
  unfold tailWord_2991822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13640089120893416420363215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72747141978098220908603813 13640089120893416420363215)
  ·
    refine ⟨20460133681340124630544823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13640089120893416420363215 20460133681340124630544823)
    ·
      refine ⟨30690200522010186945817235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20460133681340124630544823 30690200522010186945817235)
      ·
        refine ⟨46035300783015280418725853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30690200522010186945817235 46035300783015280418725853)
        ·
          refine ⟨17263237793630730157022195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46035300783015280418725853 17263237793630730157022195)
          ·
            refine ⟨25894856690446095235533293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17263237793630730157022195 25894856690446095235533293)
            ·
              refine ⟨9710571258917285713324985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25894856690446095235533293 9710571258917285713324985)
              ·
                refine ⟨7282928444187964284993739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9710571258917285713324985 7282928444187964284993739)
                ·
                  refine ⟨10924392666281946427490609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7282928444187964284993739 10924392666281946427490609)
                  ·
                    refine ⟨8193294499711459820617957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10924392666281946427490609 8193294499711459820617957)
                    ·
                      refine ⟨1536242718695898716365867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8193294499711459820617957 1536242718695898716365867)
                      ·
                        rfl

theorem cell23_2991822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2991822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991822 prefixEnd_2991822 := by exact prefixLift 2991822
  have htrace : WordTrace (prefixWord ++ tailWord_2991822) baseStart_2991822 baseEnd_2991822 := by
    simpa [prefixWord, tailWord_2991822, baseEnd_2991822] using wordTrace_append hprefix tailTrace_2991822
  have hstable : (prefixWord ++ tailWord_2991822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991822).length < 2 ^ (prefixWord ++ tailWord_2991822).sum := by decide
  have hdescent : baseEnd_2991822 < baseStart_2991822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991826 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_2991826 : Nat := 118140960795 + 2991826 * 2 ^ 59
def prefixEnd_2991826 : Nat := 4983230072969 + 3 ^ 40 * 2991826 * 2
def baseEnd_2991826 : Nat := 1536244772618516700715849

theorem tailTrace_2991826 : CollatzResearch.WordTrace tailWord_2991826 prefixEnd_2991826 1536244772618516700715849 := by
  unfold tailWord_2991826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27280214714783210011512833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72747239239421893364034221 27280214714783210011512833)
  ·
    refine ⟨20460161036087407508634625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27280214714783210011512833 20460161036087407508634625)
    ·
      refine ⟨15345120777065555631475969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20460161036087407508634625 15345120777065555631475969)
      ·
        refine ⟨11508840582799166723606977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15345120777065555631475969 11508840582799166723606977)
        ·
          refine ⟨8631630437099375042705233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11508840582799166723606977 8631630437099375042705233)
          ·
            refine ⟨6473722827824531282028925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8631630437099375042705233 6473722827824531282028925)
            ·
              refine ⟨2427646060434199230760847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6473722827824531282028925 2427646060434199230760847)
              ·
                refine ⟨3641469090651298846141271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427646060434199230760847 3641469090651298846141271)
                ·
                  refine ⟨5462203635976948269211907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641469090651298846141271 5462203635976948269211907)
                  ·
                    refine ⟨8193305453965422403817861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5462203635976948269211907 8193305453965422403817861)
                    ·
                      refine ⟨1536244772618516700715849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8193305453965422403817861 1536244772618516700715849)
                      ·
                        rfl

theorem cell23_2991826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_2991826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991826 prefixEnd_2991826 := by exact prefixLift 2991826
  have htrace : WordTrace (prefixWord ++ tailWord_2991826) baseStart_2991826 baseEnd_2991826 := by
    simpa [prefixWord, tailWord_2991826, baseEnd_2991826] using wordTrace_append hprefix tailTrace_2991826
  have hstable : (prefixWord ++ tailWord_2991826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991826).length < 2 ^ (prefixWord ++ tailWord_2991826).sum := by decide
  have hdescent : baseEnd_2991826 < baseStart_2991826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991837 : List Nat := [1, 4, 3, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2991837 : Nat := 118140960795 + 2991837 * 2 ^ 59
def prefixEnd_2991837 : Nat := 4983230072969 + 3 ^ 40 * 2991837 * 2
def baseEnd_2991837 : Nat := 1536250420905716157678299

theorem tailTrace_2991837 : CollatzResearch.WordTrace tailWord_2991837 prefixEnd_2991837 1536250420905716157678299 := by
  unfold tailWord_2991837
  simp only [CollatzResearch.WordTrace]
  refine ⟨109121260062092988924701765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72747506708061992616467843 109121260062092988924701765)
  ·
    refine ⟨20460236261642435423381581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109121260062092988924701765 20460236261642435423381581)
    ·
      refine ⟨7672588598115913283768093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20460236261642435423381581 7672588598115913283768093)
      ·
        refine ⟨2877220724293467481413035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7672588598115913283768093 2877220724293467481413035)
        ·
          refine ⟨4315831086440201222119553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877220724293467481413035 4315831086440201222119553)
          ·
            refine ⟨3236873314830150916589665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4315831086440201222119553 3236873314830150916589665)
            ·
              refine ⟨2427654986122613187442249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236873314830150916589665 2427654986122613187442249)
              ·
                refine ⟨1820741239591959890581687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2427654986122613187442249 1820741239591959890581687)
                ·
                  refine ⟨2731111859387939835872531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820741239591959890581687 2731111859387939835872531)
                  ·
                    refine ⟨4096667789081909753808797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2731111859387939835872531 4096667789081909753808797)
                    ·
                      refine ⟨1536250420905716157678299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4096667789081909753808797 1536250420905716157678299)
                      ·
                        rfl

theorem cell23_2991837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2991837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991837 prefixEnd_2991837 := by exact prefixLift 2991837
  have htrace : WordTrace (prefixWord ++ tailWord_2991837) baseStart_2991837 baseEnd_2991837 := by
    simpa [prefixWord, tailWord_2991837, baseEnd_2991837] using wordTrace_append hprefix tailTrace_2991837
  have hstable : (prefixWord ++ tailWord_2991837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991837).length < 2 ^ (prefixWord ++ tailWord_2991837).sum := by decide
  have hdescent : baseEnd_2991837 < baseStart_2991837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991845 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_2991845 : Nat := 118140960795 + 2991845 * 2 ^ 59
def prefixEnd_2991845 : Nat := 4983230072969 + 3 ^ 40 * 2991845 * 2
def baseEnd_2991845 : Nat := 512084842916984042126087

theorem tailTrace_2991845 : CollatzResearch.WordTrace tailWord_2991845 prefixEnd_2991845 512084842916984042126087 := by
  unfold tailWord_2991845
  simp only [CollatzResearch.WordTrace]
  refine ⟨109121551846064006290992989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72747701230709337527328659 109121551846064006290992989)
  ·
    refine ⟨40920581942274002359122371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109121551846064006290992989 40920581942274002359122371)
    ·
      refine ⟨61380872913411003538683557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40920581942274002359122371 61380872913411003538683557)
      ·
        refine ⟨11508913671264563163503167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61380872913411003538683557 11508913671264563163503167)
        ·
          refine ⟨17263370506896844745254751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11508913671264563163503167 17263370506896844745254751)
          ·
            refine ⟨25895055760345267117882127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17263370506896844745254751 25895055760345267117882127)
            ·
              refine ⟨38842583640517900676823191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25895055760345267117882127 38842583640517900676823191)
              ·
                refine ⟨58263875460776851015234787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38842583640517900676823191 58263875460776851015234787)
                ·
                  refine ⟨87395813191165276522852181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58263875460776851015234787 87395813191165276522852181)
                  ·
                    refine ⟨512084842916984042126087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87395813191165276522852181 512084842916984042126087)
                    ·
                      rfl

theorem cell23_2991845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_2991845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991845 prefixEnd_2991845 := by exact prefixLift 2991845
  have htrace : WordTrace (prefixWord ++ tailWord_2991845) baseStart_2991845 baseEnd_2991845 := by
    simpa [prefixWord, tailWord_2991845, baseEnd_2991845] using wordTrace_append hprefix tailTrace_2991845
  have hstable : (prefixWord ++ tailWord_2991845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991845).length < 2 ^ (prefixWord ++ tailWord_2991845).sum := by decide
  have hdescent : baseEnd_2991845 < baseStart_2991845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991859 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 3]
def baseStart_2991859 : Nat := 118140960795 + 2991859 * 2 ^ 59
def prefixEnd_2991859 : Nat := 4983230072969 + 3 ^ 40 * 2991859 * 2
def baseEnd_2991859 : Nat := 1536261717480115071603197

theorem tailTrace_2991859 : CollatzResearch.WordTrace tailWord_2991859 prefixEnd_2991859 1536261717480115071603197 := by
  unfold tailWord_2991859
  simp only [CollatzResearch.WordTrace]
  refine ⟨109122062468013286682002631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72748041645342191121335087 109122062468013286682002631)
  ·
    refine ⟨163683093702019930023003947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109122062468013286682002631 163683093702019930023003947)
    ·
      refine ⟨245524640553029895034505921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163683093702019930023003947 245524640553029895034505921)
      ·
        refine ⟨184143480414772421275879441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245524640553029895034505921 184143480414772421275879441)
        ·
          refine ⟨138107610311079315956909581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184143480414772421275879441 138107610311079315956909581)
          ·
            refine ⟨51790353866654743483841093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138107610311079315956909581 51790353866654743483841093)
            ·
              refine ⟨9710691349997764403220205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51790353866654743483841093 9710691349997764403220205)
              ·
                refine ⟨3641509256249161651207577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9710691349997764403220205 3641509256249161651207577)
                ·
                  refine ⟨2731131942186871238405683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3641509256249161651207577 2731131942186871238405683)
                  ·
                    refine ⟨4096697913280306857608525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2731131942186871238405683 4096697913280306857608525)
                    ·
                      refine ⟨1536261717480115071603197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4096697913280306857608525 1536261717480115071603197)
                      ·
                        rfl

theorem cell23_2991859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 3].length) (baseStart_2991859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991859 prefixEnd_2991859 := by exact prefixLift 2991859
  have htrace : WordTrace (prefixWord ++ tailWord_2991859) baseStart_2991859 baseEnd_2991859 := by
    simpa [prefixWord, tailWord_2991859, baseEnd_2991859] using wordTrace_append hprefix tailTrace_2991859
  have hstable : (prefixWord ++ tailWord_2991859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991859).length < 2 ^ (prefixWord ++ tailWord_2991859).sum := by decide
  have hdescent : baseEnd_2991859 < baseStart_2991859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991860 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2991860 : Nat := 118140960795 + 2991860 * 2 ^ 59
def prefixEnd_2991860 : Nat := 4983230072969 + 3 ^ 40 * 2991860 * 2
def baseEnd_2991860 : Nat := 1536262230960769567690693

theorem tailTrace_2991860 : CollatzResearch.WordTrace tailWord_2991860 prefixEnd_2991860 1536262230960769567690693 := by
  unfold tailWord_2991860
  simp only [CollatzResearch.WordTrace]
  refine ⟨54561049470504831926394517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72748065960673109235192689 54561049470504831926394517)
  ·
    refine ⟨2557549193929913996549743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54561049470504831926394517 2557549193929913996549743)
    ·
      refine ⟨3836323790894870994824615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557549193929913996549743 3836323790894870994824615)
      ·
        refine ⟨5754485686342306492236923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3836323790894870994824615 5754485686342306492236923)
        ·
          refine ⟨8631728529513459738355385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5754485686342306492236923 8631728529513459738355385)
          ·
            refine ⟨6473796397135094803766539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8631728529513459738355385 6473796397135094803766539)
            ·
              refine ⟨9710694595702642205649809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6473796397135094803766539 9710694595702642205649809)
              ·
                refine ⟨7283020946776981654237357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9710694595702642205649809 7283020946776981654237357)
                ·
                  refine ⟨2731132855041368120339009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7283020946776981654237357 2731132855041368120339009)
                  ·
                    refine ⟨2048349641281026090254257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2731132855041368120339009 2048349641281026090254257)
                    ·
                      refine ⟨1536262230960769567690693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048349641281026090254257 1536262230960769567690693)
                      ·
                        rfl

theorem cell23_2991860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2991860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991860 prefixEnd_2991860 := by exact prefixLift 2991860
  have htrace : WordTrace (prefixWord ++ tailWord_2991860) baseStart_2991860 baseEnd_2991860 := by
    simpa [prefixWord, tailWord_2991860, baseEnd_2991860] using wordTrace_append hprefix tailTrace_2991860
  have hstable : (prefixWord ++ tailWord_2991860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991860).length < 2 ^ (prefixWord ++ tailWord_2991860).sum := by decide
  have hdescent : baseEnd_2991860 < baseStart_2991860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991899 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 4, 2, 2]
def baseStart_2991899 : Nat := 118140960795 + 2991899 * 2 ^ 59
def prefixEnd_2991899 : Nat := 4983230072969 + 3 ^ 40 * 2991899 * 2
def baseEnd_2991899 : Nat := 1536282256706294915103013

theorem tailTrace_2991899 : CollatzResearch.WordTrace tailWord_2991899 prefixEnd_2991899 1536282256706294915103013 := by
  unfold tailWord_2991899
  simp only [CollatzResearch.WordTrace]
  refine ⟨109123521387868373513458751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72749014258578915675639167 109123521387868373513458751)
  ·
    refine ⟨163685282081802560270188127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109123521387868373513458751 163685282081802560270188127)
    ·
      refine ⟨245527923122703840405282191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163685282081802560270188127 245527923122703840405282191)
      ·
        refine ⟨368291884684055760607923287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245527923122703840405282191 368291884684055760607923287)
        ·
          refine ⟨552437827026083640911884931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368291884684055760607923287 552437827026083640911884931)
          ·
            refine ⟨828656740539125461367827397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552437827026083640911884931 828656740539125461367827397)
            ·
              refine ⟨155373138851086024006467637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 828656740539125461367827397 155373138851086024006467637)
              ·
                refine ⟨14566231767289314750606341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155373138851086024006467637 14566231767289314750606341)
                ·
                  refine ⟨2731168456366746515738689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14566231767289314750606341 2731168456366746515738689)
                  ·
                    refine ⟨2048376342275059886804017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2731168456366746515738689 2048376342275059886804017)
                    ·
                      refine ⟨1536282256706294915103013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048376342275059886804017 1536282256706294915103013)
                      ·
                        rfl

theorem cell23_2991899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 2, 2].length) (baseStart_2991899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991899 prefixEnd_2991899 := by exact prefixLift 2991899
  have htrace : WordTrace (prefixWord ++ tailWord_2991899) baseStart_2991899 baseEnd_2991899 := by
    simpa [prefixWord, tailWord_2991899, baseEnd_2991899] using wordTrace_append hprefix tailTrace_2991899
  have hstable : (prefixWord ++ tailWord_2991899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991899).length < 2 ^ (prefixWord ++ tailWord_2991899).sum := by decide
  have hdescent : baseEnd_2991899 < baseStart_2991899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991916 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 1, 4, 2]
def baseStart_2991916 : Nat := 118140960795 + 2991916 * 2 ^ 59
def prefixEnd_2991916 : Nat := 4983230072969 + 3 ^ 40 * 2991916 * 2
def baseEnd_2991916 : Nat := 1536290985877421348590435

theorem tailTrace_2991916 : CollatzResearch.WordTrace tailWord_2991916 prefixEnd_2991916 1536290985877421348590435 := by
  unfold tailWord_2991916
  simp only [CollatzResearch.WordTrace]
  refine ⟨54562070714403392708413801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72749427619204523611218401 54562070714403392708413801)
  ·
    refine ⟨40921553035802544531310351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54562070714403392708413801 40921553035802544531310351)
    ·
      refine ⟨61382329553703816796965527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40921553035802544531310351 61382329553703816796965527)
      ·
        refine ⟨92073494330555725195448291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61382329553703816796965527 92073494330555725195448291)
        ·
          refine ⟨138110241495833587793172437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92073494330555725195448291 138110241495833587793172437)
          ·
            refine ⟨3236958785058599713902479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 138110241495833587793172437 3236958785058599713902479)
            ·
              refine ⟨4855438177587899570853719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236958785058599713902479 4855438177587899570853719)
              ·
                refine ⟨7283157266381849356280579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4855438177587899570853719 7283157266381849356280579)
                ·
                  refine ⟨10924735899572774034420869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7283157266381849356280579 10924735899572774034420869)
                  ·
                    refine ⟨2048387981169895131453913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10924735899572774034420869 2048387981169895131453913)
                    ·
                      refine ⟨1536290985877421348590435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048387981169895131453913 1536290985877421348590435)
                      ·
                        rfl

theorem cell23_2991916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_2991916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991916 prefixEnd_2991916 := by exact prefixLift 2991916
  have htrace : WordTrace (prefixWord ++ tailWord_2991916) baseStart_2991916 baseEnd_2991916 := by
    simpa [prefixWord, tailWord_2991916, baseEnd_2991916] using wordTrace_append hprefix tailTrace_2991916
  have hstable : (prefixWord ++ tailWord_2991916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991916).length < 2 ^ (prefixWord ++ tailWord_2991916).sum := by decide
  have hdescent : baseEnd_2991916 < baseStart_2991916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991922 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 7]
def baseStart_2991922 : Nat := 118140960795 + 2991922 * 2 ^ 59
def prefixEnd_2991922 : Nat := 4983230072969 + 3 ^ 40 * 2991922 * 2
def baseEnd_2991922 : Nat := 170699340751260925012823

theorem tailTrace_2991922 : CollatzResearch.WordTrace tailWord_2991922 prefixEnd_2991922 170699340751260925012823 := by
  unfold tailWord_2991922
  simp only [CollatzResearch.WordTrace]
  refine ⟨27281090066696262110386505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72749573511190032294364013 27281090066696262110386505)
  ·
    refine ⟨20460817550022196582789879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27281090066696262110386505 20460817550022196582789879)
    ·
      refine ⟨30691226325033294874184819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20460817550022196582789879 30691226325033294874184819)
      ·
        refine ⟨46036839487549942311277229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30691226325033294874184819 46036839487549942311277229)
        ·
          refine ⟨17263814807831228366728961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46036839487549942311277229 17263814807831228366728961)
          ·
            refine ⟨12947861105873421275046721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17263814807831228366728961 12947861105873421275046721)
            ·
              refine ⟨9710895829405065956285041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12947861105873421275046721 9710895829405065956285041)
              ·
                refine ⟨7283171872053799467213781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9710895829405065956285041 7283171872053799467213781)
                ·
                  refine ⟨170699340751260925012823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7283171872053799467213781 170699340751260925012823)
                  ·
                    rfl

theorem cell23_2991922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_2991922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991922 prefixEnd_2991922 := by exact prefixLift 2991922
  have htrace : WordTrace (prefixWord ++ tailWord_2991922) baseStart_2991922 baseEnd_2991922 := by
    simpa [prefixWord, tailWord_2991922, baseEnd_2991922] using wordTrace_append hprefix tailTrace_2991922
  have hstable : (prefixWord ++ tailWord_2991922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991922).length < 2 ^ (prefixWord ++ tailWord_2991922).sum := by decide
  have hdescent : baseEnd_2991922 < baseStart_2991922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991932 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2991932 : Nat := 118140960795 + 2991932 * 2 ^ 59
def prefixEnd_2991932 : Nat := 4983230072969 + 3 ^ 40 * 2991932 * 2
def baseEnd_2991932 : Nat := 1536299201567893285990361

theorem tailTrace_2991932 : CollatzResearch.WordTrace tailWord_2991932 prefixEnd_2991932 1536299201567893285990361 := by
  unfold tailWord_2991932
  simp only [CollatzResearch.WordTrace]
  refine ⟨54562362498374410074705025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72749816664499213432940033 54562362498374410074705025)
  ·
    refine ⟨40921771873780807556028769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54562362498374410074705025 40921771873780807556028769)
    ·
      refine ⟨30691328905335605667021577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40921771873780807556028769 30691328905335605667021577)
      ·
        refine ⟨23018496679001704250266183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30691328905335605667021577 23018496679001704250266183)
        ·
          refine ⟨34527745018502556375399275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23018496679001704250266183 34527745018502556375399275)
          ·
            refine ⟨51791617527753834563098913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34527745018502556375399275 51791617527753834563098913)
            ·
              refine ⟨38843713145815375922324185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51791617527753834563098913 38843713145815375922324185)
              ·
                refine ⟨29132784859361531941743139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38843713145815375922324185 29132784859361531941743139)
                ·
                  refine ⟨43699177289042297912614709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29132784859361531941743139 43699177289042297912614709)
                  ·
                    refine ⟨4096797870847715429307629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43699177289042297912614709 4096797870847715429307629)
                    ·
                      refine ⟨1536299201567893285990361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4096797870847715429307629 1536299201567893285990361)
                      ·
                        rfl

theorem cell23_2991932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2991932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991932 prefixEnd_2991932 := by exact prefixLift 2991932
  have htrace : WordTrace (prefixWord ++ tailWord_2991932) baseStart_2991932 baseEnd_2991932 := by
    simpa [prefixWord, tailWord_2991932, baseEnd_2991932] using wordTrace_append hprefix tailTrace_2991932
  have hstable : (prefixWord ++ tailWord_2991932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991932).length < 2 ^ (prefixWord ++ tailWord_2991932).sum := by decide
  have hdescent : baseEnd_2991932 < baseStart_2991932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991939 : List Nat := [1, 1, 1, 3, 1, 5, 3, 3, 5]
def baseStart_2991939 : Nat := 118140960795 + 2991939 * 2 ^ 59
def prefixEnd_2991939 : Nat := 4983230072969 + 3 ^ 40 * 2991939 * 2
def baseEnd_2991939 : Nat := 170700310659163862066981

theorem tailTrace_2991939 : CollatzResearch.WordTrace tailWord_2991939 prefixEnd_2991939 170700310659163862066981 := by
  unfold tailWord_2991939
  simp only [CollatzResearch.WordTrace]
  refine ⟨109124980307723460344914871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72749986871815640229943247 109124980307723460344914871)
  ·
    refine ⟨163687470461585190517372307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109124980307723460344914871 163687470461585190517372307)
    ·
      refine ⟨245531205692377785776058461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163687470461585190517372307 245531205692377785776058461)
      ·
        refine ⟨92074202134641669666021923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245531205692377785776058461 92074202134641669666021923)
        ·
          refine ⟨138111303201962504499032885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92074202134641669666021923 138111303201962504499032885)
          ·
            refine ⟨12947934675183984796784333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138111303201962504499032885 12947934675183984796784333)
            ·
              refine ⟨4855475503193994298794125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12947934675183984796784333 4855475503193994298794125)
              ·
                refine ⟨1820803313697747862047797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4855475503193994298794125 1820803313697747862047797)
                ·
                  refine ⟨170700310659163862066981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1820803313697747862047797 170700310659163862066981)
                  ·
                    rfl

theorem cell23_2991939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 5].length) (baseStart_2991939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991939 prefixEnd_2991939 := by exact prefixLift 2991939
  have htrace : WordTrace (prefixWord ++ tailWord_2991939) baseStart_2991939 baseEnd_2991939 := by
    simpa [prefixWord, tailWord_2991939, baseEnd_2991939] using wordTrace_append hprefix tailTrace_2991939
  have hstable : (prefixWord ++ tailWord_2991939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991939).length < 2 ^ (prefixWord ++ tailWord_2991939).sum := by decide
  have hdescent : baseEnd_2991939 < baseStart_2991939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991955 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 8]
def baseStart_2991955 : Nat := 118140960795 + 2991955 * 2 ^ 59
def prefixEnd_2991955 : Nat := 4983230072969 + 3 ^ 40 * 2991955 * 2
def baseEnd_2991955 : Nat := 1536311011622946696002755

theorem tailTrace_2991955 : CollatzResearch.WordTrace tailWord_2991955 prefixEnd_2991955 1536311011622946696002755 := by
  unfold tailWord_2991955
  simp only [CollatzResearch.WordTrace]
  refine ⟨109125563875665495077497319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72750375917110330051664879 109125563875665495077497319)
  ·
    refine ⟨163688345813498242616245979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109125563875665495077497319 163688345813498242616245979)
    ·
      refine ⟨245532518720247363924368969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163688345813498242616245979 245532518720247363924368969)
      ·
        refine ⟨184149389040185522943276727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245532518720247363924368969 184149389040185522943276727)
        ·
          refine ⟨276224083560278284414915091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184149389040185522943276727 276224083560278284414915091)
          ·
            refine ⟨414336125340417426622372637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276224083560278284414915091 414336125340417426622372637)
            ·
              refine ⟨155376047002656534983389739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414336125340417426622372637 155376047002656534983389739)
              ·
                refine ⟨233064070503984802475084609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155376047002656534983389739 233064070503984802475084609)
                ·
                  refine ⟨174798052877988601856313457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233064070503984802475084609 174798052877988601856313457)
                  ·
                    refine ⟨131098539658491451392235093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174798052877988601856313457 131098539658491451392235093)
                    ·
                      refine ⟨1536311011622946696002755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 131098539658491451392235093 1536311011622946696002755)
                      ·
                        rfl

theorem cell23_2991955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_2991955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991955 prefixEnd_2991955 := by exact prefixLift 2991955
  have htrace : WordTrace (prefixWord ++ tailWord_2991955) baseStart_2991955 baseEnd_2991955 := by
    simpa [prefixWord, tailWord_2991955, baseEnd_2991955] using wordTrace_append hprefix tailTrace_2991955
  have hstable : (prefixWord ++ tailWord_2991955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991955).length < 2 ^ (prefixWord ++ tailWord_2991955).sum := by decide
  have hdescent : baseEnd_2991955 < baseStart_2991955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991962 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_2991962 : Nat := 118140960795 + 2991962 * 2 ^ 59
def prefixEnd_2991962 : Nat := 4983230072969 + 3 ^ 40 * 2991962 * 2
def baseEnd_2991962 : Nat := 1536314605987528168615223

theorem tailTrace_2991962 : CollatzResearch.WordTrace tailWord_2991962 prefixEnd_2991962 1536314605987528168615223 := by
  unfold tailWord_2991962
  simp only [CollatzResearch.WordTrace]
  refine ⟨27281454796660033818250535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72750546124426756848668093 27281454796660033818250535)
  ·
    refine ⟨40922182194990050727375803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27281454796660033818250535 40922182194990050727375803)
    ·
      refine ⟨61383273292485076091063705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40922182194990050727375803 61383273292485076091063705)
      ·
        refine ⟨46037454969363807068297779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61383273292485076091063705 46037454969363807068297779)
        ·
          refine ⟨69056182454045710602446669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46037454969363807068297779 69056182454045710602446669)
          ·
            refine ⟨25896068420267141475917501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69056182454045710602446669 25896068420267141475917501)
            ·
              refine ⟨9711025657600178053469063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25896068420267141475917501 9711025657600178053469063)
              ·
                refine ⟨14566538486400267080203595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9711025657600178053469063 14566538486400267080203595)
                ·
                  refine ⟨21849807729600400620305393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14566538486400267080203595 21849807729600400620305393)
                  ·
                    refine ⟨16387355797200300465229045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21849807729600400620305393 16387355797200300465229045)
                    ·
                      refine ⟨1536314605987528168615223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16387355797200300465229045 1536314605987528168615223)
                      ·
                        rfl

theorem cell23_2991962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_2991962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991962 prefixEnd_2991962 := by exact prefixLift 2991962
  have htrace : WordTrace (prefixWord ++ tailWord_2991962) baseStart_2991962 baseEnd_2991962 := by
    simpa [prefixWord, tailWord_2991962, baseEnd_2991962] using wordTrace_append hprefix tailTrace_2991962
  have hstable : (prefixWord ++ tailWord_2991962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991962).length < 2 ^ (prefixWord ++ tailWord_2991962).sum := by decide
  have hdescent : baseEnd_2991962 < baseStart_2991962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991992 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_2991992 : Nat := 118140960795 + 2991992 * 2 ^ 59
def prefixEnd_2991992 : Nat := 4983230072969 + 3 ^ 40 * 2991992 * 2
def baseEnd_2991992 : Nat := 1536330010407163051240085

theorem tailTrace_2991992 : CollatzResearch.WordTrace tailWord_2991992 prefixEnd_2991992 1536330010407163051240085 := by
  unfold tailWord_2991992
  simp only [CollatzResearch.WordTrace]
  refine ⟨54563456688265725198297115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72751275584354300264396153 54563456688265725198297115)
  ·
    refine ⟨81845185032398587797445673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54563456688265725198297115 81845185032398587797445673)
    ·
      refine ⟨61383888774298940848084255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81845185032398587797445673 61383888774298940848084255)
      ·
        refine ⟨92075833161448411272126383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61383888774298940848084255 92075833161448411272126383)
        ·
          refine ⟨138113749742172616908189575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92075833161448411272126383 138113749742172616908189575)
          ·
            refine ⟨207170624613258925362284363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138113749742172616908189575 207170624613258925362284363)
            ·
              refine ⟨310755936919888388043426545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207170624613258925362284363 310755936919888388043426545)
              ·
                refine ⟨233066952689916291032569909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310755936919888388043426545 233066952689916291032569909)
                ·
                  refine ⟨21850026814679652284303429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233066952689916291032569909 21850026814679652284303429)
                  ·
                    refine ⟨4096880027752434803306893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21850026814679652284303429 4096880027752434803306893)
                    ·
                      refine ⟨1536330010407163051240085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4096880027752434803306893 1536330010407163051240085)
                      ·
                        rfl

theorem cell23_2991992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_2991992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2991992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2991992 prefixEnd_2991992 := by exact prefixLift 2991992
  have htrace : WordTrace (prefixWord ++ tailWord_2991992) baseStart_2991992 baseEnd_2991992 := by
    simpa [prefixWord, tailWord_2991992, baseEnd_2991992] using wordTrace_append hprefix tailTrace_2991992
  have hstable : (prefixWord ++ tailWord_2991992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991992).length < 2 ^ (prefixWord ++ tailWord_2991992).sum := by decide
  have hdescent : baseEnd_2991992 < baseStart_2991992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992009 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 3]
def baseStart_2992009 : Nat := 118140960795 + 2992009 * 2 ^ 59
def prefixEnd_2992009 : Nat := 4983230072969 + 3 ^ 40 * 2992009 * 2
def baseEnd_2992009 : Nat := 1536338739578289484727507

theorem tailTrace_2992009 : CollatzResearch.WordTrace tailWord_2992009 prefixEnd_2992009 1536338739578289484727507 := by
  unfold tailWord_2992009
  simp only [CollatzResearch.WordTrace]
  refine ⟨109127533417469862299963081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72751688944979908199975387 109127533417469862299963081)
  ·
    refine ⟨81845650063102396724972311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109127533417469862299963081 81845650063102396724972311)
    ·
      refine ⟨122768475094653595087458467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81845650063102396724972311 122768475094653595087458467)
      ·
        refine ⟨184152712641980392631187701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122768475094653595087458467 184152712641980392631187701)
        ·
          refine ⟨17264316810185661809173847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184152712641980392631187701 17264316810185661809173847)
          ·
            refine ⟨25896475215278492713760771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17264316810185661809173847 25896475215278492713760771)
            ·
              refine ⟨38844712822917739070641157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25896475215278492713760771 38844712822917739070641157)
              ·
                refine ⟨7283383654297076075745217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38844712822917739070641157 7283383654297076075745217)
                ·
                  refine ⟨5462537740722807056808913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7283383654297076075745217 5462537740722807056808913)
                  ·
                    refine ⟨4096903305542105292606685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5462537740722807056808913 4096903305542105292606685)
                    ·
                      refine ⟨1536338739578289484727507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4096903305542105292606685 1536338739578289484727507)
                      ·
                        rfl

theorem cell23_2992009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_2992009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992009 prefixEnd_2992009 := by exact prefixLift 2992009
  have htrace : WordTrace (prefixWord ++ tailWord_2992009) baseStart_2992009 baseEnd_2992009 := by
    simpa [prefixWord, tailWord_2992009, baseEnd_2992009] using wordTrace_append hprefix tailTrace_2992009
  have hstable : (prefixWord ++ tailWord_2992009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992009).length < 2 ^ (prefixWord ++ tailWord_2992009).sum := by decide
  have hdescent : baseEnd_2992009 < baseStart_2992009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992029 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 6]
def baseStart_2992029 : Nat := 118140960795 + 2992029 * 2 ^ 59
def prefixEnd_2992029 : Nat := 4983230072969 + 3 ^ 40 * 2992029 * 2
def baseEnd_2992029 : Nat := 170705445465708822941935

theorem tailTrace_2992029 : CollatzResearch.WordTrace tailWord_2992029 prefixEnd_2992029 170705445465708822941935 := by
  unfold tailWord_2992029
  simp only [CollatzResearch.WordTrace]
  refine ⟨109128262877397405715691141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72752175251598270477127427 109128262877397405715691141)
  ·
    refine ⟨20461549289512013571692089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109128262877397405715691141 20461549289512013571692089)
    ·
      refine ⟨15346161967134010178769067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20461549289512013571692089 15346161967134010178769067)
      ·
        refine ⟨23019242950701015268153601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15346161967134010178769067 23019242950701015268153601)
        ·
          refine ⟨17264432213025761451115201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23019242950701015268153601 17264432213025761451115201)
          ·
            refine ⟨12948324159769321088336401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17264432213025761451115201 12948324159769321088336401)
            ·
              refine ⟨9711243119826990816252301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12948324159769321088336401 9711243119826990816252301)
              ·
                refine ⟨3641716169935121556094613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9711243119826990816252301 3641716169935121556094613)
                ·
                  refine ⟨170705445465708822941935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3641716169935121556094613 170705445465708822941935)
                  ·
                    rfl

theorem cell23_2992029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_2992029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992029 prefixEnd_2992029 := by exact prefixLift 2992029
  have htrace : WordTrace (prefixWord ++ tailWord_2992029) baseStart_2992029 baseEnd_2992029 := by
    simpa [prefixWord, tailWord_2992029, baseEnd_2992029] using wordTrace_append hprefix tailTrace_2992029
  have hstable : (prefixWord ++ tailWord_2992029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992029).length < 2 ^ (prefixWord ++ tailWord_2992029).sum := by decide
  have hdescent : baseEnd_2992029 < baseStart_2992029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992040 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2992040 : Nat := 118140960795 + 2992040 * 2 ^ 59
def prefixEnd_2992040 : Nat := 4983230072969 + 3 ^ 40 * 2992040 * 2
def baseEnd_2992040 : Nat := 1536354657478578863439865

theorem tailTrace_2992040 : CollatzResearch.WordTrace tailWord_2992040 prefixEnd_2992040 1536354657478578863439865 := by
  unfold tailWord_2992040
  simp only [CollatzResearch.WordTrace]
  refine ⟨54564332040178777297170787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72752442720238369729561049 54564332040178777297170787)
  ·
    refine ⟨81846498060268165945756181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54564332040178777297170787 81846498060268165945756181)
    ·
      refine ⟨3836554596575070278707321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81846498060268165945756181 3836554596575070278707321)
      ·
        refine ⟨2877415947431302709030491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3836554596575070278707321 2877415947431302709030491)
        ·
          refine ⟨4316123921146954063545737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877415947431302709030491 4316123921146954063545737)
          ·
            refine ⟨3237092940860215547659303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4316123921146954063545737 3237092940860215547659303)
            ·
              refine ⟨4855639411290323321488955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3237092940860215547659303 4855639411290323321488955)
              ·
                refine ⟨7283459116935484982233433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4855639411290323321488955 7283459116935484982233433)
                ·
                  refine ⟨5462594337701613736675075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7283459116935484982233433 5462594337701613736675075)
                  ·
                    refine ⟨8193891506552420605012613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5462594337701613736675075 8193891506552420605012613)
                    ·
                      refine ⟨1536354657478578863439865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8193891506552420605012613 1536354657478578863439865)
                      ·
                        rfl

theorem cell23_2992040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2992040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992040 prefixEnd_2992040 := by exact prefixLift 2992040
  have htrace : WordTrace (prefixWord ++ tailWord_2992040) baseStart_2992040 baseEnd_2992040 := by
    simpa [prefixWord, tailWord_2992040, baseEnd_2992040] using wordTrace_append hprefix tailTrace_2992040
  have hstable : (prefixWord ++ tailWord_2992040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992040).length < 2 ^ (prefixWord ++ tailWord_2992040).sum := by decide
  have hdescent : baseEnd_2992040 < baseStart_2992040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992093 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2992093 : Nat := 118140960795 + 2992093 * 2 ^ 59
def prefixEnd_2992093 : Nat := 4983230072969 + 3 ^ 40 * 2992093 * 2
def baseEnd_2992093 : Nat := 512127290651089052025707

theorem tailTrace_2992093 : CollatzResearch.WordTrace tailWord_2992093 prefixEnd_2992093 512127290651089052025707 := by
  unfold tailWord_2992093
  simp only [CollatzResearch.WordTrace]
  refine ⟨109130597149165544646020933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72753731432777029764013955 109130597149165544646020933)
  ·
    refine ⟨20461986965468539621128925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109130597149165544646020933 20461986965468539621128925)
    ·
      refine ⟨7673245112050702357923347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20461986965468539621128925 7673245112050702357923347)
      ·
        refine ⟨11509867668076053536885021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7673245112050702357923347 11509867668076053536885021)
        ·
          refine ⟨4316200375528520076331883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11509867668076053536885021 4316200375528520076331883)
          ·
            refine ⟨6474300563292780114497825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316200375528520076331883 6474300563292780114497825)
            ·
              refine ⟨4855725422469585085873369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6474300563292780114497825 4855725422469585085873369)
              ·
                refine ⟨3641794066852188814405027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4855725422469585085873369 3641794066852188814405027)
                ·
                  refine ⟨5462691100278283221607541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641794066852188814405027 5462691100278283221607541)
                  ·
                    refine ⟨512127290651089052025707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5462691100278283221607541 512127290651089052025707)
                    ·
                      rfl

theorem cell23_2992093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2992093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992093 prefixEnd_2992093 := by exact prefixLift 2992093
  have htrace : WordTrace (prefixWord ++ tailWord_2992093) baseStart_2992093 baseEnd_2992093 := by
    simpa [prefixWord, tailWord_2992093, baseEnd_2992093] using wordTrace_append hprefix tailTrace_2992093
  have hstable : (prefixWord ++ tailWord_2992093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992093).length < 2 ^ (prefixWord ++ tailWord_2992093).sum := by decide
  have hdescent : baseEnd_2992093 < baseStart_2992093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992126 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2992126 : Nat := 118140960795 + 2992126 * 2 ^ 59
def prefixEnd_2992126 : Nat := 4983230072969 + 3 ^ 40 * 2992126 * 2
def baseEnd_2992126 : Nat := 1536398816814865526964469

theorem tailTrace_2992126 : CollatzResearch.WordTrace tailWord_2992126 prefixEnd_2992126 1536398816814865526964469 := by
  unfold tailWord_2992126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641475094755748910246529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72754533838697327521314821 13641475094755748910246529)
  ·
    refine ⟨10231106321066811682684897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13641475094755748910246529 10231106321066811682684897)
    ·
      refine ⟨7673329740800108762013673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10231106321066811682684897 7673329740800108762013673)
      ·
        refine ⟨5754997305600081571510255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7673329740800108762013673 5754997305600081571510255)
        ·
          refine ⟨8632495958400122357265383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5754997305600081571510255 8632495958400122357265383)
          ·
            refine ⟨12948743937600183535898075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8632495958400122357265383 12948743937600183535898075)
            ·
              refine ⟨19423115906400275303847113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12948743937600183535898075 19423115906400275303847113)
              ·
                refine ⟨14567336929800206477885335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19423115906400275303847113 14567336929800206477885335)
                ·
                  refine ⟨21851005394700309716828003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14567336929800206477885335 21851005394700309716828003)
                  ·
                    refine ⟨32776508092050464575242005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21851005394700309716828003 32776508092050464575242005)
                    ·
                      refine ⟨1536398816814865526964469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32776508092050464575242005 1536398816814865526964469)
                      ·
                        rfl

theorem cell23_2992126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2992126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992126 prefixEnd_2992126 := by exact prefixLift 2992126
  have htrace : WordTrace (prefixWord ++ tailWord_2992126) baseStart_2992126 baseEnd_2992126 := by
    simpa [prefixWord, tailWord_2992126, baseEnd_2992126] using wordTrace_append hprefix tailTrace_2992126
  have hstable : (prefixWord ++ tailWord_2992126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992126).length < 2 ^ (prefixWord ++ tailWord_2992126).sum := by decide
  have hdescent : baseEnd_2992126 < baseStart_2992126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992167 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2992167 : Nat := 118140960795 + 2992167 * 2 ^ 59
def prefixEnd_2992167 : Nat := 4983230072969 + 3 ^ 40 * 2992167 * 2
def baseEnd_2992167 : Nat := 1536419869521699866551781

theorem tailTrace_2992167 : CollatzResearch.WordTrace tailWord_2992167 prefixEnd_2992167 1536419869521699866551781 := by
  unfold tailWord_2992167
  simp only [CollatzResearch.WordTrace]
  refine ⟨109133296150897455284214755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72755530767264970189476503 109133296150897455284214755)
  ·
    refine ⟨163699944226346182926322133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109133296150897455284214755 163699944226346182926322133)
    ·
      refine ⟨3836717442804988662335675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 163699944226346182926322133 3836717442804988662335675)
      ·
        refine ⟨5755076164207482993503513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3836717442804988662335675 5755076164207482993503513)
        ·
          refine ⟨4316307123155612245127635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5755076164207482993503513 4316307123155612245127635)
          ·
            refine ⟨6474460684733418367691453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316307123155612245127635 6474460684733418367691453)
            ·
              refine ⟨2427922756775031887884295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6474460684733418367691453 2427922756775031887884295)
              ·
                refine ⟨3641884135162547831826443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427922756775031887884295 3641884135162547831826443)
                ·
                  refine ⟨5462826202743821747739665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641884135162547831826443 5462826202743821747739665)
                  ·
                    refine ⟨4097119652057866310804749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5462826202743821747739665 4097119652057866310804749)
                    ·
                      refine ⟨1536419869521699866551781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4097119652057866310804749 1536419869521699866551781)
                      ·
                        rfl

theorem cell23_2992167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2992167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992167 prefixEnd_2992167 := by exact prefixLift 2992167
  have htrace : WordTrace (prefixWord ++ tailWord_2992167) baseStart_2992167 baseEnd_2992167 := by
    simpa [prefixWord, tailWord_2992167, baseEnd_2992167] using wordTrace_append hprefix tailTrace_2992167
  have hstable : (prefixWord ++ tailWord_2992167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992167).length < 2 ^ (prefixWord ++ tailWord_2992167).sum := by decide
  have hdescent : baseEnd_2992167 < baseStart_2992167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992186 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2]
def baseStart_2992186 : Nat := 118140960795 + 2992186 * 2 ^ 59
def prefixEnd_2992186 : Nat := 4983230072969 + 3 ^ 40 * 2992186 * 2
def baseEnd_2992186 : Nat := 1536429625654135292214193

theorem tailTrace_2992186 : CollatzResearch.WordTrace tailWord_2992186 prefixEnd_2992186 1536429625654135292214193 := by
  unfold tailWord_2992186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27283497284457155382289103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72755992758552414352770941 27283497284457155382289103)
  ·
    refine ⟨40925245926685733073433655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27283497284457155382289103 40925245926685733073433655)
    ·
      refine ⟨61387868890028599610150483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40925245926685733073433655 61387868890028599610150483)
      ·
        refine ⟨92081803335042899415225725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61387868890028599610150483 92081803335042899415225725)
        ·
          refine ⟨34530676250641087280709647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92081803335042899415225725 34530676250641087280709647)
          ·
            refine ⟨51796014375961630921064471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34530676250641087280709647 51796014375961630921064471)
            ·
              refine ⟨77694021563942446381596707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51796014375961630921064471 77694021563942446381596707)
              ·
                refine ⟨116541032345913669572395061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77694021563942446381596707 116541032345913669572395061)
                ·
                  refine ⟨10925721782429406522412037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116541032345913669572395061 10925721782429406522412037)
                  ·
                    refine ⟨2048572834205513722952257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10925721782429406522412037 2048572834205513722952257)
                    ·
                      refine ⟨1536429625654135292214193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048572834205513722952257 1536429625654135292214193)
                      ·
                        rfl

theorem cell23_2992186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_2992186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992186 prefixEnd_2992186 := by exact prefixLift 2992186
  have htrace : WordTrace (prefixWord ++ tailWord_2992186) baseStart_2992186 baseEnd_2992186 := by
    simpa [prefixWord, tailWord_2992186, baseEnd_2992186] using wordTrace_append hprefix tailTrace_2992186
  have hstable : (prefixWord ++ tailWord_2992186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992186).length < 2 ^ (prefixWord ++ tailWord_2992186).sum := by decide
  have hdescent : baseEnd_2992186 < baseStart_2992186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992236 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_2992236 : Nat := 118140960795 + 2992236 * 2 ^ 59
def prefixEnd_2992236 : Nat := 4983230072969 + 3 ^ 40 * 2992236 * 2
def baseEnd_2992236 : Nat := 1536455299686860096588963

theorem tailTrace_2992236 : CollatzResearch.WordTrace tailWord_2992236 prefixEnd_2992236 1536455299686860096588963 := by
  unfold tailWord_2992236
  simp only [CollatzResearch.WordTrace]
  refine ⟨54567906393823740034238281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72757208525098320045651041 54567906393823740034238281)
  ·
    refine ⟨40925929795367805025678711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54567906393823740034238281 40925929795367805025678711)
    ·
      refine ⟨61388894693051707538518067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40925929795367805025678711 61388894693051707538518067)
      ·
        refine ⟨92083342039577561307777101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61388894693051707538518067 92083342039577561307777101)
        ·
          refine ⟨34531253264841585490416413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92083342039577561307777101 34531253264841585490416413)
          ·
            refine ⟨12949219974315594558906155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34531253264841585490416413 12949219974315594558906155)
            ·
              refine ⟨19423829961473391838359233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12949219974315594558906155 19423829961473391838359233)
              ·
                refine ⟨14567872471105043878769425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19423829961473391838359233 14567872471105043878769425)
                ·
                  refine ⟨10925904353328782909077069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14567872471105043878769425 10925904353328782909077069)
                  ·
                    refine ⟨4097214132498293590903901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10925904353328782909077069 4097214132498293590903901)
                    ·
                      refine ⟨1536455299686860096588963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4097214132498293590903901 1536455299686860096588963)
                      ·
                        rfl

theorem cell23_2992236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_2992236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992236 prefixEnd_2992236 := by exact prefixLift 2992236
  have htrace : WordTrace (prefixWord ++ tailWord_2992236) baseStart_2992236 baseEnd_2992236 := by
    simpa [prefixWord, tailWord_2992236, baseEnd_2992236] using wordTrace_append hprefix tailTrace_2992236
  have hstable : (prefixWord ++ tailWord_2992236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992236).length < 2 ^ (prefixWord ++ tailWord_2992236).sum := by decide
  have hdescent : baseEnd_2992236 < baseStart_2992236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992383 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 4]
def baseStart_2992383 : Nat := 118140960795 + 2992383 * 2 ^ 59
def prefixEnd_2992383 : Nat := 4983230072969 + 3 ^ 40 * 2992383 * 2
def baseEnd_2992383 : Nat := 1536530781343071021450787

theorem tailTrace_2992383 : CollatzResearch.WordTrace tailWord_2992383 prefixEnd_2992383 1536530781343071021450787 := by
  unfold tailWord_2992383
  simp only [CollatzResearch.WordTrace]
  refine ⟨109141174318114924174077803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72760782878743282782718535 109141174318114924174077803)
  ·
    refine ⟨163711761477172386261116705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109141174318114924174077803 163711761477172386261116705)
    ·
      refine ⟨122783821107879289695837529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163711761477172386261116705 122783821107879289695837529)
      ·
        refine ⟨92087865830909467271878147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122783821107879289695837529 92087865830909467271878147)
        ·
          refine ⟨138131798746364200907817221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92087865830909467271878147 138131798746364200907817221)
          ·
            refine ⟨25899712264943287670215729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138131798746364200907817221 25899712264943287670215729)
            ·
              refine ⟨19424784198707465752661797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25899712264943287670215729 19424784198707465752661797)
              ·
                refine ⟨3642147037257649828624087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19424784198707465752661797 3642147037257649828624087)
                ·
                  refine ⟨5463220555886474742936131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3642147037257649828624087 5463220555886474742936131)
                  ·
                    refine ⟨8194830833829712114404197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5463220555886474742936131 8194830833829712114404197)
                    ·
                      refine ⟨1536530781343071021450787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8194830833829712114404197 1536530781343071021450787)
                      ·
                        rfl

theorem cell23_2992383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_2992383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992383 prefixEnd_2992383 := by exact prefixLift 2992383
  have htrace : WordTrace (prefixWord ++ tailWord_2992383) baseStart_2992383 baseEnd_2992383 := by
    simpa [prefixWord, tailWord_2992383, baseEnd_2992383] using wordTrace_append hprefix tailTrace_2992383
  have hstable : (prefixWord ++ tailWord_2992383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992383).length < 2 ^ (prefixWord ++ tailWord_2992383).sum := by decide
  have hdescent : baseEnd_2992383 < baseStart_2992383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992410 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_2992410 : Nat := 118140960795 + 2992410 * 2 ^ 59
def prefixEnd_2992410 : Nat := 4983230072969 + 3 ^ 40 * 2992410 * 2
def baseEnd_2992410 : Nat := 512181548440247471937721

theorem tailTrace_2992410 : CollatzResearch.WordTrace tailWord_2992410 prefixEnd_2992410 512181548440247471937721 := by
  unfold tailWord_2992410
  simp only [CollatzResearch.WordTrace]
  refine ⟨27285539772254276946327671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72761439392678071856873789 27285539772254276946327671)
  ·
    refine ⟨40928309658381415419491507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27285539772254276946327671 40928309658381415419491507)
    ·
      refine ⟨61392464487572123129237261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40928309658381415419491507 61392464487572123129237261)
      ·
        refine ⟨23022174182839546173463973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61392464487572123129237261 23022174182839546173463973)
        ·
          refine ⟨4316657659282414907524495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23022174182839546173463973 4316657659282414907524495)
          ·
            refine ⟨6474986488923622361286743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316657659282414907524495 6474986488923622361286743)
            ·
              refine ⟨9712479733385433541930115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6474986488923622361286743 9712479733385433541930115)
              ·
                refine ⟨14568719600078150312895173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9712479733385433541930115 14568719600078150312895173)
                ·
                  refine ⟨2731634925014653183667845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14568719600078150312895173 2731634925014653183667845)
                  ·
                    refine ⟨512181548440247471937721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2731634925014653183667845 512181548440247471937721)
                    ·
                      rfl

theorem cell23_2992410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_2992410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992410 prefixEnd_2992410 := by exact prefixLift 2992410
  have htrace : WordTrace (prefixWord ++ tailWord_2992410) baseStart_2992410 baseEnd_2992410 := by
    simpa [prefixWord, tailWord_2992410, baseEnd_2992410] using wordTrace_append hprefix tailTrace_2992410
  have hstable : (prefixWord ++ tailWord_2992410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992410).length < 2 ^ (prefixWord ++ tailWord_2992410).sum := by decide
  have hdescent : baseEnd_2992410 < baseStart_2992410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992478 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2992478 : Nat := 118140960795 + 2992478 * 2 ^ 59
def prefixEnd_2992478 : Nat := 4983230072969 + 3 ^ 40 * 2992478 * 2
def baseEnd_2992478 : Nat := 512193187335082716587617

theorem tailTrace_2992478 : CollatzResearch.WordTrace tailWord_2992478 prefixEnd_2992478 512193187335082716587617 := by
  unfold tailWord_2992478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13643079906596344424848261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72763092835180503599190725 13643079906596344424848261)
  ·
    refine ⟨2558077482486814579659049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13643079906596344424848261 2558077482486814579659049)
    ·
      refine ⟨1918558111865110934744287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2558077482486814579659049 1918558111865110934744287)
      ·
        refine ⟨2877837167797666402116431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918558111865110934744287 2877837167797666402116431)
        ·
          refine ⟨4316755751696499603174647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877837167797666402116431 4316755751696499603174647)
          ·
            refine ⟨6475133627544749404761971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316755751696499603174647 6475133627544749404761971)
            ·
              refine ⟨9712700441317124107142957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475133627544749404761971 9712700441317124107142957)
              ·
                refine ⟨3642262665493921540178609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9712700441317124107142957 3642262665493921540178609)
                ·
                  refine ⟨2731696999120441155133957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3642262665493921540178609 2731696999120441155133957)
                  ·
                    refine ⟨512193187335082716587617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2731696999120441155133957 512193187335082716587617)
                    ·
                      rfl

theorem cell23_2992478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2992478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992478 prefixEnd_2992478 := by exact prefixLift 2992478
  have htrace : WordTrace (prefixWord ++ tailWord_2992478) baseStart_2992478 baseEnd_2992478 := by
    simpa [prefixWord, tailWord_2992478, baseEnd_2992478] using wordTrace_append hprefix tailTrace_2992478
  have hstable : (prefixWord ++ tailWord_2992478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992478).length < 2 ^ (prefixWord ++ tailWord_2992478).sum := by decide
  have hdescent : baseEnd_2992478 < baseStart_2992478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992493 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2992493 : Nat := 118140960795 + 2992493 * 2 ^ 59
def prefixEnd_2992493 : Nat := 4983230072969 + 3 ^ 40 * 2992493 * 2
def baseEnd_2992493 : Nat := 1536587264215065591075281

theorem tailTrace_2992493 : CollatzResearch.WordTrace tailWord_2992493 prefixEnd_2992493 1536587264215065591075281 := by
  unfold tailWord_2992493
  simp only [CollatzResearch.WordTrace]
  refine ⟨109145186347716412960582133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72763457565144275307054755 109145186347716412960582133)
  ·
    refine ⟨10232361220098413715054575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109145186347716412960582133 10232361220098413715054575)
    ·
      refine ⟨15348541830147620572581863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10232361220098413715054575 15348541830147620572581863)
      ·
        refine ⟨23022812745221430858872795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15348541830147620572581863 23022812745221430858872795)
        ·
          refine ⟨34534219117832146288309193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23022812745221430858872795 34534219117832146288309193)
          ·
            refine ⟨25900664338374109716231895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34534219117832146288309193 25900664338374109716231895)
            ·
              refine ⟨38850996507561164574347843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25900664338374109716231895 38850996507561164574347843)
              ·
                refine ⟨58276494761341746861521765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38850996507561164574347843 58276494761341746861521765)
                ·
                  refine ⟨10926842767751577536535331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58276494761341746861521765 10926842767751577536535331)
                  ·
                    refine ⟨16390264151627366304802997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10926842767751577536535331 16390264151627366304802997)
                    ·
                      refine ⟨1536587264215065591075281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16390264151627366304802997 1536587264215065591075281)
                      ·
                        rfl

theorem cell23_2992493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2992493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992493 prefixEnd_2992493 := by exact prefixLift 2992493
  have htrace : WordTrace (prefixWord ++ tailWord_2992493) baseStart_2992493 baseEnd_2992493 := by
    simpa [prefixWord, tailWord_2992493, baseEnd_2992493] using wordTrace_append hprefix tailTrace_2992493
  have hstable : (prefixWord ++ tailWord_2992493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992493).length < 2 ^ (prefixWord ++ tailWord_2992493).sum := by decide
  have hdescent : baseEnd_2992493 < baseStart_2992493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992524 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 2, 2, 2]
def baseStart_2992524 : Nat := 118140960795 + 2992524 * 2 ^ 59
def prefixEnd_2992524 : Nat := 4983230072969 + 3 ^ 40 * 2992524 * 2
def baseEnd_2992524 : Nat := 1536603182115354969787639

theorem tailTrace_2992524 : CollatzResearch.WordTrace tailWord_2992524 prefixEnd_2992524 1536603182115354969787639 := by
  unfold tailWord_2992524
  simp only [CollatzResearch.WordTrace]
  refine ⟨54573158505302052627480313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72764211340402736836640417 54573158505302052627480313)
  ·
    refine ⟨40929868878976539470610235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54573158505302052627480313 40929868878976539470610235)
    ·
      refine ⟨61394803318464809205915353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40929868878976539470610235 61394803318464809205915353)
      ·
        refine ⟨46046102488848606904436515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61394803318464809205915353 46046102488848606904436515)
        ·
          refine ⟨69069153733272910356654773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46046102488848606904436515 69069153733272910356654773)
          ·
            refine ⟨6475233162494335345936385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69069153733272910356654773 6475233162494335345936385)
            ·
              refine ⟨4856424871870751509452289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6475233162494335345936385 4856424871870751509452289)
              ·
                refine ⟨3642318653903063632089217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4856424871870751509452289 3642318653903063632089217)
                ·
                  refine ⟨2731738990427297724066913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3642318653903063632089217 2731738990427297724066913)
                  ·
                    refine ⟨2048804242820473293050185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2731738990427297724066913 2048804242820473293050185)
                    ·
                      refine ⟨1536603182115354969787639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048804242820473293050185 1536603182115354969787639)
                      ·
                        rfl

theorem cell23_2992524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_2992524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992524 prefixEnd_2992524 := by exact prefixLift 2992524
  have htrace : WordTrace (prefixWord ++ tailWord_2992524) baseStart_2992524 baseEnd_2992524 := by
    simpa [prefixWord, tailWord_2992524, baseEnd_2992524] using wordTrace_append hprefix tailTrace_2992524
  have hstable : (prefixWord ++ tailWord_2992524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992524).length < 2 ^ (prefixWord ++ tailWord_2992524).sum := by decide
  have hdescent : baseEnd_2992524 < baseStart_2992524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992543 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 1, 7]
def baseStart_2992543 : Nat := 118140960795 + 2992543 * 2 ^ 59
def prefixEnd_2992543 : Nat := 4983230072969 + 3 ^ 40 * 2992543 * 2
def baseEnd_2992543 : Nat := 512204312749263465150017

theorem tailTrace_2992543 : CollatzResearch.WordTrace tailWord_2992543 prefixEnd_2992543 512204312749263465150017 := by
  unfold tailWord_2992543
  simp only [CollatzResearch.WordTrace]
  refine ⟨109147009997535271499902283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72764673331690180999934855 109147009997535271499902283)
  ·
    refine ⟨163720514996302907249853425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109147009997535271499902283 163720514996302907249853425)
    ·
      refine ⟨122790386247227180437390069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163720514996302907249853425 122790386247227180437390069)
      ·
        refine ⟨11511598710677548166005319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122790386247227180437390069 11511598710677548166005319)
        ·
          refine ⟨17267398066016322249007979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11511598710677548166005319 17267398066016322249007979)
          ·
            refine ⟨25901097099024483373511969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17267398066016322249007979 25901097099024483373511969)
            ·
              refine ⟨19425822824268362530133977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25901097099024483373511969 19425822824268362530133977)
              ·
                refine ⟨14569367118201271897600483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19425822824268362530133977 14569367118201271897600483)
                ·
                  refine ⟨21854050677301907846400725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14569367118201271897600483 21854050677301907846400725)
                  ·
                    refine ⟨512204312749263465150017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21854050677301907846400725 512204312749263465150017)
                    ·
                      rfl

theorem cell23_2992543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_2992543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992543 prefixEnd_2992543 := by exact prefixLift 2992543
  have htrace : WordTrace (prefixWord ++ tailWord_2992543) baseStart_2992543 baseEnd_2992543 := by
    simpa [prefixWord, tailWord_2992543, baseEnd_2992543] using wordTrace_append hprefix tailTrace_2992543
  have hstable : (prefixWord ++ tailWord_2992543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992543).length < 2 ^ (prefixWord ++ tailWord_2992543).sum := by decide
  have hdescent : baseEnd_2992543 < baseStart_2992543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992597 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_2992597 : Nat := 118140960795 + 2992597 * 2 ^ 59
def prefixEnd_2992597 : Nat := 4983230072969 + 3 ^ 40 * 2992597 * 2
def baseEnd_2992597 : Nat := 1536640666203133184174803

theorem tailTrace_2992597 : CollatzResearch.WordTrace tailWord_2992597 prefixEnd_2992597 1536640666203133184174803 := by
  unfold tailWord_2992597
  simp only [CollatzResearch.WordTrace]
  refine ⟨109148979539339638722368045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72765986359559759148245363 109148979539339638722368045)
  ·
    refine ⟨40930867327252364520888017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109148979539339638722368045 40930867327252364520888017)
    ·
      refine ⟨30698150495439273390666013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40930867327252364520888017 30698150495439273390666013)
      ·
        refine ⟨11511806435789727521499755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30698150495439273390666013 11511806435789727521499755)
        ·
          refine ⟨17267709653684591282249633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11511806435789727521499755 17267709653684591282249633)
          ·
            refine ⟨12950782240263443461687225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17267709653684591282249633 12950782240263443461687225)
            ·
              refine ⟨9713086680197582596265419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12950782240263443461687225 9713086680197582596265419)
              ·
                refine ⟨14569630020296373894398129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9713086680197582596265419 14569630020296373894398129)
                ·
                  refine ⟨10927222515222280420798597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14569630020296373894398129 10927222515222280420798597)
                  ·
                    refine ⟨2048854221604177578899737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10927222515222280420798597 2048854221604177578899737)
                    ·
                      refine ⟨1536640666203133184174803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048854221604177578899737 1536640666203133184174803)
                      ·
                        rfl

theorem cell23_2992597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_2992597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992597 prefixEnd_2992597 := by exact prefixLift 2992597
  have htrace : WordTrace (prefixWord ++ tailWord_2992597) baseStart_2992597 baseEnd_2992597 := by
    simpa [prefixWord, tailWord_2992597, baseEnd_2992597] using wordTrace_append hprefix tailTrace_2992597
  have hstable : (prefixWord ++ tailWord_2992597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992597).length < 2 ^ (prefixWord ++ tailWord_2992597).sum := by decide
  have hdescent : baseEnd_2992597 < baseStart_2992597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992640 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 9, 2]
def baseStart_2992640 : Nat := 118140960795 + 2992640 * 2 ^ 59
def prefixEnd_2992640 : Nat := 4983230072969 + 3 ^ 40 * 2992640 * 2
def baseEnd_2992640 : Nat := 1536662745871276515937105

theorem tailTrace_2992640 : CollatzResearch.WordTrace tailWord_2992640 prefixEnd_2992640 1536662745871276515937105 := by
  unfold tailWord_2992640
  simp only [CollatzResearch.WordTrace]
  refine ⟨54575273939091928533091687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72767031918789238044122249 54575273939091928533091687)
  ·
    refine ⟨81862910908637892799637531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54575273939091928533091687 81862910908637892799637531)
    ·
      refine ⟨122794366362956839199456297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81862910908637892799637531 122794366362956839199456297)
      ·
        refine ⟨92095774772217629399592223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122794366362956839199456297 92095774772217629399592223)
        ·
          refine ⟨138143662158326444099388335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92095774772217629399592223 138143662158326444099388335)
          ·
            refine ⟨207215493237489666149082503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138143662158326444099388335 207215493237489666149082503)
            ·
              refine ⟨310823239856234499223623755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207215493237489666149082503 310823239856234499223623755)
              ·
                refine ⟨466234859784351748835435633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310823239856234499223623755 466234859784351748835435633)
                ·
                  refine ⟨349676144838263811626576725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466234859784351748835435633 349676144838263811626576725)
                  ·
                    refine ⟨2048883661161702021249473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 349676144838263811626576725 2048883661161702021249473)
                    ·
                      refine ⟨1536662745871276515937105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048883661161702021249473 1536662745871276515937105)
                      ·
                        rfl

theorem cell23_2992640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_2992640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992640 prefixEnd_2992640 := by exact prefixLift 2992640
  have htrace : WordTrace (prefixWord ++ tailWord_2992640) baseStart_2992640 baseEnd_2992640 := by
    simpa [prefixWord, tailWord_2992640, baseEnd_2992640] using wordTrace_append hprefix tailTrace_2992640
  have hstable : (prefixWord ++ tailWord_2992640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992640).length < 2 ^ (prefixWord ++ tailWord_2992640).sum := by decide
  have hdescent : baseEnd_2992640 < baseStart_2992640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992641 : List Nat := [1, 2, 4, 1, 3, 2, 3, 2, 1, 4]
def baseStart_2992641 : Nat := 118140960795 + 2992641 * 2 ^ 59
def prefixEnd_2992641 : Nat := 4983230072969 + 3 ^ 40 * 2992641 * 2
def baseEnd_2992641 : Nat := 512221086450643670674867

theorem tailTrace_2992641 : CollatzResearch.WordTrace tailWord_2992641 prefixEnd_2992641 512221086450643670674867 := by
  unfold tailWord_2992641
  simp only [CollatzResearch.WordTrace]
  refine ⟨109150584351180234236969777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72767056234120156157979851 109150584351180234236969777)
  ·
    refine ⟨81862938263385175677727333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109150584351180234236969777 81862938263385175677727333)
    ·
      refine ⟨15349300924384720439573875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81862938263385175677727333 15349300924384720439573875)
      ·
        refine ⟨23023951386577080659360813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15349300924384720439573875 23023951386577080659360813)
        ·
          refine ⟨8633981769966405247260305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23023951386577080659360813 8633981769966405247260305)
          ·
            refine ⟨6475486327474803935445229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8633981769966405247260305 6475486327474803935445229)
            ·
              refine ⟨2428307372803051475791961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6475486327474803935445229 2428307372803051475791961)
              ·
                refine ⟨1821230529602288606843971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428307372803051475791961 1821230529602288606843971)
                ·
                  refine ⟨2731845794403432910265957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821230529602288606843971 2731845794403432910265957)
                  ·
                    refine ⟨512221086450643670674867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2731845794403432910265957 512221086450643670674867)
                    ·
                      rfl

theorem cell23_2992641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_2992641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992641 prefixEnd_2992641 := by exact prefixLift 2992641
  have htrace : WordTrace (prefixWord ++ tailWord_2992641) baseStart_2992641 baseEnd_2992641 := by
    simpa [prefixWord, tailWord_2992641, baseEnd_2992641] using wordTrace_append hprefix tailTrace_2992641
  have hstable : (prefixWord ++ tailWord_2992641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992641).length < 2 ^ (prefixWord ++ tailWord_2992641).sum := by decide
  have hdescent : baseEnd_2992641 < baseStart_2992641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992650 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_2992650 : Nat := 118140960795 + 2992650 * 2 ^ 59
def prefixEnd_2992650 : Nat := 4983230072969 + 3 ^ 40 * 2992650 * 2
def baseEnd_2992650 : Nat := 512222626892607158937353

theorem tailTrace_2992650 : CollatzResearch.WordTrace tailWord_2992650 prefixEnd_2992650 512222626892607158937353 := by
  unfold tailWord_2992650
  simp only [CollatzResearch.WordTrace]
  refine ⟨27287728152036907193511851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72767275072098419182698269 27287728152036907193511851)
  ·
    refine ⟨40931592228055360790267777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27287728152036907193511851 40931592228055360790267777)
    ·
      refine ⟨30698694171041520592700833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40931592228055360790267777 30698694171041520592700833)
      ·
        refine ⟨23024020628281140444525625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30698694171041520592700833 23024020628281140444525625)
        ·
          refine ⟨17268015471210855333394219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23024020628281140444525625 17268015471210855333394219)
          ·
            refine ⟨25902023206816283000091329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17268015471210855333394219 25902023206816283000091329)
            ·
              refine ⟨19426517405112212250068497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25902023206816283000091329 19426517405112212250068497)
              ·
                refine ⟨14569888053834159187551373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19426517405112212250068497 14569888053834159187551373)
                ·
                  refine ⟨5463708020187809695331765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14569888053834159187551373 5463708020187809695331765)
                  ·
                    refine ⟨512222626892607158937353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5463708020187809695331765 512222626892607158937353)
                    ·
                      rfl

theorem cell23_2992650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_2992650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992650 prefixEnd_2992650 := by exact prefixLift 2992650
  have htrace : WordTrace (prefixWord ++ tailWord_2992650) baseStart_2992650 baseEnd_2992650 := by
    simpa [prefixWord, tailWord_2992650, baseEnd_2992650] using wordTrace_append hprefix tailTrace_2992650
  have hstable : (prefixWord ++ tailWord_2992650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992650).length < 2 ^ (prefixWord ++ tailWord_2992650).sum := by decide
  have hdescent : baseEnd_2992650 < baseStart_2992650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992654 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_2992654 : Nat := 118140960795 + 2992654 * 2 ^ 59
def prefixEnd_2992654 : Nat := 4983230072969 + 3 ^ 40 * 2992654 * 2
def baseEnd_2992654 : Nat := 170741103844493273462449

theorem tailTrace_2992654 : CollatzResearch.WordTrace tailWord_2992654 prefixEnd_2992654 170741103844493273462449 := by
  unfold tailWord_2992654
  simp only [CollatzResearch.WordTrace]
  refine ⟨13643882312516642182149127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72767372333422091638128677 13643882312516642182149127)
  ·
    refine ⟨20465823468774963273223691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13643882312516642182149127 20465823468774963273223691)
    ·
      refine ⟨30698735203162444909835537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20465823468774963273223691 30698735203162444909835537)
      ·
        refine ⟨23024051402371833682376653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30698735203162444909835537 23024051402371833682376653)
        ·
          refine ⟨8634019275889437630891245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23024051402371833682376653 8634019275889437630891245)
          ·
            refine ⟨3237757228458539111584217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8634019275889437630891245 3237757228458539111584217)
            ·
              refine ⟨2428317921343904333688163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237757228458539111584217 2428317921343904333688163)
              ·
                refine ⟨3642476882015856500532245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2428317921343904333688163 3642476882015856500532245)
                ·
                  refine ⟨170741103844493273462449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3642476882015856500532245 170741103844493273462449)
                  ·
                    rfl

theorem cell23_2992654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_2992654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992654 prefixEnd_2992654 := by exact prefixLift 2992654
  have htrace : WordTrace (prefixWord ++ tailWord_2992654) baseStart_2992654 baseEnd_2992654 := by
    simpa [prefixWord, tailWord_2992654, baseEnd_2992654] using wordTrace_append hprefix tailTrace_2992654
  have hstable : (prefixWord ++ tailWord_2992654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992654).length < 2 ^ (prefixWord ++ tailWord_2992654).sum := by decide
  have hdescent : baseEnd_2992654 < baseStart_2992654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992692 : List Nat := [2, 5, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_2992692 : Nat := 118140960795 + 2992692 * 2 ^ 59
def prefixEnd_2992692 : Nat := 4983230072969 + 3 ^ 40 * 2992692 * 2
def baseEnd_2992692 : Nat := 512229815621770104162289

theorem tailTrace_2992692 : CollatzResearch.WordTrace tailWord_2992692 prefixEnd_2992692 512229815621770104162289 := by
  unfold tailWord_2992692
  simp only [CollatzResearch.WordTrace]
  refine ⟨54576222236997734973538165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72768296315996979964717553 54576222236997734973538165)
  ·
    refine ⟨5116520834718537653769203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54576222236997734973538165 5116520834718537653769203)
    ·
      refine ⟨7674781252077806480653805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5116520834718537653769203 7674781252077806480653805)
      ·
        refine ⟨2878042969529177430245177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7674781252077806480653805 2878042969529177430245177)
        ·
          refine ⟨2158532227146883072683883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878042969529177430245177 2158532227146883072683883)
          ·
            refine ⟨3237798340720324609025825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158532227146883072683883 3237798340720324609025825)
            ·
              refine ⟨2428348755540243456769369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237798340720324609025825 2428348755540243456769369)
              ·
                refine ⟨1821261566655182592577027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428348755540243456769369 1821261566655182592577027)
                ·
                  refine ⟨2731892349982773888865541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821261566655182592577027 2731892349982773888865541)
                  ·
                    refine ⟨512229815621770104162289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2731892349982773888865541 512229815621770104162289)
                    ·
                      rfl

theorem cell23_2992692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_2992692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992692 prefixEnd_2992692 := by exact prefixLift 2992692
  have htrace : WordTrace (prefixWord ++ tailWord_2992692) baseStart_2992692 baseEnd_2992692 := by
    simpa [prefixWord, tailWord_2992692, baseEnd_2992692] using wordTrace_append hprefix tailTrace_2992692
  have hstable : (prefixWord ++ tailWord_2992692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992692).length < 2 ^ (prefixWord ++ tailWord_2992692).sum := by decide
  have hdescent : baseEnd_2992692 < baseStart_2992692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992698 : List Nat := [3, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3]
def baseStart_2992698 : Nat := 118140960795 + 2992698 * 2 ^ 59
def prefixEnd_2992698 : Nat := 4983230072969 + 3 ^ 40 * 2992698 * 2
def baseEnd_2992698 : Nat := 1536692527749237289011839

theorem tailTrace_2992698 : CollatzResearch.WordTrace tailWord_2992698 prefixEnd_2992698 1536692527749237289011839 := by
  unfold tailWord_2992698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27288165827993433242948687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72768442207982488647863165 27288165827993433242948687)
  ·
    refine ⟨40932248741990149864423031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27288165827993433242948687 40932248741990149864423031)
    ·
      refine ⟨61398373112985224796634547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40932248741990149864423031 61398373112985224796634547)
      ·
        refine ⟨92097559669477837194951821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61398373112985224796634547 92097559669477837194951821)
        ·
          refine ⟨34536584876054188948106933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92097559669477837194951821 34536584876054188948106933)
          ·
            refine ⟨3237804832130080213885025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34536584876054188948106933 3237804832130080213885025)
            ·
              refine ⟨2428353624097560160413769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237804832130080213885025 2428353624097560160413769)
              ·
                refine ⟨1821265218073170120310327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428353624097560160413769 1821265218073170120310327)
                ·
                  refine ⟨2731897827109755180465491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821265218073170120310327 2731897827109755180465491)
                  ·
                    refine ⟨4097846740664632770698237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2731897827109755180465491 4097846740664632770698237)
                    ·
                      refine ⟨1536692527749237289011839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4097846740664632770698237 1536692527749237289011839)
                      ·
                        rfl

theorem cell23_2992698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_2992698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992698 prefixEnd_2992698 := by exact prefixLift 2992698
  have htrace : WordTrace (prefixWord ++ tailWord_2992698) baseStart_2992698 baseEnd_2992698 := by
    simpa [prefixWord, tailWord_2992698, baseEnd_2992698] using wordTrace_append hprefix tailTrace_2992698
  have hstable : (prefixWord ++ tailWord_2992698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992698).length < 2 ^ (prefixWord ++ tailWord_2992698).sum := by decide
  have hdescent : baseEnd_2992698 < baseStart_2992698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992737 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2992737 : Nat := 118140960795 + 2992737 * 2 ^ 59
def prefixEnd_2992737 : Nat := 4983230072969 + 3 ^ 40 * 2992737 * 2
def baseEnd_2992737 : Nat := 1536712553494762636424159

theorem tailTrace_2992737 : CollatzResearch.WordTrace tailWord_2992737 prefixEnd_2992737 1536712553494762636424159 := by
  unfold tailWord_2992737
  simp only [CollatzResearch.WordTrace]
  refine ⟨109154085758832442632464465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72769390505888295088309643 109154085758832442632464465)
  ·
    refine ⟨81865564319124331974348349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109154085758832442632464465 81865564319124331974348349)
    ·
      refine ⟨30699586619671624490380631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81865564319124331974348349 30699586619671624490380631)
      ·
        refine ⟨46049379929507436735570947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30699586619671624490380631 46049379929507436735570947)
        ·
          refine ⟨69074069894261155103356421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46049379929507436735570947 69074069894261155103356421)
          ·
            refine ⟨12951388105173966581879329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69074069894261155103356421 12951388105173966581879329)
            ·
              refine ⟨9713541078880474936409497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12951388105173966581879329 9713541078880474936409497)
              ·
                refine ⟨7285155809160356202307123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9713541078880474936409497 7285155809160356202307123)
                ·
                  refine ⟨10927733713740534303460685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7285155809160356202307123 10927733713740534303460685)
                  ·
                    refine ⟨4097900142652700363797757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10927733713740534303460685 4097900142652700363797757)
                    ·
                      refine ⟨1536712553494762636424159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4097900142652700363797757 1536712553494762636424159)
                      ·
                        rfl

theorem cell23_2992737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2992737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992737 prefixEnd_2992737 := by exact prefixLift 2992737
  have htrace : WordTrace (prefixWord ++ tailWord_2992737) baseStart_2992737 baseEnd_2992737 := by
    simpa [prefixWord, tailWord_2992737, baseEnd_2992737] using wordTrace_append hprefix tailTrace_2992737
  have hstable : (prefixWord ++ tailWord_2992737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992737).length < 2 ^ (prefixWord ++ tailWord_2992737).sum := by decide
  have hdescent : baseEnd_2992737 < baseStart_2992737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992747 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 5, 3, 2]
def baseStart_2992747 : Nat := 118140960795 + 2992747 * 2 ^ 59
def prefixEnd_2992747 : Nat := 4983230072969 + 3 ^ 40 * 2992747 * 2
def baseEnd_2992747 : Nat := 1536717688301307597299113

theorem tailTrace_2992747 : CollatzResearch.WordTrace tailWord_2992747 prefixEnd_2992747 1536717688301307597299113 := by
  unfold tailWord_2992747
  simp only [CollatzResearch.WordTrace]
  refine ⟨109154450488796214340328495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72769633659197476226885663 109154450488796214340328495)
  ·
    refine ⟨163731675733194321510492743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109154450488796214340328495 163731675733194321510492743)
    ·
      refine ⟨245597513599791482265739115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163731675733194321510492743 245597513599791482265739115)
      ·
        refine ⟨368396270399687223398608673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245597513599791482265739115 368396270399687223398608673)
        ·
          refine ⟨276297202799765417548956505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368396270399687223398608673 276297202799765417548956505)
          ·
            refine ⟨207222902099824063161717379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276297202799765417548956505 207222902099824063161717379)
            ·
              refine ⟨310834353149736094742576069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207222902099824063161717379 310834353149736094742576069)
              ·
                refine ⟨58281441215575517764233013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310834353149736094742576069 58281441215575517764233013)
                ·
                  refine ⟨5463885113960204790396845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58281441215575517764233013 5463885113960204790396845)
                  ·
                    refine ⟨2048956917735076796398817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5463885113960204790396845 2048956917735076796398817)
                    ·
                      refine ⟨1536717688301307597299113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2048956917735076796398817 1536717688301307597299113)
                      ·
                        rfl

theorem cell23_2992747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 3, 2].length) (baseStart_2992747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992747 prefixEnd_2992747 := by exact prefixLift 2992747
  have htrace : WordTrace (prefixWord ++ tailWord_2992747) baseStart_2992747 baseEnd_2992747 := by
    simpa [prefixWord, tailWord_2992747, baseEnd_2992747] using wordTrace_append hprefix tailTrace_2992747
  have hstable : (prefixWord ++ tailWord_2992747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992747).length < 2 ^ (prefixWord ++ tailWord_2992747).sum := by decide
  have hdescent : baseEnd_2992747 < baseStart_2992747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992822 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_2992822 : Nat := 118140960795 + 2992822 * 2 ^ 59
def prefixEnd_2992822 : Nat := 4983230072969 + 3 ^ 40 * 2992822 * 2
def baseEnd_2992822 : Nat := 1536756199350394803861269

theorem tailTrace_2992822 : CollatzResearch.WordTrace tailWord_2992822 prefixEnd_2992822 1536756199350394803861269 := by
  unfold tailWord_2992822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822324122720281384331795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72771457309016334766205813 6822324122720281384331795)
  ·
    refine ⟨10233486184080422076497693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6822324122720281384331795 10233486184080422076497693)
    ·
      refine ⟨3837557319030158278686635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10233486184080422076497693 3837557319030158278686635)
      ·
        refine ⟨5756335978545237418029953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837557319030158278686635 5756335978545237418029953)
        ·
          refine ⟨4317251983908928063522465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5756335978545237418029953 4317251983908928063522465)
          ·
            refine ⟨3237938987931696047641849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4317251983908928063522465 3237938987931696047641849)
            ·
              refine ⟨2428454240948772035731387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237938987931696047641849 2428454240948772035731387)
              ·
                refine ⟨3642681361423158053597081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2428454240948772035731387 3642681361423158053597081)
                ·
                  refine ⟨2732011021067368540197811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3642681361423158053597081 2732011021067368540197811)
                  ·
                    refine ⟨4098016531601052810296717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2732011021067368540197811 4098016531601052810296717)
                    ·
                      refine ⟨1536756199350394803861269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098016531601052810296717 1536756199350394803861269)
                      ·
                        rfl

theorem cell23_2992822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_2992822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992822 prefixEnd_2992822 := by exact prefixLift 2992822
  have htrace : WordTrace (prefixWord ++ tailWord_2992822) baseStart_2992822 baseEnd_2992822 := by
    simpa [prefixWord, tailWord_2992822, baseEnd_2992822] using wordTrace_append hprefix tailTrace_2992822
  have hstable : (prefixWord ++ tailWord_2992822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992822).length < 2 ^ (prefixWord ++ tailWord_2992822).sum := by decide
  have hdescent : baseEnd_2992822 < baseStart_2992822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992887 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_2992887 : Nat := 118140960795 + 2992887 * 2 ^ 59
def prefixEnd_2992887 : Nat := 4983230072969 + 3 ^ 40 * 2992887 * 2
def baseEnd_2992887 : Nat := 1536789575592937049548469

theorem tailTrace_2992887 : CollatzResearch.WordTrace tailWord_2992887 prefixEnd_2992887 1536789575592937049548469 := by
  unfold tailWord_2992887
  simp only [CollatzResearch.WordTrace]
  refine ⟨109159556708289018250424915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72773037805526012166949943 109159556708289018250424915)
  ·
    refine ⟨163739335062433527375637373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109159556708289018250424915 163739335062433527375637373)
    ·
      refine ⟨61402250648412572765864015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163739335062433527375637373 61402250648412572765864015)
      ·
        refine ⟨92103375972618859148796023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61402250648412572765864015 92103375972618859148796023)
        ·
          refine ⟨138155063958928288723194035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92103375972618859148796023 138155063958928288723194035)
          ·
            refine ⟨207232595938392433084791053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138155063958928288723194035 207232595938392433084791053)
            ·
              refine ⟨77712223476897162406796645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207232595938392433084791053 77712223476897162406796645)
              ·
                refine ⟨14571041901918217951274371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77712223476897162406796645 14571041901918217951274371)
                ·
                  refine ⟨21856562852877326926911557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14571041901918217951274371 21856562852877326926911557)
                  ·
                    refine ⟨4098105534914498798795917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21856562852877326926911557 4098105534914498798795917)
                    ·
                      refine ⟨1536789575592937049548469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098105534914498798795917 1536789575592937049548469)
                      ·
                        rfl

theorem cell23_2992887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_2992887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992887 prefixEnd_2992887 := by exact prefixLift 2992887
  have htrace : WordTrace (prefixWord ++ tailWord_2992887) baseStart_2992887 baseEnd_2992887 := by
    simpa [prefixWord, tailWord_2992887, baseEnd_2992887] using wordTrace_append hprefix tailTrace_2992887
  have hstable : (prefixWord ++ tailWord_2992887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992887).length < 2 ^ (prefixWord ++ tailWord_2992887).sum := by decide
  have hdescent : baseEnd_2992887 < baseStart_2992887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992904 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2992904 : Nat := 118140960795 + 2992904 * 2 ^ 59
def prefixEnd_2992904 : Nat := 4983230072969 + 3 ^ 40 * 2992904 * 2
def baseEnd_2992904 : Nat := 1536798304764063483035891

theorem tailTrace_2992904 : CollatzResearch.WordTrace tailWord_2992904 prefixEnd_2992904 1536798304764063483035891 := by
  unfold tailWord_2992904
  simp only [CollatzResearch.WordTrace]
  refine ⟨54580088374613715076896883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72773451166151620102529177 54580088374613715076896883)
  ·
    refine ⟨81870132561920572615345325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54580088374613715076896883 81870132561920572615345325)
    ·
      refine ⟨30701299710720214730754497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81870132561920572615345325 30701299710720214730754497)
      ·
        refine ⟨23025974783040161048065873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30701299710720214730754497 23025974783040161048065873)
        ·
          refine ⟨17269481087280120786049405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23025974783040161048065873 17269481087280120786049405)
          ·
            refine ⟨6476055407730045294768527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17269481087280120786049405 6476055407730045294768527)
            ·
              refine ⟨9714083111595067942152791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476055407730045294768527 9714083111595067942152791)
              ·
                refine ⟨14571124667392601913229187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9714083111595067942152791 14571124667392601913229187)
                ·
                  refine ⟨21856687001088902869843781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14571124667392601913229187 21856687001088902869843781)
                  ·
                    refine ⟨4098128812704169288095709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21856687001088902869843781 4098128812704169288095709)
                    ·
                      refine ⟨1536798304764063483035891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098128812704169288095709 1536798304764063483035891)
                      ·
                        rfl

theorem cell23_2992904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2992904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992904 prefixEnd_2992904 := by exact prefixLift 2992904
  have htrace : WordTrace (prefixWord ++ tailWord_2992904) baseStart_2992904 baseEnd_2992904 := by
    simpa [prefixWord, tailWord_2992904, baseEnd_2992904] using wordTrace_append hprefix tailTrace_2992904
  have hstable : (prefixWord ++ tailWord_2992904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992904).length < 2 ^ (prefixWord ++ tailWord_2992904).sum := by decide
  have hdescent : baseEnd_2992904 < baseStart_2992904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992911 : List Nat := [1, 1, 2, 1, 1, 1, 8, 3, 1, 4]
def baseStart_2992911 : Nat := 118140960795 + 2992911 * 2 ^ 59
def prefixEnd_2992911 : Nat := 4983230072969 + 3 ^ 40 * 2992911 * 2
def baseEnd_2992911 : Nat := 512267299709548318549453

theorem tailTrace_2992911 : CollatzResearch.WordTrace tailWord_2992911 prefixEnd_2992911 512267299709548318549453 := by
  unfold tailWord_2992911
  simp only [CollatzResearch.WordTrace]
  refine ⟨109160432060202070349298587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72773621373468046899532391 109160432060202070349298587)
  ·
    refine ⟨163740648090303105523947881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109160432060202070349298587 163740648090303105523947881)
    ·
      refine ⟨122805486067727329142960911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163740648090303105523947881 122805486067727329142960911)
      ·
        refine ⟨184208229101590993714441367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122805486067727329142960911 184208229101590993714441367)
        ·
          refine ⟨276312343652386490571662051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184208229101590993714441367 276312343652386490571662051)
          ·
            refine ⟨414468515478579735857493077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276312343652386490571662051 414468515478579735857493077)
            ·
              refine ⟨4857052915764606279579997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 414468515478579735857493077 4857052915764606279579997)
              ·
                refine ⟨1821394843411727354842499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4857052915764606279579997 1821394843411727354842499)
                ·
                  refine ⟨2732092265117591032263749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821394843411727354842499 2732092265117591032263749)
                  ·
                    refine ⟨512267299709548318549453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2732092265117591032263749 512267299709548318549453)
                    ·
                      rfl

theorem cell23_2992911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 4].length) (baseStart_2992911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992911 prefixEnd_2992911 := by exact prefixLift 2992911
  have htrace : WordTrace (prefixWord ++ tailWord_2992911) baseStart_2992911 baseEnd_2992911 := by
    simpa [prefixWord, tailWord_2992911, baseEnd_2992911] using wordTrace_append hprefix tailTrace_2992911
  have hstable : (prefixWord ++ tailWord_2992911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992911).length < 2 ^ (prefixWord ++ tailWord_2992911).sum := by decide
  have hdescent : baseEnd_2992911 < baseStart_2992911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992924 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 6]
def baseStart_2992924 : Nat := 118140960795 + 2992924 * 2 ^ 59
def prefixEnd_2992924 : Nat := 4983230072969 + 3 ^ 40 * 2992924 * 2
def baseEnd_2992924 : Nat := 170756508264128156087311

theorem tailTrace_2992924 : CollatzResearch.WordTrace tailWord_2992924 prefixEnd_2992924 170756508264128156087311 := by
  unfold tailWord_2992924
  simp only [CollatzResearch.WordTrace]
  refine ⟨54580453104577486784760913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72773937472769982379681217 54580453104577486784760913)
  ·
    refine ⟨40935339828433115088570685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54580453104577486784760913 40935339828433115088570685)
    ·
      refine ⟨15350752435662418158214007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40935339828433115088570685 15350752435662418158214007)
      ·
        refine ⟨23026128653493627237321011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15350752435662418158214007 23026128653493627237321011)
        ·
          refine ⟨34539192980240440855981517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23026128653493627237321011 34539192980240440855981517)
          ·
            refine ⟨12952197367590165320993069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34539192980240440855981517 12952197367590165320993069)
            ·
              refine ⟨4857074012846311995372401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12952197367590165320993069 4857074012846311995372401)
              ·
                refine ⟨3642805509634733996529301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4857074012846311995372401 3642805509634733996529301)
                ·
                  refine ⟨170756508264128156087311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3642805509634733996529301 170756508264128156087311)
                  ·
                    rfl

theorem cell23_2992924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_2992924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992924 prefixEnd_2992924 := by exact prefixLift 2992924
  have htrace : WordTrace (prefixWord ++ tailWord_2992924) baseStart_2992924 baseEnd_2992924 := by
    simpa [prefixWord, tailWord_2992924, baseEnd_2992924] using wordTrace_append hprefix tailTrace_2992924
  have hstable : (prefixWord ++ tailWord_2992924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992924).length < 2 ^ (prefixWord ++ tailWord_2992924).sum := by decide
  have hdescent : baseEnd_2992924 < baseStart_2992924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992927 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_2992927 : Nat := 118140960795 + 2992927 * 2 ^ 59
def prefixEnd_2992927 : Nat := 4983230072969 + 3 ^ 40 * 2992927 * 2
def baseEnd_2992927 : Nat := 1536810114819116893048285

theorem tailTrace_2992927 : CollatzResearch.WordTrace tailWord_2992927 prefixEnd_2992927 1536810114819116893048285 := by
  unfold tailWord_2992927
  simp only [CollatzResearch.WordTrace]
  refine ⟨109161015628144105081881035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72774010418762736721254023 109161015628144105081881035)
  ·
    refine ⟨163741523442216157622821553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109161015628144105081881035 163741523442216157622821553)
    ·
      refine ⟨122806142581662118217116165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163741523442216157622821553 122806142581662118217116165)
      ·
        refine ⟨23026151734061647165709281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122806142581662118217116165 23026151734061647165709281)
        ·
          refine ⟨17269613800546235374281961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23026151734061647165709281 17269613800546235374281961)
          ·
            refine ⟨12952210350409676530711471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17269613800546235374281961 12952210350409676530711471)
            ·
              refine ⟨19428315525614514796067207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12952210350409676530711471 19428315525614514796067207)
              ·
                refine ⟨29142473288421772194100811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19428315525614514796067207 29142473288421772194100811)
                ·
                  refine ⟨43713709932632658291151217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29142473288421772194100811 43713709932632658291151217)
                  ·
                    refine ⟨32785282449474493718363413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43713709932632658291151217 32785282449474493718363413)
                    ·
                      refine ⟨1536810114819116893048285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32785282449474493718363413 1536810114819116893048285)
                      ·
                        rfl

theorem cell23_2992927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_2992927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992927 prefixEnd_2992927 := by exact prefixLift 2992927
  have htrace : WordTrace (prefixWord ++ tailWord_2992927) baseStart_2992927 baseEnd_2992927 := by
    simpa [prefixWord, tailWord_2992927, baseEnd_2992927] using wordTrace_append hprefix tailTrace_2992927
  have hstable : (prefixWord ++ tailWord_2992927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992927).length < 2 ^ (prefixWord ++ tailWord_2992927).sum := by decide
  have hdescent : baseEnd_2992927 < baseStart_2992927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992967 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 3, 6]
def baseStart_2992967 : Nat := 118140960795 + 2992967 * 2 ^ 59
def prefixEnd_2992967 : Nat := 4983230072969 + 3 ^ 40 * 2992967 * 2
def baseEnd_2992967 : Nat := 512276884681765578849367

theorem tailTrace_2992967 : CollatzResearch.WordTrace tailWord_2992967 prefixEnd_2992967 512276884681765578849367 := by
  unfold tailWord_2992967
  simp only [CollatzResearch.WordTrace]
  refine ⟨109162474547999191913337155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72774983031999461275558103 109162474547999191913337155)
  ·
    refine ⟨163743711821998787870005733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109162474547999191913337155 163743711821998787870005733)
    ·
      refine ⟨30701945966624772725626075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163743711821998787870005733 30701945966624772725626075)
      ·
        refine ⟨46052918949937159088439113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30701945966624772725626075 46052918949937159088439113)
        ·
          refine ⟨34539689212452869316329335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46052918949937159088439113 34539689212452869316329335)
          ·
            refine ⟨51809533818679303974494003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34539689212452869316329335 51809533818679303974494003)
            ·
              refine ⟨77714300728018955961741005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51809533818679303974494003 77714300728018955961741005)
              ·
                refine ⟨29142862773007108485652877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77714300728018955961741005 29142862773007108485652877)
                ·
                  refine ⟨10928573539877665682119829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29142862773007108485652877 10928573539877665682119829)
                  ·
                    refine ⟨512276884681765578849367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10928573539877665682119829 512276884681765578849367)
                    ·
                      rfl

theorem cell23_2992967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_2992967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992967 prefixEnd_2992967 := by exact prefixLift 2992967
  have htrace : WordTrace (prefixWord ++ tailWord_2992967) baseStart_2992967 baseEnd_2992967 := by
    simpa [prefixWord, tailWord_2992967, baseEnd_2992967] using wordTrace_append hprefix tailTrace_2992967
  have hstable : (prefixWord ++ tailWord_2992967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992967).length < 2 ^ (prefixWord ++ tailWord_2992967).sum := by decide
  have hdescent : baseEnd_2992967 < baseStart_2992967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992985 : List Nat := [1, 2, 1, 2, 2, 5, 3, 2, 1, 1, 3]
def baseStart_2992985 : Nat := 118140960795 + 2992985 * 2 ^ 59
def prefixEnd_2992985 : Nat := 4983230072969 + 3 ^ 40 * 2992985 * 2
def baseEnd_2992985 : Nat := 1536839896697077666123019

theorem tailTrace_2992985 : CollatzResearch.WordTrace tailWord_2992985 prefixEnd_2992985 1536839896697077666123019 := by
  unfold tailWord_2992985
  simp only [CollatzResearch.WordTrace]
  refine ⟨109163131061933980987492409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72775420707955987324994939 109163131061933980987492409)
  ·
    refine ⟨81872348296450485740619307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109163131061933980987492409 81872348296450485740619307)
    ·
      refine ⟨122808522444675728610928961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81872348296450485740619307 122808522444675728610928961)
      ·
        refine ⟨92106391833506796458196721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122808522444675728610928961 92106391833506796458196721)
        ·
          refine ⟨69079793875130097343647541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92106391833506796458196721 69079793875130097343647541)
          ·
            refine ⟨6476230675793446625966957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69079793875130097343647541 6476230675793446625966957)
            ·
              refine ⟨2428586503422542484737609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6476230675793446625966957 2428586503422542484737609)
              ·
                refine ⟨1821439877566906863553207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428586503422542484737609 1821439877566906863553207)
                ·
                  refine ⟨2732159816350360295329811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821439877566906863553207 2732159816350360295329811)
                  ·
                    refine ⟨4098239724525540442994717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2732159816350360295329811 4098239724525540442994717)
                    ·
                      refine ⟨1536839896697077666123019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098239724525540442994717 1536839896697077666123019)
                      ·
                        rfl

theorem cell23_2992985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_2992985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992985 prefixEnd_2992985 := by exact prefixLift 2992985
  have htrace : WordTrace (prefixWord ++ tailWord_2992985) baseStart_2992985 baseEnd_2992985 := by
    simpa [prefixWord, tailWord_2992985, baseEnd_2992985] using wordTrace_append hprefix tailTrace_2992985
  have hstable : (prefixWord ++ tailWord_2992985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992985).length < 2 ^ (prefixWord ++ tailWord_2992985).sum := by decide
  have hdescent : baseEnd_2992985 < baseStart_2992985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992997 : List Nat := [1, 3, 1, 3, 1, 1, 3, 10]
def baseStart_2992997 : Nat := 118140960795 + 2992997 * 2 ^ 59
def prefixEnd_2992997 : Nat := 4983230072969 + 3 ^ 40 * 2992997 * 2
def baseEnd_2992997 : Nat := 56920224387590059969369

theorem tailTrace_2992997 : CollatzResearch.WordTrace tailWord_2992997 prefixEnd_2992997 56920224387590059969369 := by
  unfold tailWord_2992997
  simp only [CollatzResearch.WordTrace]
  refine ⟨109163568737890507036929245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72775712491927004691286163 109163568737890507036929245)
  ·
    refine ⟨40936338276708940138848467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109163568737890507036929245 40936338276708940138848467)
    ·
      refine ⟨61404507415063410208272701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40936338276708940138848467 61404507415063410208272701)
      ·
        refine ⟨23026690280648778828102263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61404507415063410208272701 23026690280648778828102263)
        ·
          refine ⟨34540035420973168242153395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23026690280648778828102263 34540035420973168242153395)
          ·
            refine ⟨51810053131459752363230093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34540035420973168242153395 51810053131459752363230093)
            ·
              refine ⟨19428769924297407136211285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51810053131459752363230093 19428769924297407136211285)
              ·
                refine ⟨56920224387590059969369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19428769924297407136211285 56920224387590059969369)
                ·
                  rfl

theorem cell23_2992997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 10].length) (baseStart_2992997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2992997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2992997 prefixEnd_2992997 := by exact prefixLift 2992997
  have htrace : WordTrace (prefixWord ++ tailWord_2992997) baseStart_2992997 baseEnd_2992997 := by
    simpa [prefixWord, tailWord_2992997, baseEnd_2992997] using wordTrace_append hprefix tailTrace_2992997
  have hstable : (prefixWord ++ tailWord_2992997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992997).length < 2 ^ (prefixWord ++ tailWord_2992997).sum := by decide
  have hdescent : baseEnd_2992997 < baseStart_2992997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993004 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_2993004 : Nat := 118140960795 + 2993004 * 2 ^ 59
def prefixEnd_2993004 : Nat := 4983230072969 + 3 ^ 40 * 2993004 * 2
def baseEnd_2993004 : Nat := 1536849652829513091785431

theorem tailTrace_2993004 : CollatzResearch.WordTrace tailWord_2993004 prefixEnd_2993004 1536849652829513091785431 := by
  unfold tailWord_2993004
  simp only [CollatzResearch.WordTrace]
  refine ⟨54581912024432573616217033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72775882699243431488289377 54581912024432573616217033)
  ·
    refine ⟨40936434018324430212162775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54581912024432573616217033 40936434018324430212162775)
    ·
      refine ⟨61404651027486645318244163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40936434018324430212162775 61404651027486645318244163)
      ·
        refine ⟨92106976541229967977366245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61404651027486645318244163 92106976541229967977366245)
        ·
          refine ⟨17270058101480618995756171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92106976541229967977366245 17270058101480618995756171)
          ·
            refine ⟨25905087152220928493634257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17270058101480618995756171 25905087152220928493634257)
            ·
              refine ⟨19428815364165696370225693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25905087152220928493634257 19428815364165696370225693)
              ·
                refine ⟨7285805761562136138834635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19428815364165696370225693 7285805761562136138834635)
                ·
                  refine ⟨10928708642343204208251953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7285805761562136138834635 10928708642343204208251953)
                  ·
                    refine ⟨8196531481757403156188965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10928708642343204208251953 8196531481757403156188965)
                    ·
                      refine ⟨1536849652829513091785431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8196531481757403156188965 1536849652829513091785431)
                      ·
                        rfl

theorem cell23_2993004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_2993004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993004 prefixEnd_2993004 := by exact prefixLift 2993004
  have htrace : WordTrace (prefixWord ++ tailWord_2993004) baseStart_2993004 baseEnd_2993004 := by
    simpa [prefixWord, tailWord_2993004, baseEnd_2993004] using wordTrace_append hprefix tailTrace_2993004
  have hstable : (prefixWord ++ tailWord_2993004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993004).length < 2 ^ (prefixWord ++ tailWord_2993004).sum := by decide
  have hdescent : baseEnd_2993004 < baseStart_2993004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993011 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 3]
def baseStart_2993011 : Nat := 118140960795 + 2993011 * 2 ^ 59
def prefixEnd_2993011 : Nat := 4983230072969 + 3 ^ 40 * 2993011 * 2
def baseEnd_2993011 : Nat := 1536853247194094564397899

theorem tailTrace_2993011 : CollatzResearch.WordTrace tailWord_2993011 prefixEnd_2993011 1536853247194094564397899 := by
  unfold tailWord_2993011
  simp only [CollatzResearch.WordTrace]
  refine ⟨109164079359839787427938887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72776052906559858285292591 109164079359839787427938887)
  ·
    refine ⟨163746119039759681141908331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109164079359839787427938887 163746119039759681141908331)
    ·
      refine ⟨245619178559639521712862497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163746119039759681141908331 245619178559639521712862497)
      ·
        refine ⟨184214383919729641284646873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245619178559639521712862497 184214383919729641284646873)
        ·
          refine ⟨138160787939797230963485155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184214383919729641284646873 138160787939797230963485155)
          ·
            refine ⟨207241181909695846445227733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138160787939797230963485155 207241181909695846445227733)
            ·
              refine ⟨4857215201008496401060025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 207241181909695846445227733 4857215201008496401060025)
              ·
                refine ⟨3642911400756372300795019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4857215201008496401060025 3642911400756372300795019)
                ·
                  refine ⟨5464367101134558451192529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3642911400756372300795019 5464367101134558451192529)
                  ·
                    refine ⟨4098275325850918838394397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5464367101134558451192529 4098275325850918838394397)
                    ·
                      refine ⟨1536853247194094564397899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098275325850918838394397 1536853247194094564397899)
                      ·
                        rfl

theorem cell23_2993011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 3].length) (baseStart_2993011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993011 prefixEnd_2993011 := by exact prefixLift 2993011
  have htrace : WordTrace (prefixWord ++ tailWord_2993011) baseStart_2993011 baseEnd_2993011 := by
    simpa [prefixWord, tailWord_2993011, baseEnd_2993011] using wordTrace_append hprefix tailTrace_2993011
  have hstable : (prefixWord ++ tailWord_2993011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993011).length < 2 ^ (prefixWord ++ tailWord_2993011).sum := by decide
  have hdescent : baseEnd_2993011 < baseStart_2993011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993044 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_2993044 : Nat := 118140960795 + 2993044 * 2 ^ 59
def prefixEnd_2993044 : Nat := 4983230072969 + 3 ^ 40 * 2993044 * 2
def baseEnd_2993044 : Nat := 512290064018564311761749

theorem tailTrace_2993044 : CollatzResearch.WordTrace tailWord_2993044 prefixEnd_2993044 512290064018564311761749 := by
  unfold tailWord_2993044
  simp only [CollatzResearch.WordTrace]
  refine ⟨54582641484360117031945093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72776855312480156042593457 54582641484360117031945093)
  ·
    refine ⟨10234245278317521943489705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54582641484360117031945093 10234245278317521943489705)
    ·
      refine ⟨7675683958738141457617279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10234245278317521943489705 7675683958738141457617279)
      ·
        refine ⟨11513525938107212186425919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7675683958738141457617279 11513525938107212186425919)
        ·
          refine ⟨17270288907160818279638879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11513525938107212186425919 17270288907160818279638879)
          ·
            refine ⟨25905433360741227419458319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17270288907160818279638879 25905433360741227419458319)
            ·
              refine ⟨38858150041111841129187479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25905433360741227419458319 38858150041111841129187479)
              ·
                refine ⟨58287225061667761693781219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38858150041111841129187479 58287225061667761693781219)
                ·
                  refine ⟨87430837592501642540671829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58287225061667761693781219 87430837592501642540671829)
                  ·
                    refine ⟨512290064018564311761749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87430837592501642540671829 512290064018564311761749)
                    ·
                      rfl

theorem cell23_2993044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_2993044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993044 prefixEnd_2993044 := by exact prefixLift 2993044
  have htrace : WordTrace (prefixWord ++ tailWord_2993044) baseStart_2993044 baseEnd_2993044 := by
    simpa [prefixWord, tailWord_2993044, baseEnd_2993044] using wordTrace_append hprefix tailTrace_2993044
  have hstable : (prefixWord ++ tailWord_2993044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993044).length < 2 ^ (prefixWord ++ tailWord_2993044).sum := by decide
  have hdescent : baseEnd_2993044 < baseStart_2993044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993058 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2993058 : Nat := 118140960795 + 2993058 * 2 ^ 59
def prefixEnd_2993058 : Nat := 4983230072969 + 3 ^ 40 * 2993058 * 2
def baseEnd_2993058 : Nat := 1536877380784855880510183

theorem tailTrace_2993058 : CollatzResearch.WordTrace tailWord_2993058 prefixEnd_2993058 1536877380784855880510183 := by
  unfold tailWord_2993058
  simp only [CollatzResearch.WordTrace]
  refine ⟨27291448397667378613724957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72777195727113009636599885 27291448397667378613724957)
  ·
    refine ⟨10234293149125266980146859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27291448397667378613724957 10234293149125266980146859)
    ·
      refine ⟨15351439723687900470220289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10234293149125266980146859 15351439723687900470220289)
      ·
        refine ⟨11513579792765925352665217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15351439723687900470220289 11513579792765925352665217)
        ·
          refine ⟨8635184844574444014498913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11513579792765925352665217 8635184844574444014498913)
          ·
            refine ⟨6476388633430833010874185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8635184844574444014498913 6476388633430833010874185)
            ·
              refine ⟨4857291475073124758155639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6476388633430833010874185 4857291475073124758155639)
              ·
                refine ⟨7285937212609687137233459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857291475073124758155639 7285937212609687137233459)
                ·
                  refine ⟨10928905818914530705850189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7285937212609687137233459 10928905818914530705850189)
                  ·
                    refine ⟨4098339682092949014693821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10928905818914530705850189 4098339682092949014693821)
                    ·
                      refine ⟨1536877380784855880510183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098339682092949014693821 1536877380784855880510183)
                      ·
                        rfl

theorem cell23_2993058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2993058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993058 prefixEnd_2993058 := by exact prefixLift 2993058
  have htrace : WordTrace (prefixWord ++ tailWord_2993058) baseStart_2993058 baseEnd_2993058 := by
    simpa [prefixWord, tailWord_2993058, baseEnd_2993058] using wordTrace_append hprefix tailTrace_2993058
  have hstable : (prefixWord ++ tailWord_2993058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993058).length < 2 ^ (prefixWord ++ tailWord_2993058).sum := by decide
  have hdescent : baseEnd_2993058 < baseStart_2993058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993085 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_2993085 : Nat := 118140960795 + 2993085 * 2 ^ 59
def prefixEnd_2993085 : Nat := 4983230072969 + 3 ^ 40 * 2993085 * 2
def baseEnd_2993085 : Nat := 1536891244762527274872559

theorem tailTrace_2993085 : CollatzResearch.WordTrace tailWord_2993085 prefixEnd_2993085 1536891244762527274872559 := by
  unfold tailWord_2993085
  simp only [CollatzResearch.WordTrace]
  refine ⟨109166778361571698066132709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72777852241047798710755139 109166778361571698066132709)
  ·
    refine ⟨20468770942794693387399883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109166778361571698066132709 20468770942794693387399883)
    ·
      refine ⟨30703156414192040081099825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20468770942794693387399883 30703156414192040081099825)
      ·
        refine ⟨23027367310644030060824869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30703156414192040081099825 23027367310644030060824869)
        ·
          refine ⟨4317631370745755636404663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23027367310644030060824869 4317631370745755636404663)
          ·
            refine ⟨6476447056118633454606995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317631370745755636404663 6476447056118633454606995)
            ·
              refine ⟨9714670584177950181910493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476447056118633454606995 9714670584177950181910493)
              ·
                refine ⟨3643001469066731318216435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9714670584177950181910493 3643001469066731318216435)
                ·
                  refine ⟨5464502203600096977324653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643001469066731318216435 5464502203600096977324653)
                  ·
                    refine ⟨2049188326350036366496745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5464502203600096977324653 2049188326350036366496745)
                    ·
                      refine ⟨1536891244762527274872559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049188326350036366496745 1536891244762527274872559)
                      ·
                        rfl

theorem cell23_2993085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_2993085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993085 prefixEnd_2993085 := by exact prefixLift 2993085
  have htrace : WordTrace (prefixWord ++ tailWord_2993085) baseStart_2993085 baseEnd_2993085 := by
    simpa [prefixWord, tailWord_2993085, baseEnd_2993085] using wordTrace_append hprefix tailTrace_2993085
  have hstable : (prefixWord ++ tailWord_2993085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993085).length < 2 ^ (prefixWord ++ tailWord_2993085).sum := by decide
  have hdescent : baseEnd_2993085 < baseStart_2993085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993144 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_2993144 : Nat := 118140960795 + 2993144 * 2 ^ 59
def prefixEnd_2993144 : Nat := 4983230072969 + 3 ^ 40 * 2993144 * 2
def baseEnd_2993144 : Nat := 1536921540121142544034787

theorem tailTrace_2993144 : CollatzResearch.WordTrace tailWord_2993144 prefixEnd_2993144 1536921540121142544034787 := by
  unfold tailWord_2993144
  simp only [CollatzResearch.WordTrace]
  refine ⟨54584465134178975571265243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72779286845571967428353657 54584465134178975571265243)
  ·
    refine ⟨81876697701268463356897865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54584465134178975571265243 81876697701268463356897865)
    ·
      refine ⟨61407523275951347517673399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81876697701268463356897865 61407523275951347517673399)
      ·
        refine ⟨92111284913927021276510099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61407523275951347517673399 92111284913927021276510099)
        ·
          refine ⟨138166927370890531914765149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92111284913927021276510099 138166927370890531914765149)
          ·
            refine ⟨51812597764083949468036931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138166927370890531914765149 51812597764083949468036931)
            ·
              refine ⟨77718896646125924202055397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51812597764083949468036931 77718896646125924202055397)
              ·
                refine ⟨14572293121148610787885387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77718896646125924202055397 14572293121148610787885387)
                ·
                  refine ⟨21858439681722916181828081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14572293121148610787885387 21858439681722916181828081)
                  ·
                    refine ⟨16393829761292187136371061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21858439681722916181828081 16393829761292187136371061)
                    ·
                      refine ⟨1536921540121142544034787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16393829761292187136371061 1536921540121142544034787)
                      ·
                        rfl

theorem cell23_2993144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_2993144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993144 prefixEnd_2993144 := by exact prefixLift 2993144
  have htrace : WordTrace (prefixWord ++ tailWord_2993144) baseStart_2993144 baseEnd_2993144 := by
    simpa [prefixWord, tailWord_2993144, baseEnd_2993144] using wordTrace_append hprefix tailTrace_2993144
  have hstable : (prefixWord ++ tailWord_2993144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993144).length < 2 ^ (prefixWord ++ tailWord_2993144).sum := by decide
  have hdescent : baseEnd_2993144 < baseStart_2993144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993171 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 1, 6, 2]
def baseStart_2993171 : Nat := 118140960795 + 2993171 * 2 ^ 59
def prefixEnd_2993171 : Nat := 4983230072969 + 3 ^ 40 * 2993171 * 2
def baseEnd_2993171 : Nat := 1536935404098813938397163

theorem tailTrace_2993171 : CollatzResearch.WordTrace tailWord_2993171 prefixEnd_2993171 1536935404098813938397163 := by
  unfold tailWord_2993171
  simp only [CollatzResearch.WordTrace]
  refine ⟨109169915039260134753763367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72779943359506756502508911 109169915039260134753763367)
  ·
    refine ⟨163754872558890202130645051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109169915039260134753763367 163754872558890202130645051)
    ·
      refine ⟨245632308838335303195967577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163754872558890202130645051 245632308838335303195967577)
      ·
        refine ⟨184224231628751477396975683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245632308838335303195967577 184224231628751477396975683)
        ·
          refine ⟨276336347443127216095463525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184224231628751477396975683 276336347443127216095463525)
          ·
            refine ⟨51813065145586353017899411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276336347443127216095463525 51813065145586353017899411)
            ·
              refine ⟨77719597718379529526849117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51813065145586353017899411 77719597718379529526849117)
              ·
                refine ⟨29144849144392323572568419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77719597718379529526849117 29144849144392323572568419)
                ·
                  refine ⟨43717273716588485358852629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29144849144392323572568419 43717273716588485358852629)
                  ·
                    refine ⟨2049247205465085251196217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43717273716588485358852629 2049247205465085251196217)
                    ·
                      refine ⟨1536935404098813938397163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049247205465085251196217 1536935404098813938397163)
                      ·
                        rfl

theorem cell23_2993171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 6, 2].length) (baseStart_2993171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993171 prefixEnd_2993171 := by exact prefixLift 2993171
  have htrace : WordTrace (prefixWord ++ tailWord_2993171) baseStart_2993171 baseEnd_2993171 := by
    simpa [prefixWord, tailWord_2993171, baseEnd_2993171] using wordTrace_append hprefix tailTrace_2993171
  have hstable : (prefixWord ++ tailWord_2993171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993171).length < 2 ^ (prefixWord ++ tailWord_2993171).sum := by decide
  have hdescent : baseEnd_2993171 < baseStart_2993171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993188 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2993188 : Nat := 118140960795 + 2993188 * 2 ^ 59
def prefixEnd_2993188 : Nat := 4983230072969 + 3 ^ 40 * 2993188 * 2
def baseEnd_2993188 : Nat := 1536944133269940371884585

theorem tailTrace_2993188 : CollatzResearch.WordTrace tailWord_2993188 prefixEnd_2993188 1536944133269940371884585 := by
  unfold tailWord_2993188
  simp only [CollatzResearch.WordTrace]
  refine ⟨54585267540099273328566109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72780356720132364438088145 54585267540099273328566109)
  ·
    refine ⟨20469475327537227498212291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54585267540099273328566109 20469475327537227498212291)
    ·
      refine ⟨30704212991305841247318437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20469475327537227498212291 30704212991305841247318437)
      ·
        refine ⟨5757039935869845233872207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30704212991305841247318437 5757039935869845233872207)
        ·
          refine ⟨8635559903804767850808311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757039935869845233872207 8635559903804767850808311)
          ·
            refine ⟨12953339855707151776212467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8635559903804767850808311 12953339855707151776212467)
            ·
              refine ⟨19430009783560727664318701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12953339855707151776212467 19430009783560727664318701)
              ·
                refine ⟨7286253668835272874119513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19430009783560727664318701 7286253668835272874119513)
                ·
                  refine ⟨5464690251626454655589635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7286253668835272874119513 5464690251626454655589635)
                  ·
                    refine ⟨8197035377439681983384453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464690251626454655589635 8197035377439681983384453)
                    ·
                      refine ⟨1536944133269940371884585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8197035377439681983384453 1536944133269940371884585)
                      ·
                        rfl

theorem cell23_2993188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2993188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993188 prefixEnd_2993188 := by exact prefixLift 2993188
  have htrace : WordTrace (prefixWord ++ tailWord_2993188) baseStart_2993188 baseEnd_2993188 := by
    simpa [prefixWord, tailWord_2993188, baseEnd_2993188] using wordTrace_append hprefix tailTrace_2993188
  have hstable : (prefixWord ++ tailWord_2993188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993188).length < 2 ^ (prefixWord ++ tailWord_2993188).sum := by decide
  have hdescent : baseEnd_2993188 < baseStart_2993188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993208 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_2993208 : Nat := 118140960795 + 2993208 * 2 ^ 59
def prefixEnd_2993208 : Nat := 4983230072969 + 3 ^ 40 * 2993208 * 2
def baseEnd_2993208 : Nat := 1536954402883030293634493

theorem tailTrace_2993208 : CollatzResearch.WordTrace tailWord_2993208 prefixEnd_2993208 1536954402883030293634493 := by
  unfold tailWord_2993208
  simp only [CollatzResearch.WordTrace]
  refine ⟨54585632270063045036430139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72780843026750726715240185 54585632270063045036430139)
  ·
    refine ⟨81878448405094567554645209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54585632270063045036430139 81878448405094567554645209)
    ·
      refine ⟨61408836303820925665983907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81878448405094567554645209 61408836303820925665983907)
      ·
        refine ⟨92113254455731388498975861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61408836303820925665983907 92113254455731388498975861)
        ·
          refine ⟨8635617605224817671778987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92113254455731388498975861 8635617605224817671778987)
          ·
            refine ⟨12953426407837226507668481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8635617605224817671778987 12953426407837226507668481)
            ·
              refine ⟨9715069805877919880751361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12953426407837226507668481 9715069805877919880751361)
              ·
                refine ⟨7286302354408439910563521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9715069805877919880751361 7286302354408439910563521)
                ·
                  refine ⟨5464726765806329932922641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7286302354408439910563521 5464726765806329932922641)
                  ·
                    refine ⟨4098545074354747449691981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5464726765806329932922641 4098545074354747449691981)
                    ·
                      refine ⟨1536954402883030293634493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098545074354747449691981 1536954402883030293634493)
                      ·
                        rfl

theorem cell23_2993208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_2993208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993208 prefixEnd_2993208 := by exact prefixLift 2993208
  have htrace : WordTrace (prefixWord ++ tailWord_2993208) baseStart_2993208 baseEnd_2993208 := by
    simpa [prefixWord, tailWord_2993208, baseEnd_2993208] using wordTrace_append hprefix tailTrace_2993208
  have hstable : (prefixWord ++ tailWord_2993208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993208).length < 2 ^ (prefixWord ++ tailWord_2993208).sum := by decide
  have hdescent : baseEnd_2993208 < baseStart_2993208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993222 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_2993222 : Nat := 118140960795 + 2993222 * 2 ^ 59
def prefixEnd_2993222 : Nat := 4983230072969 + 3 ^ 40 * 2993222 * 2
def baseEnd_2993222 : Nat := 1536961591612193238859429

theorem tailTrace_2993222 : CollatzResearch.WordTrace tailWord_2993222 prefixEnd_2993222 1536961591612193238859429 := by
  unfold tailWord_2993222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3411617973814855326995935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72781183441383580309246613 3411617973814855326995935)
  ·
    refine ⟨5117426960722282990493903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3411617973814855326995935 5117426960722282990493903)
    ·
      refine ⟨7676140441083424485740855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5117426960722282990493903 7676140441083424485740855)
      ·
        refine ⟨11514210661625136728611283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7676140441083424485740855 11514210661625136728611283)
        ·
          refine ⟨17271315992437705092916925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11514210661625136728611283 17271315992437705092916925)
          ·
            refine ⟨6476743497164139409843847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17271315992437705092916925 6476743497164139409843847)
            ·
              refine ⟨9715115245746209114765771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476743497164139409843847 9715115245746209114765771)
              ·
                refine ⟨14572672868619313672148657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9715115245746209114765771 14572672868619313672148657)
                ·
                  refine ⟨10929504651464485254111493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14572672868619313672148657 10929504651464485254111493)
                  ·
                    refine ⟨2049282122149590985145905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10929504651464485254111493 2049282122149590985145905)
                    ·
                      refine ⟨1536961591612193238859429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049282122149590985145905 1536961591612193238859429)
                      ·
                        rfl

theorem cell23_2993222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_2993222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993222 prefixEnd_2993222 := by exact prefixLift 2993222
  have htrace : WordTrace (prefixWord ++ tailWord_2993222) baseStart_2993222 baseEnd_2993222 := by
    simpa [prefixWord, tailWord_2993222, baseEnd_2993222] using wordTrace_append hprefix tailTrace_2993222
  have hstable : (prefixWord ++ tailWord_2993222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993222).length < 2 ^ (prefixWord ++ tailWord_2993222).sum := by decide
  have hdescent : baseEnd_2993222 < baseStart_2993222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993248 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 1, 5, 2]
def baseStart_2993248 : Nat := 118140960795 + 2993248 * 2 ^ 59
def prefixEnd_2993248 : Nat := 4983230072969 + 3 ^ 40 * 2993248 * 2
def baseEnd_2993248 : Nat := 1536974942109210137134309

theorem tailTrace_2993248 : CollatzResearch.WordTrace tailWord_2993248 prefixEnd_2993248 1536974942109210137134309 := by
  unfold tailWord_2993248
  simp only [CollatzResearch.WordTrace]
  refine ⟨54586361729990588452158199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72781815639987451269544265 54586361729990588452158199)
  ·
    refine ⟨81879542594985882678237299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54586361729990588452158199 81879542594985882678237299)
    ·
      refine ⟨122819313892478824017355949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81879542594985882678237299 122819313892478824017355949)
      ·
        refine ⟨46057242709679559006508481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122819313892478824017355949 46057242709679559006508481)
        ·
          refine ⟨34542932032259669254881361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46057242709679559006508481 34542932032259669254881361)
          ·
            refine ⟨25907199024194751941161021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34542932032259669254881361 25907199024194751941161021)
            ·
              refine ⟨9715199634073031977935383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25907199024194751941161021 9715199634073031977935383)
              ·
                refine ⟨14572799451109547966903075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9715199634073031977935383 14572799451109547966903075)
                ·
                  refine ⟨21859199176664321950354613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14572799451109547966903075 21859199176664321950354613)
                  ·
                    refine ⟨2049299922812280182845745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21859199176664321950354613 2049299922812280182845745)
                    ·
                      refine ⟨1536974942109210137134309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049299922812280182845745 1536974942109210137134309)
                      ·
                        rfl

theorem cell23_2993248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_2993248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993248 prefixEnd_2993248 := by exact prefixLift 2993248
  have htrace : WordTrace (prefixWord ++ tailWord_2993248) baseStart_2993248 baseEnd_2993248 := by
    simpa [prefixWord, tailWord_2993248, baseEnd_2993248] using wordTrace_append hprefix tailTrace_2993248
  have hstable : (prefixWord ++ tailWord_2993248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993248).length < 2 ^ (prefixWord ++ tailWord_2993248).sum := by decide
  have hdescent : baseEnd_2993248 < baseStart_2993248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993329 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 3, 2, 2]
def baseStart_2993329 : Nat := 118140960795 + 2993329 * 2 ^ 59
def prefixEnd_2993329 : Nat := 4983230072969 + 3 ^ 40 * 2993329 * 2
def baseEnd_2993329 : Nat := 1537016534042224320221437

theorem tailTrace_2993329 : CollatzResearch.WordTrace tailWord_2993329 prefixEnd_2993329 1537016534042224320221437 := by
  unfold tailWord_2993329
  simp only [CollatzResearch.WordTrace]
  refine ⟨109175677772687727738015041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72783785181791818492010027 109175677772687727738015041)
  ·
    refine ⟨81881758329515795803511281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109175677772687727738015041 81881758329515795803511281)
    ·
      refine ⟨61411318747136846852633461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81881758329515795803511281 61411318747136846852633461)
      ·
        refine ⟨5757311132544079392434387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61411318747136846852633461 5757311132544079392434387)
        ·
          refine ⟨8635966698816119088651581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757311132544079392434387 8635966698816119088651581)
          ·
            refine ⟨3238487512056044658244343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8635966698816119088651581 3238487512056044658244343)
            ·
              refine ⟨4857731268084066987366515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238487512056044658244343 4857731268084066987366515)
              ·
                refine ⟨7286596902126100481049773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857731268084066987366515 7286596902126100481049773)
                ·
                  refine ⟨2732473838297287680393665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7286596902126100481049773 2732473838297287680393665)
                  ·
                    refine ⟨2049355378722965760295249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2732473838297287680393665 2049355378722965760295249)
                    ·
                      refine ⟨1537016534042224320221437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049355378722965760295249 1537016534042224320221437)
                      ·
                        rfl

theorem cell23_2993329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_2993329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993329 prefixEnd_2993329 := by exact prefixLift 2993329
  have htrace : WordTrace (prefixWord ++ tailWord_2993329) baseStart_2993329 baseEnd_2993329 := by
    simpa [prefixWord, tailWord_2993329, baseEnd_2993329] using wordTrace_append hprefix tailTrace_2993329
  have hstable : (prefixWord ++ tailWord_2993329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993329).length < 2 ^ (prefixWord ++ tailWord_2993329).sum := by decide
  have hdescent : baseEnd_2993329 < baseStart_2993329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993338 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2]
def baseStart_2993338 : Nat := 118140960795 + 2993338 * 2 ^ 59
def prefixEnd_2993338 : Nat := 4983230072969 + 3 ^ 40 * 2993338 * 2
def baseEnd_2993338 : Nat := 1537021155368114785008895

theorem tailTrace_2993338 : CollatzResearch.WordTrace tailWord_2993338 prefixEnd_2993338 1537021155368114785008895 := by
  unfold tailWord_2993338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27294001507413780568773167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72784004019770081516728445 27294001507413780568773167)
  ·
    refine ⟨40941002261120670853159751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27294001507413780568773167 40941002261120670853159751)
    ·
      refine ⟨61411503391681006279739627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40941002261120670853159751 61411503391681006279739627)
      ·
        refine ⟨92117255087521509419609441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61411503391681006279739627 92117255087521509419609441)
        ·
          refine ⟨69087941315641132064707081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92117255087521509419609441 69087941315641132064707081)
          ·
            refine ⟨51815955986730849048530311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69087941315641132064707081 51815955986730849048530311)
            ·
              refine ⟨77723933980096273572795467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51815955986730849048530311 77723933980096273572795467)
              ·
                refine ⟨116585900970144410359193201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77723933980096273572795467 116585900970144410359193201)
                ·
                  refine ⟨87439425727608307769394901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116585900970144410359193201 87439425727608307769394901)
                  ·
                    refine ⟨2049361540490819713345193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 87439425727608307769394901 2049361540490819713345193)
                    ·
                      refine ⟨1537021155368114785008895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049361540490819713345193 1537021155368114785008895)
                      ·
                        rfl

theorem cell23_2993338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_2993338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993338 prefixEnd_2993338 := by exact prefixLift 2993338
  have htrace : WordTrace (prefixWord ++ tailWord_2993338) baseStart_2993338 baseEnd_2993338 := by
    simpa [prefixWord, tailWord_2993338, baseEnd_2993338] using wordTrace_append hprefix tailTrace_2993338
  have hstable : (prefixWord ++ tailWord_2993338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993338).length < 2 ^ (prefixWord ++ tailWord_2993338).sum := by decide
  have hdescent : baseEnd_2993338 < baseStart_2993338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993346 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2993346 : Nat := 118140960795 + 2993346 * 2 ^ 59
def prefixEnd_2993346 : Nat := 4983230072969 + 3 ^ 40 * 2993346 * 2
def baseEnd_2993346 : Nat := 1537025263213350753708859

theorem tailTrace_2993346 : CollatzResearch.WordTrace tailWord_2993346 prefixEnd_2993346 1537025263213350753708859 := by
  unfold tailWord_2993346
  simp only [CollatzResearch.WordTrace]
  refine ⟨27294074453406534910345973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72784198542417426427589261 27294074453406534910345973)
  ·
    refine ⟨2558819480006862647844935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27294074453406534910345973 2558819480006862647844935)
    ·
      refine ⟨3838229220010293971767403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558819480006862647844935 3838229220010293971767403)
      ·
        refine ⟨5757343830015440957651105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838229220010293971767403 5757343830015440957651105)
        ·
          refine ⟨4318007872511580718238329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757343830015440957651105 4318007872511580718238329)
          ·
            refine ⟨3238505904383685538678747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4318007872511580718238329 3238505904383685538678747)
            ·
              refine ⟨4857758856575528308018121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238505904383685538678747 4857758856575528308018121)
              ·
                refine ⟨3643319142431646231013591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4857758856575528308018121 3643319142431646231013591)
                ·
                  refine ⟨5464978713647469346520387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643319142431646231013591 5464978713647469346520387)
                  ·
                    refine ⟨8197468070471204019780581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464978713647469346520387 8197468070471204019780581)
                    ·
                      refine ⟨1537025263213350753708859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8197468070471204019780581 1537025263213350753708859)
                      ·
                        rfl

theorem cell23_2993346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2993346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993346 prefixEnd_2993346 := by exact prefixLift 2993346
  have htrace : WordTrace (prefixWord ++ tailWord_2993346) baseStart_2993346 baseEnd_2993346 := by
    simpa [prefixWord, tailWord_2993346, baseEnd_2993346] using wordTrace_append hprefix tailTrace_2993346
  have hstable : (prefixWord ++ tailWord_2993346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993346).length < 2 ^ (prefixWord ++ tailWord_2993346).sum := by decide
  have hdescent : baseEnd_2993346 < baseStart_2993346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993355 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 1, 3, 2]
def baseStart_2993355 : Nat := 118140960795 + 2993355 * 2 ^ 59
def prefixEnd_2993355 : Nat := 4983230072969 + 3 ^ 40 * 2993355 * 2
def baseEnd_2993355 : Nat := 1537029884539241218496317

theorem tailTrace_2993355 : CollatzResearch.WordTrace tailWord_2993355 prefixEnd_2993355 1537029884539241218496317 := by
  unfold tailWord_2993355
  simp only [CollatzResearch.WordTrace]
  refine ⟨109176626070593534178461519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72784417380395689452307679 109176626070593534178461519)
  ·
    refine ⟨163764939105890301267692279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109176626070593534178461519 163764939105890301267692279)
    ·
      refine ⟨245647408658835451901538419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163764939105890301267692279 245647408658835451901538419)
      ·
        refine ⟨368471112988253177852307629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245647408658835451901538419 368471112988253177852307629)
        ·
          refine ⟨138176667370594941694615361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368471112988253177852307629 138176667370594941694615361)
          ·
            refine ⟨103632500527946206270961521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138176667370594941694615361 103632500527946206270961521)
            ·
              refine ⟨77724375395959654703221141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103632500527946206270961521 77724375395959654703221141)
              ·
                refine ⟨3643330096685608814213491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77724375395959654703221141 3643330096685608814213491)
                ·
                  refine ⟨5464995145028413221320237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643330096685608814213491 5464995145028413221320237)
                  ·
                    refine ⟨2049373179385654957995089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5464995145028413221320237 2049373179385654957995089)
                    ·
                      refine ⟨1537029884539241218496317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049373179385654957995089 1537029884539241218496317)
                      ·
                        rfl

theorem cell23_2993355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 3, 2].length) (baseStart_2993355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993355 prefixEnd_2993355 := by exact prefixLift 2993355
  have htrace : WordTrace (prefixWord ++ tailWord_2993355) baseStart_2993355 baseEnd_2993355 := by
    simpa [prefixWord, tailWord_2993355, baseEnd_2993355] using wordTrace_append hprefix tailTrace_2993355
  have hstable : (prefixWord ++ tailWord_2993355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993355).length < 2 ^ (prefixWord ++ tailWord_2993355).sum := by decide
  have hdescent : baseEnd_2993355 < baseStart_2993355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993361 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 4, 6]
def baseStart_2993361 : Nat := 118140960795 + 2993361 * 2 ^ 59
def prefixEnd_2993361 : Nat := 4983230072969 + 3 ^ 40 * 2993361 * 2
def baseEnd_2993361 : Nat := 512344321807722731673763

theorem tailTrace_2993361 : CollatzResearch.WordTrace tailWord_2993361 prefixEnd_2993361 512344321807722731673763 := by
  unfold tailWord_2993361
  simp only [CollatzResearch.WordTrace]
  refine ⟨109176844908571797203179937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72784563272381198135453291 109176844908571797203179937)
  ·
    refine ⟨81882633681428847902384953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109176844908571797203179937 81882633681428847902384953)
    ·
      refine ⟨61411975261071635926788715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81882633681428847902384953 61411975261071635926788715)
      ·
        refine ⟨92117962891607453890183073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61411975261071635926788715 92117962891607453890183073)
        ·
          refine ⟨69088472168705590417637305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92117962891607453890183073 69088472168705590417637305)
          ·
            refine ⟨51816354126529192813227979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69088472168705590417637305 51816354126529192813227979)
            ·
              refine ⟨77724531189793789219841969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51816354126529192813227979 77724531189793789219841969)
              ·
                refine ⟨58293398392345341914881477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77724531189793789219841969 58293398392345341914881477)
                ·
                  refine ⟨10930012198564751609040277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58293398392345341914881477 10930012198564751609040277)
                  ·
                    refine ⟨512344321807722731673763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10930012198564751609040277 512344321807722731673763)
                    ·
                      rfl

theorem cell23_2993361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_2993361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993361 prefixEnd_2993361 := by exact prefixLift 2993361
  have htrace : WordTrace (prefixWord ++ tailWord_2993361) baseStart_2993361 baseEnd_2993361 := by
    simpa [prefixWord, tailWord_2993361, baseEnd_2993361] using wordTrace_append hprefix tailTrace_2993361
  have hstable : (prefixWord ++ tailWord_2993361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993361).length < 2 ^ (prefixWord ++ tailWord_2993361).sum := by decide
  have hdescent : baseEnd_2993361 < baseStart_2993361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993366 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2993366 : Nat := 118140960795 + 2993366 * 2 ^ 59
def prefixEnd_2993366 : Nat := 4983230072969 + 3 ^ 40 * 2993366 * 2
def baseEnd_2993366 : Nat := 1537035532826440675458767

theorem tailTrace_2993366 : CollatzResearch.WordTrace tailWord_2993366 prefixEnd_2993366 1537035532826440675458767 := by
  unfold tailWord_2993366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823564204597105191069497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72784684849035788704741301 6823564204597105191069497)
  ·
    refine ⟨5117673153447828893302123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6823564204597105191069497 5117673153447828893302123)
    ·
      refine ⟨7676509730171743339953185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5117673153447828893302123 7676509730171743339953185)
      ·
        refine ⟨5757382297628807504964889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7676509730171743339953185 5757382297628807504964889)
        ·
          refine ⟨4318036723221605628723667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757382297628807504964889 4318036723221605628723667)
          ·
            refine ⟨6477055084832408443085501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318036723221605628723667 6477055084832408443085501)
            ·
              refine ⟨2428895656812153166157063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6477055084832408443085501 2428895656812153166157063)
              ·
                refine ⟨3643343485218229749235595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2428895656812153166157063 3643343485218229749235595)
                ·
                  refine ⟨5465015227827344623853393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643343485218229749235595 5465015227827344623853393)
                  ·
                    refine ⟨4098761420870508467890045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5465015227827344623853393 4098761420870508467890045)
                    ·
                      refine ⟨1537035532826440675458767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098761420870508467890045 1537035532826440675458767)
                      ·
                        rfl

theorem cell23_2993366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2993366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993366 prefixEnd_2993366 := by exact prefixLift 2993366
  have htrace : WordTrace (prefixWord ++ tailWord_2993366) baseStart_2993366 baseEnd_2993366 := by
    simpa [prefixWord, tailWord_2993366, baseEnd_2993366] using wordTrace_append hprefix tailTrace_2993366
  have hstable : (prefixWord ++ tailWord_2993366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993366).length < 2 ^ (prefixWord ++ tailWord_2993366).sum := by decide
  have hdescent : baseEnd_2993366 < baseStart_2993366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993371 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 5]
def baseStart_2993371 : Nat := 118140960795 + 2993371 * 2 ^ 59
def prefixEnd_2993371 : Nat := 4983230072969 + 3 ^ 40 * 2993371 * 2
def baseEnd_2993371 : Nat := 1537038100229713155896243

theorem tailTrace_2993371 : CollatzResearch.WordTrace tailWord_2993371 prefixEnd_2993371 1537038100229713155896243 := by
  unfold tailWord_2993371
  simp only [CollatzResearch.WordTrace]
  refine ⟨109177209638535568911043967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72784806425690379274029311 109177209638535568911043967)
  ·
    refine ⟨163765814457803353366565951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109177209638535568911043967 163765814457803353366565951)
    ·
      refine ⟨245648721686705030049848927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163765814457803353366565951 245648721686705030049848927)
      ·
        refine ⟨368473082530057545074773391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245648721686705030049848927 368473082530057545074773391)
        ·
          refine ⟨552709623795086317612160087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368473082530057545074773391 552709623795086317612160087)
          ·
            refine ⟨829064435692629476418240131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552709623795086317612160087 829064435692629476418240131)
            ·
              refine ⟨1243596653538944214627360197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829064435692629476418240131 1243596653538944214627360197)
              ·
                refine ⟨233174372538552040242630037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1243596653538944214627360197 233174372538552040242630037)
                ·
                  refine ⟨10930048712744626886373283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 233174372538552040242630037 10930048712744626886373283)
                  ·
                    refine ⟨16395073069116940329559925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10930048712744626886373283 16395073069116940329559925)
                    ·
                      refine ⟨1537038100229713155896243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16395073069116940329559925 1537038100229713155896243)
                      ·
                        rfl

theorem cell23_2993371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_2993371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993371 prefixEnd_2993371 := by exact prefixLift 2993371
  have htrace : WordTrace (prefixWord ++ tailWord_2993371) baseStart_2993371 baseEnd_2993371 := by
    simpa [prefixWord, tailWord_2993371, baseEnd_2993371] using wordTrace_append hprefix tailTrace_2993371
  have hstable : (prefixWord ++ tailWord_2993371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993371).length < 2 ^ (prefixWord ++ tailWord_2993371).sum := by decide
  have hdescent : baseEnd_2993371 < baseStart_2993371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993388 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_2993388 : Nat := 118140960795 + 2993388 * 2 ^ 59
def prefixEnd_2993388 : Nat := 4983230072969 + 3 ^ 40 * 2993388 * 2
def baseEnd_2993388 : Nat := 1537046829400839589383665

theorem tailTrace_2993388 : CollatzResearch.WordTrace tailWord_2993388 prefixEnd_2993388 1537046829400839589383665 := by
  unfold tailWord_2993388
  simp only [CollatzResearch.WordTrace]
  refine ⟨54588914839736990407206409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72785219786315987209608545 54588914839736990407206409)
  ·
    refine ⟨40941686129802742805404807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54588914839736990407206409 40941686129802742805404807)
    ·
      refine ⟨61412529194704114208107211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40941686129802742805404807 61412529194704114208107211)
      ·
        refine ⟨92118793792056171312160817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61412529194704114208107211 92118793792056171312160817)
        ·
          refine ⟨69089095344042128484120613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92118793792056171312160817 69089095344042128484120613)
          ·
            refine ⟨12954205377007899090772615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69089095344042128484120613 12954205377007899090772615)
            ·
              refine ⟨19431308065511848636158923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12954205377007899090772615 19431308065511848636158923)
              ·
                refine ⟨29146962098267772954238385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19431308065511848636158923 29146962098267772954238385)
                ·
                  refine ⟨21860221573700829715678789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29146962098267772954238385 21860221573700829715678789)
                  ·
                    refine ⟨4098791545068905571689773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21860221573700829715678789 4098791545068905571689773)
                    ·
                      refine ⟨1537046829400839589383665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098791545068905571689773 1537046829400839589383665)
                      ·
                        rfl

theorem cell23_2993388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_2993388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993388 prefixEnd_2993388 := by exact prefixLift 2993388
  have htrace : WordTrace (prefixWord ++ tailWord_2993388) baseStart_2993388 baseEnd_2993388 := by
    simpa [prefixWord, tailWord_2993388, baseEnd_2993388] using wordTrace_append hprefix tailTrace_2993388
  have hstable : (prefixWord ++ tailWord_2993388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993388).length < 2 ^ (prefixWord ++ tailWord_2993388).sum := by decide
  have hdescent : baseEnd_2993388 < baseStart_2993388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993396 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2993396 : Nat := 118140960795 + 2993396 * 2 ^ 59
def prefixEnd_2993396 : Nat := 4983230072969 + 3 ^ 40 * 2993396 * 2
def baseEnd_2993396 : Nat := 1537050937246075558083629

theorem tailTrace_2993396 : CollatzResearch.WordTrace tailWord_2993396 prefixEnd_2993396 1537050937246075558083629 := by
  unfold tailWord_2993396
  simp only [CollatzResearch.WordTrace]
  refine ⟨54589060731722499090352021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72785414308963332120469361 54589060731722499090352021)
  ·
    refine ⟨2558862221799492144860251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54589060731722499090352021 2558862221799492144860251)
    ·
      refine ⟨3838293332699238217290377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558862221799492144860251 3838293332699238217290377)
      ·
        refine ⟨2878719999524428662967783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3838293332699238217290377 2878719999524428662967783)
        ·
          refine ⟨4318079999286642994451675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878719999524428662967783 4318079999286642994451675)
          ·
            refine ⟨6477119998929964491677513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318079999286642994451675 6477119998929964491677513)
            ·
              refine ⟨4857839999197473368758135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6477119998929964491677513 4857839999197473368758135)
              ·
                refine ⟨7286759998796210053137203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857839999197473368758135 7286759998796210053137203)
                ·
                  refine ⟨10930139998194315079705805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7286759998796210053137203 10930139998194315079705805)
                  ·
                    refine ⟨4098802499322868154889677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10930139998194315079705805 4098802499322868154889677)
                    ·
                      refine ⟨1537050937246075558083629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098802499322868154889677 1537050937246075558083629)
                      ·
                        rfl

theorem cell23_2993396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2993396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993396 prefixEnd_2993396 := by exact prefixLift 2993396
  have htrace : WordTrace (prefixWord ++ tailWord_2993396) baseStart_2993396 baseEnd_2993396 := by
    simpa [prefixWord, tailWord_2993396, baseEnd_2993396] using wordTrace_append hprefix tailTrace_2993396
  have hstable : (prefixWord ++ tailWord_2993396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993396).length < 2 ^ (prefixWord ++ tailWord_2993396).sum := by decide
  have hdescent : baseEnd_2993396 < baseStart_2993396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993402 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2]
def baseStart_2993402 : Nat := 118140960795 + 2993402 * 2 ^ 59
def prefixEnd_2993402 : Nat := 4983230072969 + 3 ^ 40 * 2993402 * 2
def baseEnd_2993402 : Nat := 1537054018130002534608601

theorem tailTrace_2993402 : CollatzResearch.WordTrace tailWord_2993402 prefixEnd_2993402 1537054018130002534608601 := by
  unfold tailWord_2993402
  simp only [CollatzResearch.WordTrace]
  refine ⟨27294585075355815301355615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72785560200948840803614973 27294585075355815301355615)
  ·
    refine ⟨40941877613033722952033423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27294585075355815301355615 40941877613033722952033423)
    ·
      refine ⟨61412816419550584428050135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40941877613033722952033423 61412816419550584428050135)
      ·
        refine ⟨92119224629325876642075203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61412816419550584428050135 92119224629325876642075203)
        ·
          refine ⟨138178836943988814963112805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92119224629325876642075203 138178836943988814963112805)
          ·
            refine ⟨25908531926997902805583651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138178836943988814963112805 25908531926997902805583651)
            ·
              refine ⟨38862797890496854208375477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25908531926997902805583651 38862797890496854208375477)
              ·
                refine ⟨3643387302234080082035201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38862797890496854208375477 3643387302234080082035201)
                ·
                  refine ⟨2732540476675560061526401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3643387302234080082035201 2732540476675560061526401)
                  ·
                    refine ⟨2049405357506670046144801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2732540476675560061526401 2049405357506670046144801)
                    ·
                      refine ⟨1537054018130002534608601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049405357506670046144801 1537054018130002534608601)
                      ·
                        rfl

theorem cell23_2993402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_2993402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993402 prefixEnd_2993402 := by exact prefixLift 2993402
  have htrace : WordTrace (prefixWord ++ tailWord_2993402) baseStart_2993402 baseEnd_2993402 := by
    simpa [prefixWord, tailWord_2993402, baseEnd_2993402] using wordTrace_append hprefix tailTrace_2993402
  have hstable : (prefixWord ++ tailWord_2993402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993402).length < 2 ^ (prefixWord ++ tailWord_2993402).sum := by decide
  have hdescent : baseEnd_2993402 < baseStart_2993402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993418 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2993418 : Nat := 118140960795 + 2993418 * 2 ^ 59
def prefixEnd_2993418 : Nat := 4983230072969 + 3 ^ 40 * 2993418 * 2
def baseEnd_2993418 : Nat := 1537062233820474472008527

theorem tailTrace_2993418 : CollatzResearch.WordTrace tailWord_2993418 prefixEnd_2993418 1537062233820474472008527 := by
  unfold tailWord_2993418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27294730967341323984501227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72785949246243530625336605 27294730967341323984501227)
  ·
    refine ⟨40942096451011985976751841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27294730967341323984501227 40942096451011985976751841)
    ·
      refine ⟨30706572338258989482563881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40942096451011985976751841 30706572338258989482563881)
      ·
        refine ⟨23029929253694242111922911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30706572338258989482563881 23029929253694242111922911)
        ·
          refine ⟨34544893880541363167884367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23029929253694242111922911 34544893880541363167884367)
          ·
            refine ⟨51817340820812044751826551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34544893880541363167884367 51817340820812044751826551)
            ·
              refine ⟨77726011231218067127739827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51817340820812044751826551 77726011231218067127739827)
              ·
                refine ⟨116589016846827100691609741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77726011231218067127739827 116589016846827100691609741)
                ·
                  refine ⟨43720881317560162759353653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116589016846827100691609741 43720881317560162759353653)
                  ·
                    refine ⟨4098832623521265258689405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43720881317560162759353653 4098832623521265258689405)
                    ·
                      refine ⟨1537062233820474472008527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098832623521265258689405 1537062233820474472008527)
                      ·
                        rfl

theorem cell23_2993418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2993418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993418 prefixEnd_2993418 := by exact prefixLift 2993418
  have htrace : WordTrace (prefixWord ++ tailWord_2993418) baseStart_2993418 baseEnd_2993418 := by
    simpa [prefixWord, tailWord_2993418, baseEnd_2993418] using wordTrace_append hprefix tailTrace_2993418
  have hstable : (prefixWord ++ tailWord_2993418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993418).length < 2 ^ (prefixWord ++ tailWord_2993418).sum := by decide
  have hdescent : baseEnd_2993418 < baseStart_2993418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993425 : List Nat := [1, 2, 2, 1, 1, 4, 4, 3, 5]
def baseStart_2993425 : Nat := 118140960795 + 2993425 * 2 ^ 59
def prefixEnd_2993425 : Nat := 4983230072969 + 3 ^ 40 * 2993425 * 2
def baseEnd_2993425 : Nat := 170785092020561771624555

theorem tailTrace_2993425 : CollatzResearch.WordTrace tailWord_2993425 prefixEnd_2993425 170785092020561771624555 := by
  unfold tailWord_2993425
  simp only [CollatzResearch.WordTrace]
  refine ⟨109179179180339936133509729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72786119453559957422339819 109179179180339936133509729)
  ·
    refine ⟨81884384385254952100132297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109179179180339936133509729 81884384385254952100132297)
    ·
      refine ⟨61413288288941214075099223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81884384385254952100132297 61413288288941214075099223)
      ·
        refine ⟨92119932433411821112648835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61413288288941214075099223 92119932433411821112648835)
        ·
          refine ⟨138179898650117731668973253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92119932433411821112648835 138179898650117731668973253)
          ·
            refine ⟨25908730996897074687932485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138179898650117731668973253 25908730996897074687932485)
            ·
              refine ⟨4857887061918201503987341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25908730996897074687932485 4857887061918201503987341)
              ·
                refine ⟨1821707648219325563995253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4857887061918201503987341 1821707648219325563995253)
                ·
                  refine ⟨170785092020561771624555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1821707648219325563995253 170785092020561771624555)
                  ·
                    rfl

theorem cell23_2993425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 5].length) (baseStart_2993425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993425 prefixEnd_2993425 := by exact prefixLift 2993425
  have htrace : WordTrace (prefixWord ++ tailWord_2993425) baseStart_2993425 baseEnd_2993425 := by
    simpa [prefixWord, tailWord_2993425, baseEnd_2993425] using wordTrace_append hprefix tailTrace_2993425
  have hstable : (prefixWord ++ tailWord_2993425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993425).length < 2 ^ (prefixWord ++ tailWord_2993425).sum := by decide
  have hdescent : baseEnd_2993425 < baseStart_2993425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993453 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2993453 : Nat := 118140960795 + 2993453 * 2 ^ 59
def prefixEnd_2993453 : Nat := 4983230072969 + 3 ^ 40 * 2993453 * 2
def baseEnd_2993453 : Nat := 1537080205643381835070867

theorem tailTrace_2993453 : CollatzResearch.WordTrace tailWord_2993453 prefixEnd_2993453 1537080205643381835070867 := by
  unfold tailWord_2993453
  simp only [CollatzResearch.WordTrace]
  refine ⟨109180200424238496915529013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72786800282825664610352675 109180200424238496915529013)
  ·
    refine ⟨10235643789772359085830845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109180200424238496915529013 10235643789772359085830845)
    ·
      refine ⟨3838366421164634657186567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10235643789772359085830845 3838366421164634657186567)
      ·
        refine ⟨5757549631746951985779851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838366421164634657186567 5757549631746951985779851)
        ·
          refine ⟨8636324447620427978669777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757549631746951985779851 8636324447620427978669777)
          ·
            refine ⟨6477243335715320984002333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8636324447620427978669777 6477243335715320984002333)
            ·
              refine ⟨2428966250893245369000875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6477243335715320984002333 2428966250893245369000875)
              ·
                refine ⟨3643449376339868053501313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2428966250893245369000875 3643449376339868053501313)
                ·
                  refine ⟨2732587032254901040125985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3643449376339868053501313 2732587032254901040125985)
                  ·
                    refine ⟨2049440274191175780094489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2732587032254901040125985 2049440274191175780094489)
                    ·
                      refine ⟨1537080205643381835070867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2049440274191175780094489 1537080205643381835070867)
                      ·
                        rfl

theorem cell23_2993453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2993453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993453 prefixEnd_2993453 := by exact prefixLift 2993453
  have htrace : WordTrace (prefixWord ++ tailWord_2993453) baseStart_2993453 baseEnd_2993453 := by
    simpa [prefixWord, tailWord_2993453, baseEnd_2993453] using wordTrace_append hprefix tailTrace_2993453
  have hstable : (prefixWord ++ tailWord_2993453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993453).length < 2 ^ (prefixWord ++ tailWord_2993453).sum := by decide
  have hdescent : baseEnd_2993453 < baseStart_2993453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993495 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_2993495 : Nat := 118140960795 + 2993495 * 2 ^ 59
def prefixEnd_2993495 : Nat := 4983230072969 + 3 ^ 40 * 2993495 * 2
def baseEnd_2993495 : Nat := 1537101771830870670745673

theorem tailTrace_2993495 : CollatzResearch.WordTrace tailWord_2993495 prefixEnd_2993495 1537101771830870670745673 := by
  unfold tailWord_2993495
  simp only [CollatzResearch.WordTrace]
  refine ⟨109181732290086338088557939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72787821526724225392371959 109181732290086338088557939)
  ·
    refine ⟨163772598435129507132836909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109181732290086338088557939 163772598435129507132836909)
    ·
      refine ⟨61414724413173565174813841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163772598435129507132836909 61414724413173565174813841)
      ·
        refine ⟨46061043309880173881110381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61414724413173565174813841 46061043309880173881110381)
        ·
          refine ⟨17272891241205065205416393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46061043309880173881110381 17272891241205065205416393)
          ·
            refine ⟨12954668430903798904062295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17272891241205065205416393 12954668430903798904062295)
            ·
              refine ⟨19432002646355698356093443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12954668430903798904062295 19432002646355698356093443)
              ·
                refine ⟨29148003969533547534140165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19432002646355698356093443 29148003969533547534140165)
                ·
                  refine ⟨5465250744287540162651281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29148003969533547534140165 5465250744287540162651281)
                  ·
                    refine ⟨4098938058215655121988461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5465250744287540162651281 4098938058215655121988461)
                    ·
                      refine ⟨1537101771830870670745673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4098938058215655121988461 1537101771830870670745673)
                      ·
                        rfl

theorem cell23_2993495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_2993495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993495 prefixEnd_2993495 := by exact prefixLift 2993495
  have htrace : WordTrace (prefixWord ++ tailWord_2993495) baseStart_2993495 baseEnd_2993495 := by
    simpa [prefixWord, tailWord_2993495, baseEnd_2993495] using wordTrace_append hprefix tailTrace_2993495
  have hstable : (prefixWord ++ tailWord_2993495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993495).length < 2 ^ (prefixWord ++ tailWord_2993495).sum := by decide
  have hdescent : baseEnd_2993495 < baseStart_2993495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993498 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 8]
def baseStart_2993498 : Nat := 118140960795 + 2993498 * 2 ^ 59
def prefixEnd_2993498 : Nat := 4983230072969 + 3 ^ 40 * 2993498 * 2
def baseEnd_2993498 : Nat := 170789256919203795445351

theorem tailTrace_2993498 : CollatzResearch.WordTrace tailWord_2993498 prefixEnd_2993498 170789256919203795445351 := by
  unfold tailWord_2993498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27295460427268867400229287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72787894472716979733944765 27295460427268867400229287)
  ·
    refine ⟨40943190640903301100343931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27295460427268867400229287 40943190640903301100343931)
    ·
      refine ⟨61414785961354951650515897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40943190640903301100343931 61414785961354951650515897)
      ·
        refine ⟨46061089471016213737886923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61414785961354951650515897 46061089471016213737886923)
        ·
          refine ⟨69091634206524320606830385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46061089471016213737886923 69091634206524320606830385)
          ·
            refine ⟨51818725654893240455122789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69091634206524320606830385 51818725654893240455122789)
            ·
              refine ⟨9716011060292482585335523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51818725654893240455122789 9716011060292482585335523)
              ·
                refine ⟨14574016590438723878003285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9716011060292482585335523 14574016590438723878003285)
                ·
                  refine ⟨170789256919203795445351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14574016590438723878003285 170789256919203795445351)
                  ·
                    rfl

theorem cell23_2993498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_2993498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2993498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2993498 prefixEnd_2993498 := by exact prefixLift 2993498
  have htrace : WordTrace (prefixWord ++ tailWord_2993498) baseStart_2993498 baseEnd_2993498 := by
    simpa [prefixWord, tailWord_2993498, baseEnd_2993498] using wordTrace_append hprefix tailTrace_2993498
  have hstable : (prefixWord ++ tailWord_2993498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993498).length < 2 ^ (prefixWord ++ tailWord_2993498).sum := by decide
  have hdescent : baseEnd_2993498 < baseStart_2993498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
