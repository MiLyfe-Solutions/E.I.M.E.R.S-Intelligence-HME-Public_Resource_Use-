import V185TrunkScan23Chunk1299

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7698695 : List Nat := [1, 1, 4, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7698695 : Nat := 118140960795 + 7698695 * 2 ^ 59
def prefixEnd_7698695 : Nat := 4983230072969 + 3 ^ 40 * 7698695 * 2
def baseEnd_7698695 : Nat := 3953130947365861554106853

theorem tailTrace_7698695 : CollatzResearch.WordTrace tailWord_7698695 prefixEnd_7698695 3953130947365861554106853 := by
  unfold tailWord_7698695
  simp only [CollatzResearch.WordTrace]
  refine ⟨280794474843950322271953539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187196316562633548181302359 280794474843950322271953539)
  ·
    refine ⟨421191712265925483407930309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280794474843950322271953539 421191712265925483407930309)
    ·
      refine ⟨78973446049861028138986933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421191712265925483407930309 78973446049861028138986933)
      ·
        refine ⟨7403760567174471388030025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78973446049861028138986933 7403760567174471388030025)
        ·
          refine ⟨5552820425380853541022519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7403760567174471388030025 5552820425380853541022519)
          ·
            refine ⟨8329230638071280311533779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552820425380853541022519 8329230638071280311533779)
            ·
              refine ⟨12493845957106920467300669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8329230638071280311533779 12493845957106920467300669)
              ·
                refine ⟨4685192233915095175237751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12493845957106920467300669 4685192233915095175237751)
                ·
                  refine ⟨7027788350872642762856627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685192233915095175237751 7027788350872642762856627)
                  ·
                    refine ⟨10541682526308964144284941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7027788350872642762856627 10541682526308964144284941)
                    ·
                      refine ⟨3953130947365861554106853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10541682526308964144284941 3953130947365861554106853)
                      ·
                        rfl

theorem cell23_7698695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7698695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698695 prefixEnd_7698695 := by exact prefixLift 7698695
  have htrace : WordTrace (prefixWord ++ tailWord_7698695) baseStart_7698695 baseEnd_7698695 := by
    simpa [prefixWord, tailWord_7698695, baseEnd_7698695] using wordTrace_append hprefix tailTrace_7698695
  have hstable : (prefixWord ++ tailWord_7698695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698695).length < 2 ^ (prefixWord ++ tailWord_7698695).sum := by decide
  have hdescent : baseEnd_7698695 < baseStart_7698695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698700 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_7698700 : Nat := 118140960795 + 7698700 * 2 ^ 59
def prefixEnd_7698700 : Nat := 4983230072969 + 3 ^ 40 * 7698700 * 2
def baseEnd_7698700 : Nat := 3953133514769134034544329

theorem tailTrace_7698700 : CollatzResearch.WordTrace tailWord_7698700 prefixEnd_7698700 3953133514769134034544329 := by
  unfold tailWord_7698700
  simp only [CollatzResearch.WordTrace]
  refine ⟨140397328604466104062942777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187196438139288138750590369 140397328604466104062942777)
  ·
    refine ⟨105297996453349578047207083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140397328604466104062942777 105297996453349578047207083)
    ·
      refine ⟨157946994680024367070810625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105297996453349578047207083 157946994680024367070810625)
      ·
        refine ⟨118460246010018275303107969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157946994680024367070810625 118460246010018275303107969)
        ·
          refine ⟨88845184507513706477330977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118460246010018275303107969 88845184507513706477330977)
          ·
            refine ⟨66633888380635279857998233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88845184507513706477330977 66633888380635279857998233)
            ·
              refine ⟨49975416285476459893498675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66633888380635279857998233 49975416285476459893498675)
              ·
                refine ⟨74963124428214689840248013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49975416285476459893498675 74963124428214689840248013)
                ·
                  refine ⟨28111171660580508690093005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74963124428214689840248013 28111171660580508690093005)
                  ·
                    refine ⟨10541689372717690758784877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28111171660580508690093005 10541689372717690758784877)
                    ·
                      refine ⟨3953133514769134034544329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10541689372717690758784877 3953133514769134034544329)
                      ·
                        rfl

theorem cell23_7698700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_7698700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698700 prefixEnd_7698700 := by exact prefixLift 7698700
  have htrace : WordTrace (prefixWord ++ tailWord_7698700) baseStart_7698700 baseEnd_7698700 := by
    simpa [prefixWord, tailWord_7698700, baseEnd_7698700] using wordTrace_append hprefix tailTrace_7698700
  have hstable : (prefixWord ++ tailWord_7698700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698700).length < 2 ^ (prefixWord ++ tailWord_7698700).sum := by decide
  have hdescent : baseEnd_7698700 < baseStart_7698700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698718 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7698718 : Nat := 118140960795 + 7698718 * 2 ^ 59
def prefixEnd_7698718 : Nat := 4983230072969 + 3 ^ 40 * 7698718 * 2
def baseEnd_7698718 : Nat := 3953142757420914964119247

theorem tailTrace_7698718 : CollatzResearch.WordTrace tailWord_7698718 prefixEnd_7698718 3953142757420914964119247 := by
  unfold tailWord_7698718
  simp only [CollatzResearch.WordTrace]
  refine ⟨35099414215358374650005101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187196875815244664800027205 35099414215358374650005101)
  ·
    refine ⟨13162280330759390493751913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35099414215358374650005101 13162280330759390493751913)
    ·
      refine ⟨9871710248069542870313935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13162280330759390493751913 9871710248069542870313935)
      ·
        refine ⟨14807565372104314305470903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9871710248069542870313935 14807565372104314305470903)
        ·
          refine ⟨22211348058156471458206355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14807565372104314305470903 22211348058156471458206355)
          ·
            refine ⟨33317022087234707187309533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22211348058156471458206355 33317022087234707187309533)
            ·
              refine ⟨12493883282713015195241075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33317022087234707187309533 12493883282713015195241075)
              ·
                refine ⟨18740824924069522792861613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12493883282713015195241075 18740824924069522792861613)
                ·
                  refine ⟨7027809346526071047323105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18740824924069522792861613 7027809346526071047323105)
                  ·
                    refine ⟨5270857009894553285492329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7027809346526071047323105 5270857009894553285492329)
                    ·
                      refine ⟨3953142757420914964119247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270857009894553285492329 3953142757420914964119247)
                      ·
                        rfl

theorem cell23_7698718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7698718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698718 prefixEnd_7698718 := by exact prefixLift 7698718
  have htrace : WordTrace (prefixWord ++ tailWord_7698718) baseStart_7698718 baseEnd_7698718 := by
    simpa [prefixWord, tailWord_7698718, baseEnd_7698718] using wordTrace_append hprefix tailTrace_7698718
  have hstable : (prefixWord ++ tailWord_7698718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698718).length < 2 ^ (prefixWord ++ tailWord_7698718).sum := by decide
  have hdescent : baseEnd_7698718 < baseStart_7698718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698728 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7698728 : Nat := 118140960795 + 7698728 * 2 ^ 59
def prefixEnd_7698728 : Nat := 4983230072969 + 3 ^ 40 * 7698728 * 2
def baseEnd_7698728 : Nat := 1317715964075819974998067

theorem tailTrace_7698728 : CollatzResearch.WordTrace tailWord_7698728 prefixEnd_7698728 1317715964075819974998067 := by
  unfold tailWord_7698728
  simp only [CollatzResearch.WordTrace]
  refine ⟨140397839226415384453952419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187197118968553845938603225 140397839226415384453952419)
  ·
    refine ⟨210596758839623076680928629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140397839226415384453952419 210596758839623076680928629)
    ·
      refine ⟨19743446141214663438837059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210596758839623076680928629 19743446141214663438837059)
      ·
        refine ⟨29615169211821995158255589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19743446141214663438837059 29615169211821995158255589)
        ·
          refine ⟨5552844227216624092172923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29615169211821995158255589 5552844227216624092172923)
          ·
            refine ⟨8329266340824936138259385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552844227216624092172923 8329266340824936138259385)
            ·
              refine ⟨6246949755618702103694539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8329266340824936138259385 6246949755618702103694539)
              ·
                refine ⟨9370424633428053155541809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246949755618702103694539 9370424633428053155541809)
                ·
                  refine ⟨7027818475071039866656357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9370424633428053155541809 7027818475071039866656357)
                  ·
                    refine ⟨1317715964075819974998067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7027818475071039866656357 1317715964075819974998067)
                    ·
                      rfl

theorem cell23_7698728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7698728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698728 prefixEnd_7698728 := by exact prefixLift 7698728
  have htrace : WordTrace (prefixWord ++ tailWord_7698728) baseStart_7698728 baseEnd_7698728 := by
    simpa [prefixWord, tailWord_7698728, baseEnd_7698728] using wordTrace_append hprefix tailTrace_7698728
  have hstable : (prefixWord ++ tailWord_7698728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698728).length < 2 ^ (prefixWord ++ tailWord_7698728).sum := by decide
  have hdescent : baseEnd_7698728 < baseStart_7698728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698744 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 1, 3, 2]
def baseStart_7698744 : Nat := 118140960795 + 7698744 * 2 ^ 59
def prefixEnd_7698744 : Nat := 4983230072969 + 3 ^ 40 * 7698744 * 2
def baseEnd_7698744 : Nat := 3953156107917931862394127

theorem tailTrace_7698744 : CollatzResearch.WordTrace tailWord_7698744 prefixEnd_7698744 3953156107917931862394127 := by
  unfold tailWord_7698744
  simp only [CollatzResearch.WordTrace]
  refine ⟨140398131010386401820243643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187197508013848535760324857 140398131010386401820243643)
  ·
    refine ⟨210597196515579602730365465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140398131010386401820243643 210597196515579602730365465)
    ·
      refine ⟨157947897386684702047774099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210597196515579602730365465 157947897386684702047774099)
      ·
        refine ⟨236921846080027053071661149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157947897386684702047774099 236921846080027053071661149)
        ·
          refine ⟨88845692280010144901872931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236921846080027053071661149 88845692280010144901872931)
          ·
            refine ⟨133268538420015217352809397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88845692280010144901872931 133268538420015217352809397)
            ·
              refine ⟨12493925476876426626825881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133268538420015217352809397 12493925476876426626825881)
              ·
                refine ⟨9370444107657319970119411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12493925476876426626825881 9370444107657319970119411)
                ·
                  refine ⟨14055666161485979955179117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370444107657319970119411 14055666161485979955179117)
                  ·
                    refine ⟨5270874810557242483192169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14055666161485979955179117 5270874810557242483192169)
                    ·
                      refine ⟨3953156107917931862394127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270874810557242483192169 3953156107917931862394127)
                      ·
                        rfl

theorem cell23_7698744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_7698744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698744 prefixEnd_7698744 := by exact prefixLift 7698744
  have htrace : WordTrace (prefixWord ++ tailWord_7698744) baseStart_7698744 baseEnd_7698744 := by
    simpa [prefixWord, tailWord_7698744, baseEnd_7698744] using wordTrace_append hprefix tailTrace_7698744
  have hstable : (prefixWord ++ tailWord_7698744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698744).length < 2 ^ (prefixWord ++ tailWord_7698744).sum := by decide
  have hdescent : baseEnd_7698744 < baseStart_7698744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698760 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_7698760 : Nat := 118140960795 + 7698760 * 2 ^ 59
def prefixEnd_7698760 : Nat := 4983230072969 + 3 ^ 40 * 7698760 * 2
def baseEnd_7698760 : Nat := 3953164323608403799794053

theorem tailTrace_7698760 : CollatzResearch.WordTrace tailWord_7698760 prefixEnd_7698760 3953164323608403799794053 := by
  unfold tailWord_7698760
  simp only [CollatzResearch.WordTrace]
  refine ⟨140398422794357419186534867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187197897059143225582046489 140398422794357419186534867)
  ·
    refine ⟨210597634191536128779802301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140398422794357419186534867 210597634191536128779802301)
    ·
      refine ⟨78974112821826048292425863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210597634191536128779802301 78974112821826048292425863)
      ·
        refine ⟨118461169232739072438638795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78974112821826048292425863 118461169232739072438638795)
        ·
          refine ⟨177691753849108608657958193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118461169232739072438638795 177691753849108608657958193)
          ·
            refine ⟨133268815386831456493468645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177691753849108608657958193 133268815386831456493468645)
            ·
              refine ⟨24987902885030898092525371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133268815386831456493468645 24987902885030898092525371)
              ·
                refine ⟨37481854327546347138788057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24987902885030898092525371 37481854327546347138788057)
                ·
                  refine ⟨28111390745659760354091043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37481854327546347138788057 28111390745659760354091043)
                  ·
                    refine ⟨42167086118489640531136565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28111390745659760354091043 42167086118489640531136565)
                    ·
                      refine ⟨3953164323608403799794053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42167086118489640531136565 3953164323608403799794053)
                      ·
                        rfl

theorem cell23_7698760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_7698760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698760 prefixEnd_7698760 := by exact prefixLift 7698760
  have htrace : WordTrace (prefixWord ++ tailWord_7698760) baseStart_7698760 baseEnd_7698760 := by
    simpa [prefixWord, tailWord_7698760, baseEnd_7698760] using wordTrace_append hprefix tailTrace_7698760
  have hstable : (prefixWord ++ tailWord_7698760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698760).length < 2 ^ (prefixWord ++ tailWord_7698760).sum := by decide
  have hdescent : baseEnd_7698760 < baseStart_7698760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698763 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 11]
def baseStart_7698763 : Nat := 118140960795 + 7698763 * 2 ^ 59
def prefixEnd_7698763 : Nat := 4983230072969 + 3 ^ 40 * 7698763 * 2
def baseEnd_7698763 : Nat := 439240651561151920895171

theorem tailTrace_7698763 : CollatzResearch.WordTrace tailWord_7698763 prefixEnd_7698763 439240651561151920895171 := by
  unfold tailWord_7698763
  simp only [CollatzResearch.WordTrace]
  refine ⟨280796955007703969885428943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187197970005135979923619295 280796955007703969885428943)
  ·
    refine ⟨421195432511555954828143415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280796955007703969885428943 421195432511555954828143415)
    ·
      refine ⟨631793148767333932242215123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421195432511555954828143415 631793148767333932242215123)
      ·
        refine ⟨947689723151000898363322685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631793148767333932242215123 947689723151000898363322685)
        ·
          refine ⟨355383646181625336886246007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 947689723151000898363322685 355383646181625336886246007)
          ·
            refine ⟨533075469272438005329369011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355383646181625336886246007 533075469272438005329369011)
            ·
              refine ⟨799613203908657007994053517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533075469272438005329369011 799613203908657007994053517)
              ·
                refine ⟨299854951465746377997770069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799613203908657007994053517 299854951465746377997770069)
                ·
                  refine ⟨439240651561151920895171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 299854951465746377997770069 439240651561151920895171)
                  ·
                    rfl

theorem cell23_7698763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 11].length) (baseStart_7698763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698763 prefixEnd_7698763 := by exact prefixLift 7698763
  have htrace : WordTrace (prefixWord ++ tailWord_7698763) baseStart_7698763 baseEnd_7698763 := by
    simpa [prefixWord, tailWord_7698763, baseEnd_7698763] using wordTrace_append hprefix tailTrace_7698763
  have hstable : (prefixWord ++ tailWord_7698763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698763).length < 2 ^ (prefixWord ++ tailWord_7698763).sum := by decide
  have hdescent : baseEnd_7698763 < baseStart_7698763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698791 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_7698791 : Nat := 118140960795 + 7698791 * 2 ^ 59
def prefixEnd_7698791 : Nat := 4983230072969 + 3 ^ 40 * 7698791 * 2
def baseEnd_7698791 : Nat := 3953180241508693178506411

theorem tailTrace_7698791 : CollatzResearch.WordTrace tailWord_7698791 prefixEnd_7698791 3953180241508693178506411 := by
  unfold tailWord_7698791
  simp only [CollatzResearch.WordTrace]
  refine ⟨280797976251602530667448227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187198650834401687111632151 280797976251602530667448227)
  ·
    refine ⟨421196964377403796001172341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280797976251602530667448227 421196964377403796001172341)
    ·
      refine ⟨39487215410381605875109907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 421196964377403796001172341 39487215410381605875109907)
      ·
        refine ⟨59230823115572408812664861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39487215410381605875109907 59230823115572408812664861)
        ·
          refine ⟨22211558668339653304749323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59230823115572408812664861 22211558668339653304749323)
          ·
            refine ⟨33317338002509479957123985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22211558668339653304749323 33317338002509479957123985)
            ·
              refine ⟨24988003501882109967842989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33317338002509479957123985 24988003501882109967842989)
              ·
                refine ⟨9370501313205791237941121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24988003501882109967842989 9370501313205791237941121)
                ·
                  refine ⟨7027875984904343428455841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9370501313205791237941121 7027875984904343428455841)
                  ·
                    refine ⟨5270906988678257571341881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7027875984904343428455841 5270906988678257571341881)
                    ·
                      refine ⟨3953180241508693178506411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270906988678257571341881 3953180241508693178506411)
                      ·
                        rfl

theorem cell23_7698791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_7698791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698791 prefixEnd_7698791 := by exact prefixLift 7698791
  have htrace : WordTrace (prefixWord ++ tailWord_7698791) baseStart_7698791 baseEnd_7698791 := by
    simpa [prefixWord, tailWord_7698791, baseEnd_7698791] using wordTrace_append hprefix tailTrace_7698791
  have hstable : (prefixWord ++ tailWord_7698791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698791).length < 2 ^ (prefixWord ++ tailWord_7698791).sum := by decide
  have hdescent : baseEnd_7698791 < baseStart_7698791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698860 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_7698860 : Nat := 118140960795 + 7698860 * 2 ^ 59
def prefixEnd_7698860 : Nat := 4983230072969 + 3 ^ 40 * 7698860 * 2
def baseEnd_7698860 : Nat := 3953215671673853408543593

theorem tailTrace_7698860 : CollatzResearch.WordTrace tailWord_7698860 prefixEnd_7698860 3953215671673853408543593 := by
  unfold tailWord_7698860
  simp only [CollatzResearch.WordTrace]
  refine ⟨140400246444176277725855017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187200328592235036967806689 140400246444176277725855017)
  ·
    refine ⟨105300184833132208294391263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140400246444176277725855017 105300184833132208294391263)
    ·
      refine ⟨157950277249698312441586895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105300184833132208294391263 157950277249698312441586895)
      ·
        refine ⟨236925415874547468662380343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157950277249698312441586895 236925415874547468662380343)
        ·
          refine ⟨355388123811821202993570515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236925415874547468662380343 355388123811821202993570515)
          ·
            refine ⟨533082185717731804490355773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355388123811821202993570515 533082185717731804490355773)
            ·
              refine ⟨199905819644149426683883415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533082185717731804490355773 199905819644149426683883415)
              ·
                refine ⟨299858729466224140025825123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199905819644149426683883415 299858729466224140025825123)
                ·
                  refine ⟨449788094199336210038737685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299858729466224140025825123 449788094199336210038737685)
                  ·
                    refine ⟨21083816915593884845565829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 449788094199336210038737685 21083816915593884845565829)
                    ·
                      refine ⟨3953215671673853408543593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21083816915593884845565829 3953215671673853408543593)
                      ·
                        rfl

theorem cell23_7698860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_7698860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698860 prefixEnd_7698860 := by exact prefixLift 7698860
  have htrace : WordTrace (prefixWord ++ tailWord_7698860) baseStart_7698860 baseEnd_7698860 := by
    simpa [prefixWord, tailWord_7698860, baseEnd_7698860] using wordTrace_append hprefix tailTrace_7698860
  have hstable : (prefixWord ++ tailWord_7698860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698860).length < 2 ^ (prefixWord ++ tailWord_7698860).sum := by decide
  have hdescent : baseEnd_7698860 < baseStart_7698860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698931 : List Nat := [1, 1, 1, 2, 2, 2, 4, 5, 1, 1, 3]
def baseStart_7698931 : Nat := 118140960795 + 7698931 * 2 ^ 59
def prefixEnd_7698931 : Nat := 4983230072969 + 3 ^ 40 * 7698931 * 2
def baseEnd_7698931 : Nat := 3953252128800322630755767

theorem tailTrace_7698931 : CollatzResearch.WordTrace tailWord_7698931 prefixEnd_7698931 3953252128800322630755767 := by
  unfold tailWord_7698931
  simp only [CollatzResearch.WordTrace]
  refine ⟨280803082471095334577544647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187202054980730223051696431 280803082471095334577544647)
  ·
    refine ⟨421204623706643001866316971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280803082471095334577544647 421204623706643001866316971)
    ·
      refine ⟨631806935559964502799475457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421204623706643001866316971 631806935559964502799475457)
      ·
        refine ⟨473855201669973377099606593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631806935559964502799475457 473855201669973377099606593)
        ·
          refine ⟨355391401252480032824704945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473855201669973377099606593 355391401252480032824704945)
          ·
            refine ⟨266543550939360024618528709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355391401252480032824704945 266543550939360024618528709)
            ·
              refine ⟨49976915801130004615974133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266543550939360024618528709 49976915801130004615974133)
              ·
                refine ⟨4685335856355937932747575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49976915801130004615974133 4685335856355937932747575)
                ·
                  refine ⟨7028003784533906899121363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685335856355937932747575 7028003784533906899121363)
                  ·
                    refine ⟨10542005676800860348682045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7028003784533906899121363 10542005676800860348682045)
                    ·
                      refine ⟨3953252128800322630755767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10542005676800860348682045 3953252128800322630755767)
                      ·
                        rfl

theorem cell23_7698931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 1, 3].length) (baseStart_7698931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698931 prefixEnd_7698931 := by exact prefixLift 7698931
  have htrace : WordTrace (prefixWord ++ tailWord_7698931) baseStart_7698931 baseEnd_7698931 := by
    simpa [prefixWord, tailWord_7698931, baseEnd_7698931] using wordTrace_append hprefix tailTrace_7698931
  have hstable : (prefixWord ++ tailWord_7698931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698931).length < 2 ^ (prefixWord ++ tailWord_7698931).sum := by decide
  have hdescent : baseEnd_7698931 < baseStart_7698931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698998 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_7698998 : Nat := 118140960795 + 7698998 * 2 ^ 59
def prefixEnd_7698998 : Nat := 4983230072969 + 3 ^ 40 * 7698998 * 2
def baseEnd_7698998 : Nat := 1317762177334724622872653

theorem tailTrace_7698998 : CollatzResearch.WordTrace tailWord_7698998 prefixEnd_7698998 1317762177334724622872653 := by
  unfold tailWord_7698998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17550345385115787813764603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187203684107901736680155765 17550345385115787813764603)
  ·
    refine ⟨26325518077673681720646905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17550345385115787813764603 26325518077673681720646905)
    ·
      refine ⟨19744138558255261290485179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26325518077673681720646905 19744138558255261290485179)
      ·
        refine ⟨29616207837382891935727769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19744138558255261290485179 29616207837382891935727769)
        ·
          refine ⟨22212155878037168951795827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29616207837382891935727769 22212155878037168951795827)
          ·
            refine ⟨33318233817055753427693741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22212155878037168951795827 33318233817055753427693741)
            ·
              refine ⟨12494337681395907535385153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33318233817055753427693741 12494337681395907535385153)
              ·
                refine ⟨9370753261046930651538865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12494337681395907535385153 9370753261046930651538865)
                ·
                  refine ⟨7028064945785197988654149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9370753261046930651538865 7028064945785197988654149)
                  ·
                    refine ⟨1317762177334724622872653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7028064945785197988654149 1317762177334724622872653)
                    ·
                      rfl

theorem cell23_7698998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_7698998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698998 prefixEnd_7698998 := by exact prefixLift 7698998
  have htrace : WordTrace (prefixWord ++ tailWord_7698998) baseStart_7698998 baseEnd_7698998 := by
    simpa [prefixWord, tailWord_7698998, baseEnd_7698998] using wordTrace_append hprefix tailTrace_7698998
  have hstable : (prefixWord ++ tailWord_7698998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698998).length < 2 ^ (prefixWord ++ tailWord_7698998).sum := by decide
  have hdescent : baseEnd_7698998 < baseStart_7698998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699005 : List Nat := [1, 4, 1, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_7699005 : Nat := 118140960795 + 7699005 * 2 ^ 59
def prefixEnd_7699005 : Nat := 4983230072969 + 3 ^ 40 * 7699005 * 2
def baseEnd_7699005 : Nat := 3953290126368755341230427

theorem tailTrace_7699005 : CollatzResearch.WordTrace tailWord_7699005 prefixEnd_7699005 3953290126368755341230427 := by
  unfold tailWord_7699005
  simp only [CollatzResearch.WordTrace]
  refine ⟨280805781472827245215738469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187203854315218163477158979 280805781472827245215738469)
  ·
    refine ⟨52651084026155108477950963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280805781472827245215738469 52651084026155108477950963)
    ·
      refine ⟨78976626039232662716926445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52651084026155108477950963 78976626039232662716926445)
      ·
        refine ⟨29616234764712248518847417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78976626039232662716926445 29616234764712248518847417)
        ·
          refine ⟨22212176073534186389135563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29616234764712248518847417 22212176073534186389135563)
          ·
            refine ⟨33318264110301279583703345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22212176073534186389135563 33318264110301279583703345)
            ·
              refine ⟨24988698082725959687777509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33318264110301279583703345 24988698082725959687777509)
              ·
                refine ⟨4685380890511117441458283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24988698082725959687777509 4685380890511117441458283)
                ·
                  refine ⟨7028071335766676162187425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685380890511117441458283 7028071335766676162187425)
                  ·
                    refine ⟨5271053501825007121640569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7028071335766676162187425 5271053501825007121640569)
                    ·
                      refine ⟨3953290126368755341230427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271053501825007121640569 3953290126368755341230427)
                      ·
                        rfl

theorem cell23_7699005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_7699005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699005 prefixEnd_7699005 := by exact prefixLift 7699005
  have htrace : WordTrace (prefixWord ++ tailWord_7699005) baseStart_7699005 baseEnd_7699005 := by
    simpa [prefixWord, tailWord_7699005, baseEnd_7699005] using wordTrace_append hprefix tailTrace_7699005
  have hstable : (prefixWord ++ tailWord_7699005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699005).length < 2 ^ (prefixWord ++ tailWord_7699005).sum := by decide
  have hdescent : baseEnd_7699005 < baseStart_7699005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699067 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 7]
def baseStart_7699067 : Nat := 118140960795 + 7699067 * 2 ^ 59
def prefixEnd_7699067 : Nat := 4983230072969 + 3 ^ 40 * 7699067 * 2
def baseEnd_7699067 : Nat := 439257995796592677628349

theorem tailTrace_7699067 : CollatzResearch.WordTrace tailWord_7699067 prefixEnd_7699067 439257995796592677628349 := by
  unfold tailWord_7699067
  simp only [CollatzResearch.WordTrace]
  refine ⟨280808042798602629804495455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187205361865735086536330303 280808042798602629804495455)
  ·
    refine ⟨421212064197903944706743183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280808042798602629804495455 421212064197903944706743183)
    ·
      refine ⟨631818096296855917060114775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421212064197903944706743183 631818096296855917060114775)
      ·
        refine ⟨947727144445283875590172163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631818096296855917060114775 947727144445283875590172163)
        ·
          refine ⟨1421590716667925813385258245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947727144445283875590172163 1421590716667925813385258245)
          ·
            refine ⟨266548259375236090009735921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1421590716667925813385258245 266548259375236090009735921)
            ·
              refine ⟨199911194531427067507301941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266548259375236090009735921 199911194531427067507301941)
              ·
                refine ⟨18741674487321287578809557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199911194531427067507301941 18741674487321287578809557)
                ·
                  refine ⟨439257995796592677628349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18741674487321287578809557 439257995796592677628349)
                  ·
                    rfl

theorem cell23_7699067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 7].length) (baseStart_7699067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699067 prefixEnd_7699067 := by exact prefixLift 7699067
  have htrace : WordTrace (prefixWord ++ tailWord_7699067) baseStart_7699067 baseEnd_7699067 := by
    simpa [prefixWord, tailWord_7699067, baseEnd_7699067] using wordTrace_append hprefix tailTrace_7699067
  have hstable : (prefixWord ++ tailWord_7699067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699067).length < 2 ^ (prefixWord ++ tailWord_7699067).sum := by decide
  have hdescent : baseEnd_7699067 < baseStart_7699067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699082 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_7699082 : Nat := 118140960795 + 7699082 * 2 ^ 59
def prefixEnd_7699082 : Nat := 4983230072969 + 3 ^ 40 * 7699082 * 2
def baseEnd_7699082 : Nat := 3953329664379151539967573

theorem tailTrace_7699082 : CollatzResearch.WordTrace tailWord_7699082 prefixEnd_7699082 3953329664379151539967573 := by
  unfold tailWord_7699082
  simp only [CollatzResearch.WordTrace]
  refine ⟨70202147473387071841572875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187205726595698858244194333 70202147473387071841572875)
  ·
    refine ⟨105303221210080607762359313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70202147473387071841572875 105303221210080607762359313)
    ·
      refine ⟨78977415907560455821769485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105303221210080607762359313 78977415907560455821769485)
      ·
        refine ⟨29616530965335170933163557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78977415907560455821769485 29616530965335170933163557)
        ·
          refine ⟨5553099556000344549968167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29616530965335170933163557 5553099556000344549968167)
          ·
            refine ⟨8329649334000516824952251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553099556000344549968167 8329649334000516824952251)
            ·
              refine ⟨12494474001000775237428377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8329649334000516824952251 12494474001000775237428377)
              ·
                refine ⟨9370855500750581428071283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12494474001000775237428377 9370855500750581428071283)
                ·
                  refine ⟨14056283251125872142106925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370855500750581428071283 14056283251125872142106925)
                  ·
                    refine ⟨5271106219172202053290097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14056283251125872142106925 5271106219172202053290097)
                    ·
                      refine ⟨3953329664379151539967573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271106219172202053290097 3953329664379151539967573)
                      ·
                        rfl

theorem cell23_7699082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_7699082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699082 prefixEnd_7699082 := by exact prefixLift 7699082
  have htrace : WordTrace (prefixWord ++ tailWord_7699082) baseStart_7699082 baseEnd_7699082 := by
    simpa [prefixWord, tailWord_7699082, baseEnd_7699082] using wordTrace_append hprefix tailTrace_7699082
  have hstable : (prefixWord ++ tailWord_7699082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699082).length < 2 ^ (prefixWord ++ tailWord_7699082).sum := by decide
  have hdescent : baseEnd_7699082 < baseStart_7699082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699148 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_7699148 : Nat := 118140960795 + 7699148 * 2 ^ 59
def prefixEnd_7699148 : Nat := 4983230072969 + 3 ^ 40 * 7699148 * 2
def baseEnd_7699148 : Nat := 1317787851367449427247423

theorem tailTrace_7699148 : CollatzResearch.WordTrace tailWord_7699148 prefixEnd_7699148 1317787851367449427247423 := by
  unfold tailWord_7699148
  simp only [CollatzResearch.WordTrace]
  refine ⟨140405498555654590319097049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187207331407539453758796065 140405498555654590319097049)
  ·
    refine ⟨105304123916740942739322787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140405498555654590319097049 105304123916740942739322787)
    ·
      refine ⟨157956185875111414108984181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105304123916740942739322787 157956185875111414108984181)
      ·
        refine ⟨14808392425791695072717267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157956185875111414108984181 14808392425791695072717267)
        ·
          refine ⟨22212588638687542609075901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14808392425791695072717267 22212588638687542609075901)
          ·
            refine ⟨8329720739507828478403463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22212588638687542609075901 8329720739507828478403463)
            ·
              refine ⟨12494581109261742717605195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8329720739507828478403463 12494581109261742717605195)
              ·
                refine ⟨18741871663892614076407793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12494581109261742717605195 18741871663892614076407793)
                ·
                  refine ⟨14056403747919460557305845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18741871663892614076407793 14056403747919460557305845)
                  ·
                    refine ⟨1317787851367449427247423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14056403747919460557305845 1317787851367449427247423)
                    ·
                      rfl

theorem cell23_7699148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_7699148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699148 prefixEnd_7699148 := by exact prefixLift 7699148
  have htrace : WordTrace (prefixWord ++ tailWord_7699148) baseStart_7699148 baseEnd_7699148 := by
    simpa [prefixWord, tailWord_7699148, baseEnd_7699148] using wordTrace_append hprefix tailTrace_7699148
  have hstable : (prefixWord ++ tailWord_7699148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699148).length < 2 ^ (prefixWord ++ tailWord_7699148).sum := by decide
  have hdescent : baseEnd_7699148 < baseStart_7699148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699221 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_7699221 : Nat := 118140960795 + 7699221 * 2 ^ 59
def prefixEnd_7699221 : Nat := 4983230072969 + 3 ^ 40 * 7699221 * 2
def baseEnd_7699221 : Nat := 1317800346063375498709811

theorem tailTrace_7699221 : CollatzResearch.WordTrace tailWord_7699221 prefixEnd_7699221 1317800346063375498709811 := by
  unfold tailWord_7699221
  simp only [CollatzResearch.WordTrace]
  refine ⟨280813659640044714105601517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187209106426696476070401011 280813659640044714105601517)
  ·
    refine ⟨105305122365016767789600569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280813659640044714105601517 105305122365016767789600569)
    ·
      refine ⟨78978841773762575842200427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105305122365016767789600569 78978841773762575842200427)
      ·
        refine ⟨118468262660643863763300641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78978841773762575842200427 118468262660643863763300641)
        ·
          refine ⟨88851196995482897822475481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118468262660643863763300641 88851196995482897822475481)
          ·
            refine ⟨66638397746612173366856611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88851196995482897822475481 66638397746612173366856611)
            ·
              refine ⟨99957596619918260050284917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66638397746612173366856611 99957596619918260050284917)
              ·
                refine ⟨9371024683117336879714211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99957596619918260050284917 9371024683117336879714211)
                ·
                  refine ⟨14056537024676005319571317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9371024683117336879714211 14056537024676005319571317)
                  ·
                    refine ⟨1317800346063375498709811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14056537024676005319571317 1317800346063375498709811)
                    ·
                      rfl

theorem cell23_7699221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_7699221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699221 prefixEnd_7699221 := by exact prefixLift 7699221
  have htrace : WordTrace (prefixWord ++ tailWord_7699221) baseStart_7699221 baseEnd_7699221 := by
    simpa [prefixWord, tailWord_7699221, baseEnd_7699221] using wordTrace_append hprefix tailTrace_7699221
  have hstable : (prefixWord ++ tailWord_7699221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699221).length < 2 ^ (prefixWord ++ tailWord_7699221).sum := by decide
  have hdescent : baseEnd_7699221 < baseStart_7699221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699228 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_7699228 : Nat := 118140960795 + 7699228 * 2 ^ 59
def prefixEnd_7699228 : Nat := 4983230072969 + 3 ^ 40 * 7699228 * 2
def baseEnd_7699228 : Nat := 3953404632554707968741901

theorem tailTrace_7699228 : CollatzResearch.WordTrace tailWord_7699228 prefixEnd_7699228 3953404632554707968741901 := by
  unfold tailWord_7699228
  simp only [CollatzResearch.WordTrace]
  refine ⟨140406957475509677150553169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187209276634012902867404225 140406957475509677150553169)
  ·
    refine ⟨105305218106632257862914877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140406957475509677150553169 105305218106632257862914877)
    ·
      refine ⟨39489456789987096698593079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105305218106632257862914877 39489456789987096698593079)
      ·
        refine ⟨59234185184980645047889619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39489456789987096698593079 59234185184980645047889619)
        ·
          refine ⟨88851277777470967571834429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59234185184980645047889619 88851277777470967571834429)
          ·
            refine ⟨33319229166551612839437911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88851277777470967571834429 33319229166551612839437911)
            ·
              refine ⟨49978843749827419259156867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33319229166551612839437911 49978843749827419259156867)
              ·
                refine ⟨74968265624741128888735301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49978843749827419259156867 74968265624741128888735301)
                ·
                  refine ⟨14056549804638961666637869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74968265624741128888735301 14056549804638961666637869)
                  ·
                    refine ⟨5271206176739610624989201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14056549804638961666637869 5271206176739610624989201)
                    ·
                      refine ⟨3953404632554707968741901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271206176739610624989201 3953404632554707968741901)
                      ·
                        rfl

theorem cell23_7699228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_7699228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699228 prefixEnd_7699228 := by exact prefixLift 7699228
  have htrace : WordTrace (prefixWord ++ tailWord_7699228) baseStart_7699228 baseEnd_7699228 := by
    simpa [prefixWord, tailWord_7699228, baseEnd_7699228] using wordTrace_append hprefix tailTrace_7699228
  have hstable : (prefixWord ++ tailWord_7699228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699228).length < 2 ^ (prefixWord ++ tailWord_7699228).sum := by decide
  have hdescent : baseEnd_7699228 < baseStart_7699228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699229 : List Nat := [1, 4, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_7699229 : Nat := 118140960795 + 7699229 * 2 ^ 59
def prefixEnd_7699229 : Nat := 4983230072969 + 3 ^ 40 * 7699229 * 2
def baseEnd_7699229 : Nat := 1317801715345120821609799

theorem tailTrace_7699229 : CollatzResearch.WordTrace tailWord_7699229 prefixEnd_7699229 1317801715345120821609799 := by
  unfold tailWord_7699229
  simp only [CollatzResearch.WordTrace]
  refine ⟨280813951424015731471892741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187209300949343820981261827 280813951424015731471892741)
  ·
    refine ⟨52652615892002949650979889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280813951424015731471892741 52652615892002949650979889)
    ·
      refine ⟨39489461919002212238234917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52652615892002949650979889 39489461919002212238234917)
      ·
        refine ⟨7404274109812914794669047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39489461919002212238234917 7404274109812914794669047)
        ·
          refine ⟨11106411164719372192003571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7404274109812914794669047 11106411164719372192003571)
          ·
            refine ⟨16659616747079058288005357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11106411164719372192003571 16659616747079058288005357)
            ·
              refine ⟨6247356280154646858002009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16659616747079058288005357 6247356280154646858002009)
              ·
                refine ⟨4685517210115985143501507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6247356280154646858002009 4685517210115985143501507)
                ·
                  refine ⟨7028275815173977715252261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685517210115985143501507 7028275815173977715252261)
                  ·
                    refine ⟨1317801715345120821609799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7028275815173977715252261 1317801715345120821609799)
                    ·
                      rfl

theorem cell23_7699229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_7699229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699229 prefixEnd_7699229 := by exact prefixLift 7699229
  have htrace : WordTrace (prefixWord ++ tailWord_7699229) baseStart_7699229 baseEnd_7699229 := by
    simpa [prefixWord, tailWord_7699229, baseEnd_7699229] using wordTrace_append hprefix tailTrace_7699229
  have hstable : (prefixWord ++ tailWord_7699229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699229).length < 2 ^ (prefixWord ++ tailWord_7699229).sum := by decide
  have hdescent : baseEnd_7699229 < baseStart_7699229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699242 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 6]
def baseStart_7699242 : Nat := 118140960795 + 7699242 * 2 ^ 59
def prefixEnd_7699242 : Nat := 4983230072969 + 3 ^ 40 * 7699242 * 2
def baseEnd_7699242 : Nat := 439267980142652323774093

theorem tailTrace_7699242 : CollatzResearch.WordTrace tailWord_7699242 prefixEnd_7699242 439267980142652323774093 := by
  unfold tailWord_7699242
  simp only [CollatzResearch.WordTrace]
  refine ⟨70203606393242158673028995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187209617048645756461410653 70203606393242158673028995)
  ·
    refine ⟨105305409589863238009543493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70203606393242158673028995 105305409589863238009543493)
    ·
      refine ⟨19744764298099357126789405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105305409589863238009543493 19744764298099357126789405)
      ·
        refine ⟨7404286611787258922546027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19744764298099357126789405 7404286611787258922546027)
        ·
          refine ⟨11106429917680888383819041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7404286611787258922546027 11106429917680888383819041)
          ·
            refine ⟨8329822438260666287864281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11106429917680888383819041 8329822438260666287864281)
            ·
              refine ⟨6247366828695499715898211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8329822438260666287864281 6247366828695499715898211)
              ·
                refine ⟨9371050243043249573847317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6247366828695499715898211 9371050243043249573847317)
                ·
                  refine ⟨439267980142652323774093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9371050243043249573847317 439267980142652323774093)
                  ·
                    rfl

theorem cell23_7699242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_7699242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699242 prefixEnd_7699242 := by exact prefixLift 7699242
  have htrace : WordTrace (prefixWord ++ tailWord_7699242) baseStart_7699242 baseEnd_7699242 := by
    simpa [prefixWord, tailWord_7699242, baseEnd_7699242] using wordTrace_append hprefix tailTrace_7699242
  have hstable : (prefixWord ++ tailWord_7699242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699242).length < 2 ^ (prefixWord ++ tailWord_7699242).sum := by decide
  have hdescent : baseEnd_7699242 < baseStart_7699242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699258 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_7699258 : Nat := 118140960795 + 7699258 * 2 ^ 59
def prefixEnd_7699258 : Nat := 4983230072969 + 3 ^ 40 * 7699258 * 2
def baseEnd_7699258 : Nat := 3953420036974342851366763

theorem tailTrace_7699258 : CollatzResearch.WordTrace tailWord_7699258 prefixEnd_7699258 3953420036974342851366763 := by
  unfold tailWord_7699258
  simp only [CollatzResearch.WordTrace]
  refine ⟨70203752285227667356174607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187210006093940446283132285 70203752285227667356174607)
  ·
    refine ⟨105305628427841501034261911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70203752285227667356174607 105305628427841501034261911)
    ·
      refine ⟨157958442641762251551392867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105305628427841501034261911 157958442641762251551392867)
      ·
        refine ⟨236937663962643377327089301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157958442641762251551392867 236937663962643377327089301)
        ·
          refine ⟨11106452998248908312207311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236937663962643377327089301 11106452998248908312207311)
          ·
            refine ⟨16659679497373362468310967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11106452998248908312207311 16659679497373362468310967)
            ·
              refine ⟨24989519246060043702466451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16659679497373362468310967 24989519246060043702466451)
              ·
                refine ⟨37484278869090065553699677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24989519246060043702466451 37484278869090065553699677)
                ·
                  refine ⟨14056604575908774582637379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37484278869090065553699677 14056604575908774582637379)
                  ·
                    refine ⟨21084906863863161873956069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14056604575908774582637379 21084906863863161873956069)
                    ·
                      refine ⟨3953420036974342851366763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21084906863863161873956069 3953420036974342851366763)
                      ·
                        rfl

theorem cell23_7699258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_7699258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699258 prefixEnd_7699258 := by exact prefixLift 7699258
  have htrace : WordTrace (prefixWord ++ tailWord_7699258) baseStart_7699258 baseEnd_7699258 := by
    simpa [prefixWord, tailWord_7699258, baseEnd_7699258] using wordTrace_append hprefix tailTrace_7699258
  have hstable : (prefixWord ++ tailWord_7699258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699258).length < 2 ^ (prefixWord ++ tailWord_7699258).sum := by decide
  have hdescent : baseEnd_7699258 < baseStart_7699258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699262 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_7699262 : Nat := 118140960795 + 7699262 * 2 ^ 59
def prefixEnd_7699262 : Nat := 4983230072969 + 3 ^ 40 * 7699262 * 2
def baseEnd_7699262 : Nat := 3953422090896960835716745

theorem tailTrace_7699262 : CollatzResearch.WordTrace tailWord_7699262 prefixEnd_7699262 3953422090896960835716745 := by
  unfold tailWord_7699262
  simp only [CollatzResearch.WordTrace]
  refine ⟨35101894379112022263480505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187210103355264118738562693 35101894379112022263480505)
  ·
    refine ⟨26326420784334016697610379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35101894379112022263480505 26326420784334016697610379)
    ·
      refine ⟨39489631176501025046415569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26326420784334016697610379 39489631176501025046415569)
      ·
        refine ⟨29617223382375768784811677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39489631176501025046415569 29617223382375768784811677)
        ·
          refine ⟨11106458768390913294304379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29617223382375768784811677 11106458768390913294304379)
          ·
            refine ⟨16659688152586369941456569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11106458768390913294304379 16659688152586369941456569)
            ·
              refine ⟨12494766114439777456092427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16659688152586369941456569 12494766114439777456092427)
              ·
                refine ⟨18742149171659666184138641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12494766114439777456092427 18742149171659666184138641)
                ·
                  refine ⟨14056611878744749638103981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18742149171659666184138641 14056611878744749638103981)
                  ·
                    refine ⟨5271229454529281114288993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14056611878744749638103981 5271229454529281114288993)
                    ·
                      refine ⟨3953422090896960835716745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271229454529281114288993 3953422090896960835716745)
                      ·
                        rfl

theorem cell23_7699262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_7699262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699262 prefixEnd_7699262 := by exact prefixLift 7699262
  have htrace : WordTrace (prefixWord ++ tailWord_7699262) baseStart_7699262 baseEnd_7699262 := by
    simpa [prefixWord, tailWord_7699262, baseEnd_7699262] using wordTrace_append hprefix tailTrace_7699262
  have hstable : (prefixWord ++ tailWord_7699262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699262).length < 2 ^ (prefixWord ++ tailWord_7699262).sum := by decide
  have hdescent : baseEnd_7699262 < baseStart_7699262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699278 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_7699278 : Nat := 118140960795 + 7699278 * 2 ^ 59
def prefixEnd_7699278 : Nat := 4983230072969 + 3 ^ 40 * 7699278 * 2
def baseEnd_7699278 : Nat := 3953430306587432773116671

theorem tailTrace_7699278 : CollatzResearch.WordTrace tailWord_7699278 prefixEnd_7699278 3953430306587432773116671 := by
  unfold tailWord_7699278
  simp only [CollatzResearch.WordTrace]
  refine ⟨35101967325104776605053311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187210492400558808560284325 35101967325104776605053311)
  ·
    refine ⟨52652950987657164907579967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35101967325104776605053311 52652950987657164907579967)
    ·
      refine ⟨78979426481485747361369951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52652950987657164907579967 78979426481485747361369951)
      ·
        refine ⟨118469139722228621042054927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78979426481485747361369951 118469139722228621042054927)
        ·
          refine ⟨177703709583342931563082391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118469139722228621042054927 177703709583342931563082391)
          ·
            refine ⟨266555564375014397344623587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177703709583342931563082391 266555564375014397344623587)
            ·
              refine ⟨399833346562521596016935381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266555564375014397344623587 399833346562521596016935381)
              ·
                refine ⟨9371094060059099906646923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 399833346562521596016935381 9371094060059099906646923)
                ·
                  refine ⟨14056641090088649859970385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9371094060059099906646923 14056641090088649859970385)
                  ·
                    refine ⟨10542480817566487394977789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14056641090088649859970385 10542480817566487394977789)
                    ·
                      refine ⟨3953430306587432773116671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10542480817566487394977789 3953430306587432773116671)
                      ·
                        rfl

theorem cell23_7699278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_7699278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699278 prefixEnd_7699278 := by exact prefixLift 7699278
  have htrace : WordTrace (prefixWord ++ tailWord_7699278) baseStart_7699278 baseEnd_7699278 := by
    simpa [prefixWord, tailWord_7699278, baseEnd_7699278] using wordTrace_append hprefix tailTrace_7699278
  have hstable : (prefixWord ++ tailWord_7699278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699278).length < 2 ^ (prefixWord ++ tailWord_7699278).sum := by decide
  have hdescent : baseEnd_7699278 < baseStart_7699278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699281 : List Nat := [1, 2, 2, 1, 7, 10]
def baseStart_7699281 : Nat := 118140960795 + 7699281 * 2 ^ 59
def prefixEnd_7699281 : Nat := 4983230072969 + 3 ^ 40 * 7699281 * 2
def baseEnd_7699281 : Nat := 16269266860203276795799

theorem tailTrace_7699281 : CollatzResearch.WordTrace tailWord_7699281 prefixEnd_7699281 16269266860203276795799 := by
  unfold tailWord_7699281
  simp only [CollatzResearch.WordTrace]
  refine ⟨280815848019827344352785697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187210565346551562901857131 280815848019827344352785697)
  ·
    refine ⟨210611886014870508264589273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280815848019827344352785697 210611886014870508264589273)
    ·
      refine ⟨157958914511152881198441955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210611886014870508264589273 157958914511152881198441955)
      ·
        refine ⟨236938371766729321797662933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157958914511152881198441955 236938371766729321797662933)
        ·
          refine ⟨5553243088282718479632725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 236938371766729321797662933 5553243088282718479632725)
          ·
            refine ⟨16269266860203276795799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5553243088282718479632725 16269266860203276795799)
            ·
              rfl

theorem cell23_7699281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 10].length) (baseStart_7699281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699281 prefixEnd_7699281 := by exact prefixLift 7699281
  have htrace : WordTrace (prefixWord ++ tailWord_7699281) baseStart_7699281 baseEnd_7699281 := by
    simpa [prefixWord, tailWord_7699281, baseEnd_7699281] using wordTrace_append hprefix tailTrace_7699281
  have hstable : (prefixWord ++ tailWord_7699281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699281).length < 2 ^ (prefixWord ++ tailWord_7699281).sum := by decide
  have hdescent : baseEnd_7699281 < baseStart_7699281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699308 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_7699308 : Nat := 118140960795 + 7699308 * 2 ^ 59
def prefixEnd_7699308 : Nat := 4983230072969 + 3 ^ 40 * 7699308 * 2
def baseEnd_7699308 : Nat := 3953445711007067655741533

theorem tailTrace_7699308 : CollatzResearch.WordTrace tailWord_7699308 prefixEnd_7699308 3953445711007067655741533 := by
  unfold tailWord_7699308
  simp only [CollatzResearch.WordTrace]
  refine ⟨140408416395364763982009289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187211221860486351976012385 140408416395364763982009289)
  ·
    refine ⟨105306312296523572986506967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140408416395364763982009289 105306312296523572986506967)
    ·
      refine ⟨157959468444785359479760451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105306312296523572986506967 157959468444785359479760451)
      ·
        refine ⟨236939202667178039219640677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157959468444785359479760451 236939202667178039219640677)
        ·
          refine ⟨44426100500095882353682627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236939202667178039219640677 44426100500095882353682627)
          ·
            refine ⟨66639150750143823530523941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44426100500095882353682627 66639150750143823530523941)
            ·
              refine ⟨12494840765651966911973239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66639150750143823530523941 12494840765651966911973239)
              ·
                refine ⟨18742261148477950367959859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12494840765651966911973239 18742261148477950367959859)
                ·
                  refine ⟨28113391722716925551939789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18742261148477950367959859 28113391722716925551939789)
                  ·
                    refine ⟨10542521896018847081977421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28113391722716925551939789 10542521896018847081977421)
                    ·
                      refine ⟨3953445711007067655741533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10542521896018847081977421 3953445711007067655741533)
                      ·
                        rfl

theorem cell23_7699308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_7699308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699308 prefixEnd_7699308 := by exact prefixLift 7699308
  have htrace : WordTrace (prefixWord ++ tailWord_7699308) baseStart_7699308 baseEnd_7699308 := by
    simpa [prefixWord, tailWord_7699308, baseEnd_7699308] using wordTrace_append hprefix tailTrace_7699308
  have hstable : (prefixWord ++ tailWord_7699308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699308).length < 2 ^ (prefixWord ++ tailWord_7699308).sum := by decide
  have hdescent : baseEnd_7699308 < baseStart_7699308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699326 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7699326 : Nat := 118140960795 + 7699326 * 2 ^ 59
def prefixEnd_7699326 : Nat := 4983230072969 + 3 ^ 40 * 7699326 * 2
def baseEnd_7699326 : Nat := 3953454953658848585316451

theorem tailTrace_7699326 : CollatzResearch.WordTrace tailWord_7699326 prefixEnd_7699326 3953454953658848585316451 := by
  unfold tailWord_7699326
  simp only [CollatzResearch.WordTrace]
  refine ⟨35102186163083039629771729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187211659536442878025449221 35102186163083039629771729)
  ·
    refine ⟨26326639622312279722328797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35102186163083039629771729 26326639622312279722328797)
    ·
      refine ⟨9872489858367104895873299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26326639622312279722328797 9872489858367104895873299)
      ·
        refine ⟨14808734787550657343809949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9872489858367104895873299 14808734787550657343809949)
        ·
          refine ⟨5553275545331496503928731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14808734787550657343809949 5553275545331496503928731)
          ·
            refine ⟨8329913317997244755893097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553275545331496503928731 8329913317997244755893097)
            ·
              refine ⟨6247434988497933566919823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8329913317997244755893097 6247434988497933566919823)
              ·
                refine ⟨9371152482746900350379735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6247434988497933566919823 9371152482746900350379735)
                ·
                  refine ⟨14056728724120350525569603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9371152482746900350379735 14056728724120350525569603)
                  ·
                    refine ⟨21085093086180525788354405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14056728724120350525569603 21085093086180525788354405)
                    ·
                      refine ⟨3953454953658848585316451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21085093086180525788354405 3953454953658848585316451)
                      ·
                        rfl

theorem cell23_7699326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7699326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699326 prefixEnd_7699326 := by exact prefixLift 7699326
  have htrace : WordTrace (prefixWord ++ tailWord_7699326) baseStart_7699326 baseEnd_7699326 := by
    simpa [prefixWord, tailWord_7699326, baseEnd_7699326] using wordTrace_append hprefix tailTrace_7699326
  have hstable : (prefixWord ++ tailWord_7699326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699326).length < 2 ^ (prefixWord ++ tailWord_7699326).sum := by decide
  have hdescent : baseEnd_7699326 < baseStart_7699326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699408 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 2, 5, 2]
def baseStart_7699408 : Nat := 118140960795 + 7699408 * 2 ^ 59
def prefixEnd_7699408 : Nat := 4983230072969 + 3 ^ 40 * 7699408 * 2
def baseEnd_7699408 : Nat := 3953497059072517264491073

theorem tailTrace_7699408 : CollatzResearch.WordTrace tailWord_7699408 prefixEnd_7699408 3953497059072517264491073 := by
  unfold tailWord_7699408
  simp only [CollatzResearch.WordTrace]
  refine ⟨140410240045183622521329439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187213653393578163361772585 140410240045183622521329439)
  ·
    refine ⟨210615360067775433781994159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140410240045183622521329439 210615360067775433781994159)
    ·
      refine ⟨315923040101663150672991239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210615360067775433781994159 315923040101663150672991239)
      ·
        refine ⟨473884560152494726009486859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315923040101663150672991239 473884560152494726009486859)
        ·
          refine ⟨710826840228742089014230289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473884560152494726009486859 710826840228742089014230289)
          ·
            refine ⟨533120130171556566760672717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710826840228742089014230289 533120130171556566760672717)
            ·
              refine ⟨199920048814333712535252269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533120130171556566760672717 199920048814333712535252269)
              ·
                refine ⟨74970018305375142200719601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199920048814333712535252269 74970018305375142200719601)
                ·
                  refine ⟨56227513729031356650539701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74970018305375142200719601 56227513729031356650539701)
                  ·
                    refine ⟨5271329412096689685988097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56227513729031356650539701 5271329412096689685988097)
                    ·
                      refine ⟨3953497059072517264491073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271329412096689685988097 3953497059072517264491073)
                      ·
                        rfl

theorem cell23_7699408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 5, 2].length) (baseStart_7699408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699408 prefixEnd_7699408 := by exact prefixLift 7699408
  have htrace : WordTrace (prefixWord ++ tailWord_7699408) baseStart_7699408 baseEnd_7699408 := by
    simpa [prefixWord, tailWord_7699408, baseEnd_7699408] using wordTrace_append hprefix tailTrace_7699408
  have hstable : (prefixWord ++ tailWord_7699408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699408).length < 2 ^ (prefixWord ++ tailWord_7699408).sum := by decide
  have hdescent : baseEnd_7699408 < baseStart_7699408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699451 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 6]
def baseStart_7699451 : Nat := 118140960795 + 7699451 * 2 ^ 59
def prefixEnd_7699451 : Nat := 4983230072969 + 3 ^ 40 * 7699451 * 2
def baseEnd_7699451 : Nat := 3953519138740660596253375

theorem tailTrace_7699451 : CollatzResearch.WordTrace tailWord_7699451 prefixEnd_7699451 3953519138740660596253375 := by
  unfold tailWord_7699451
  simp only [CollatzResearch.WordTrace]
  refine ⟨280822048429211463386474207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187214698952807642257649471 280822048429211463386474207)
  ·
    refine ⟨421233072643817195079711311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280822048429211463386474207 421233072643817195079711311)
    ·
      refine ⟨631849608965725792619566967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421233072643817195079711311 631849608965725792619566967)
      ·
        refine ⟨947774413448588688929350451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631849608965725792619566967 947774413448588688929350451)
        ·
          refine ⟨1421661620172883033394025677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947774413448588688929350451 1421661620172883033394025677)
          ·
            refine ⟨533123107564831137522759629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1421661620172883033394025677 533123107564831137522759629)
            ·
              refine ⟨199921165336811676571034861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533123107564831137522759629 199921165336811676571034861)
              ·
                refine ⟨74970437001304378714138073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199921165336811676571034861 74970437001304378714138073)
                ·
                  refine ⟨56227827750978284035603555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74970437001304378714138073 56227827750978284035603555)
                  ·
                    refine ⟨84341741626467426053405333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56227827750978284035603555 84341741626467426053405333)
                    ·
                      refine ⟨3953519138740660596253375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84341741626467426053405333 3953519138740660596253375)
                      ·
                        rfl

theorem cell23_7699451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_7699451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699451 prefixEnd_7699451 := by exact prefixLift 7699451
  have htrace : WordTrace (prefixWord ++ tailWord_7699451) baseStart_7699451 baseEnd_7699451 := by
    simpa [prefixWord, tailWord_7699451, baseEnd_7699451] using wordTrace_append hprefix tailTrace_7699451
  have hstable : (prefixWord ++ tailWord_7699451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699451).length < 2 ^ (prefixWord ++ tailWord_7699451).sum := by decide
  have hdescent : baseEnd_7699451 < baseStart_7699451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699492 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7699492 : Nat := 118140960795 + 7699492 * 2 ^ 59
def prefixEnd_7699492 : Nat := 4983230072969 + 3 ^ 40 * 7699492 * 2
def baseEnd_7699492 : Nat := 3953540191447494935840687

theorem tailTrace_7699492 : CollatzResearch.WordTrace tailWord_7699492 prefixEnd_7699492 3953540191447494935840687 := by
  unfold tailWord_7699492
  simp only [CollatzResearch.WordTrace]
  refine ⟨140411771911031463694358365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187215695881375284925811153 140411771911031463694358365)
  ·
    refine ⟨52654414466636798885384387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140411771911031463694358365 52654414466636798885384387)
    ·
      refine ⟨78981621699955198328076581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52654414466636798885384387 78981621699955198328076581)
      ·
        refine ⟨14809054068741599686514359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78981621699955198328076581 14809054068741599686514359)
        ·
          refine ⟨22213581103112399529771539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14809054068741599686514359 22213581103112399529771539)
          ·
            refine ⟨33320371654668599294657309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22213581103112399529771539 33320371654668599294657309)
            ·
              refine ⟨12495139370500724735496491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33320371654668599294657309 12495139370500724735496491)
              ·
                refine ⟨18742709055751087103244737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12495139370500724735496491 18742709055751087103244737)
                ·
                  refine ⟨14057031791813315327433553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18742709055751087103244737 14057031791813315327433553)
                  ·
                    refine ⟨10542773843859986495575165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14057031791813315327433553 10542773843859986495575165)
                    ·
                      refine ⟨3953540191447494935840687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10542773843859986495575165 3953540191447494935840687)
                      ·
                        rfl

theorem cell23_7699492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7699492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699492 prefixEnd_7699492 := by exact prefixLift 7699492
  have htrace : WordTrace (prefixWord ++ tailWord_7699492) baseStart_7699492 baseEnd_7699492 := by
    simpa [prefixWord, tailWord_7699492, baseEnd_7699492] using wordTrace_append hprefix tailTrace_7699492
  have hstable : (prefixWord ++ tailWord_7699492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699492).length < 2 ^ (prefixWord ++ tailWord_7699492).sum := by decide
  have hdescent : baseEnd_7699492 < baseStart_7699492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699505 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_7699505 : Nat := 118140960795 + 7699505 * 2 ^ 59
def prefixEnd_7699505 : Nat := 4983230072969 + 3 ^ 40 * 7699505 * 2
def baseEnd_7699505 : Nat := 3953546866696003384978127

theorem tailTrace_7699505 : CollatzResearch.WordTrace tailWord_7699505 prefixEnd_7699505 3953546866696003384978127 := by
  unfold tailWord_7699505
  simp only [CollatzResearch.WordTrace]
  refine ⟨280824017971015830608939969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187216011980677220405959979 280824017971015830608939969)
  ·
    refine ⟨210618013478261872956704977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280824017971015830608939969 210618013478261872956704977)
    ·
      refine ⟨157963510108696404717528733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210618013478261872956704977 157963510108696404717528733)
      ·
        refine ⟨59236316290761151769073275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157963510108696404717528733 59236316290761151769073275)
        ·
          refine ⟨88854474436141727653609913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59236316290761151769073275 88854474436141727653609913)
          ·
            refine ⟨66640855827106295740207435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88854474436141727653609913 66640855827106295740207435)
            ·
              refine ⟨99961283740659443610311153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66640855827106295740207435 99961283740659443610311153)
              ·
                refine ⟨74970962805494582707733365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99961283740659443610311153 74970962805494582707733365)
                ·
                  refine ⟨7028527763015117128850003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74970962805494582707733365 7028527763015117128850003)
                  ·
                    refine ⟨10542791644522675693275005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7028527763015117128850003 10542791644522675693275005)
                    ·
                      refine ⟨3953546866696003384978127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10542791644522675693275005 3953546866696003384978127)
                      ·
                        rfl

theorem cell23_7699505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_7699505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699505 prefixEnd_7699505 := by exact prefixLift 7699505
  have htrace : WordTrace (prefixWord ++ tailWord_7699505) baseStart_7699505 baseEnd_7699505 := by
    simpa [prefixWord, tailWord_7699505, baseEnd_7699505] using wordTrace_append hprefix tailTrace_7699505
  have hstable : (prefixWord ++ tailWord_7699505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699505).length < 2 ^ (prefixWord ++ tailWord_7699505).sum := by decide
  have hdescent : baseEnd_7699505 < baseStart_7699505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699562 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_7699562 : Nat := 118140960795 + 7699562 * 2 ^ 59
def prefixEnd_7699562 : Nat := 4983230072969 + 3 ^ 40 * 7699562 * 2
def baseEnd_7699562 : Nat := 3953576135093309661965365

theorem tailTrace_7699562 : CollatzResearch.WordTrace tailWord_7699562 prefixEnd_7699562 3953576135093309661965365 := by
  unfold tailWord_7699562
  simp only [CollatzResearch.WordTrace]
  refine ⟨70206524232952332335941235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187217397954539552895843293 70206524232952332335941235)
  ·
    refine ⟨105309786349428498503911853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70206524232952332335941235 105309786349428498503911853)
    ·
      refine ⟨39491169881035686938966945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105309786349428498503911853 39491169881035686938966945)
      ·
        refine ⟨29618377410776765204225209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39491169881035686938966945 29618377410776765204225209)
        ·
          refine ⟨22213783058082573903168907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29618377410776765204225209 22213783058082573903168907)
          ·
            refine ⟨33320674587123860854753361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22213783058082573903168907 33320674587123860854753361)
            ·
              refine ⟨24990505940342895641065021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33320674587123860854753361 24990505940342895641065021)
              ·
                refine ⟨9371439727628585865399383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24990505940342895641065021 9371439727628585865399383)
                ·
                  refine ⟨14057159591442878798099075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9371439727628585865399383 14057159591442878798099075)
                  ·
                    refine ⟨21085739387164318197148613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14057159591442878798099075 21085739387164318197148613)
                    ·
                      refine ⟨3953576135093309661965365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21085739387164318197148613 3953576135093309661965365)
                      ·
                        rfl

theorem cell23_7699562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_7699562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699562 prefixEnd_7699562 := by exact prefixLift 7699562
  have htrace : WordTrace (prefixWord ++ tailWord_7699562) baseStart_7699562 baseEnd_7699562 := by
    simpa [prefixWord, tailWord_7699562, baseEnd_7699562] using wordTrace_append hprefix tailTrace_7699562
  have hstable : (prefixWord ++ tailWord_7699562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699562).length < 2 ^ (prefixWord ++ tailWord_7699562).sum := by decide
  have hdescent : baseEnd_7699562 < baseStart_7699562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699565 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_7699565 : Nat := 118140960795 + 7699565 * 2 ^ 59
def prefixEnd_7699565 : Nat := 4983230072969 + 3 ^ 40 * 7699565 * 2
def baseEnd_7699565 : Nat := 3953577675535273150227851

theorem tailTrace_7699565 : CollatzResearch.WordTrace tailWord_7699565 prefixEnd_7699565 3953577675535273150227851 := by
  unfold tailWord_7699565
  simp only [CollatzResearch.WordTrace]
  refine ⟨280826206350798460856124149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187217470900532307237416099 280826206350798460856124149)
  ·
    refine ⟨26327456845387355705261639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280826206350798460856124149 26327456845387355705261639)
    ·
      refine ⟨39491185268081033557892459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26327456845387355705261639 39491185268081033557892459)
      ·
        refine ⟨59236777902121550336838689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39491185268081033557892459 59236777902121550336838689)
        ·
          refine ⟨44427583426591162752629017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59236777902121550336838689 44427583426591162752629017)
          ·
            refine ⟨33320687569943372064471763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44427583426591162752629017 33320687569943372064471763)
            ·
              refine ⟨49981031354915058096707645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33320687569943372064471763 49981031354915058096707645)
              ·
                refine ⟨18742886758093146786265367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49981031354915058096707645 18742886758093146786265367)
                ·
                  refine ⟨28114330137139720179398051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18742886758093146786265367 28114330137139720179398051)
                  ·
                    refine ⟨42171495205709580269097077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28114330137139720179398051 42171495205709580269097077)
                    ·
                      refine ⟨3953577675535273150227851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42171495205709580269097077 3953577675535273150227851)
                      ·
                        rfl

theorem cell23_7699565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_7699565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699565 prefixEnd_7699565 := by exact prefixLift 7699565
  have htrace : WordTrace (prefixWord ++ tailWord_7699565) baseStart_7699565 baseEnd_7699565 := by
    simpa [prefixWord, tailWord_7699565, baseEnd_7699565] using wordTrace_append hprefix tailTrace_7699565
  have hstable : (prefixWord ++ tailWord_7699565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699565).length < 2 ^ (prefixWord ++ tailWord_7699565).sum := by decide
  have hdescent : baseEnd_7699565 < baseStart_7699565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699573 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7699573 : Nat := 118140960795 + 7699573 * 2 ^ 59
def prefixEnd_7699573 : Nat := 4983230072969 + 3 ^ 40 * 7699573 * 2
def baseEnd_7699573 : Nat := 3953581783380509118927815

theorem tailTrace_7699573 : CollatzResearch.WordTrace tailWord_7699573 prefixEnd_7699573 3953581783380509118927815 := by
  unfold tailWord_7699573
  simp only [CollatzResearch.WordTrace]
  refine ⟨280826498134769478222415373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187217665423179652148276915 280826498134769478222415373)
  ·
    refine ⟨105309936800538554333405765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280826498134769478222415373 105309936800538554333405765)
    ·
      refine ⟨19745613150100978937513581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105309936800538554333405765 19745613150100978937513581)
      ·
        refine ⟨7404604931287867101567593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19745613150100978937513581 7404604931287867101567593)
        ·
          refine ⟨5553453698465900326175695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7404604931287867101567593 5553453698465900326175695)
          ·
            refine ⟨8330180547698850489263543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553453698465900326175695 8330180547698850489263543)
            ·
              refine ⟨12495270821548275733895315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8330180547698850489263543 12495270821548275733895315)
              ·
                refine ⟨18742906232322413600842973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12495270821548275733895315 18742906232322413600842973)
                ·
                  refine ⟨7028589837120905100316115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18742906232322413600842973 7028589837120905100316115)
                  ·
                    refine ⟨10542884755681357650474173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7028589837120905100316115 10542884755681357650474173)
                    ·
                      refine ⟨3953581783380509118927815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10542884755681357650474173 3953581783380509118927815)
                      ·
                        rfl

theorem cell23_7699573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7699573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699573 prefixEnd_7699573 := by exact prefixLift 7699573
  have htrace : WordTrace (prefixWord ++ tailWord_7699573) baseStart_7699573 baseEnd_7699573 := by
    simpa [prefixWord, tailWord_7699573, baseEnd_7699573] using wordTrace_append hprefix tailTrace_7699573
  have hstable : (prefixWord ++ tailWord_7699573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699573).length < 2 ^ (prefixWord ++ tailWord_7699573).sum := by decide
  have hdescent : baseEnd_7699573 < baseStart_7699573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699579 : List Nat := [1, 1, 1, 1, 1, 4, 1, 8, 1, 2, 2]
def baseStart_7699579 : Nat := 118140960795 + 7699579 * 2 ^ 59
def prefixEnd_7699579 : Nat := 4983230072969 + 3 ^ 40 * 7699579 * 2
def baseEnd_7699579 : Nat := 3953584864264436095452787

theorem tailTrace_7699579 : CollatzResearch.WordTrace tailWord_7699579 prefixEnd_7699579 3953584864264436095452787 := by
  unfold tailWord_7699579
  simp only [CollatzResearch.WordTrace]
  refine ⟨280826716972747741247133791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187217811315165160831422527 280826716972747741247133791)
  ·
    refine ⟨421240075459121611870700687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280826716972747741247133791 421240075459121611870700687)
    ·
      refine ⟨631860113188682417806051031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421240075459121611870700687 631860113188682417806051031)
      ·
        refine ⟨947790169783023626709076547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631860113188682417806051031 947790169783023626709076547)
        ·
          refine ⟨1421685254674535440063614821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947790169783023626709076547 1421685254674535440063614821)
          ·
            refine ⟨266565985251475395011927779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1421685254674535440063614821 266565985251475395011927779)
            ·
              refine ⟨399848977877213092517891669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266565985251475395011927779 399848977877213092517891669)
              ·
                refine ⟨4685730209498590927944043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 399848977877213092517891669 4685730209498590927944043)
                ·
                  refine ⟨7028595314247886391916065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685730209498590927944043 7028595314247886391916065)
                  ·
                    refine ⟨5271446485685914793937049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7028595314247886391916065 5271446485685914793937049)
                    ·
                      refine ⟨3953584864264436095452787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271446485685914793937049 3953584864264436095452787)
                      ·
                        rfl

theorem cell23_7699579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 2, 2].length) (baseStart_7699579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699579 prefixEnd_7699579 := by exact prefixLift 7699579
  have htrace : WordTrace (prefixWord ++ tailWord_7699579) baseStart_7699579 baseEnd_7699579 := by
    simpa [prefixWord, tailWord_7699579, baseEnd_7699579] using wordTrace_append hprefix tailTrace_7699579
  have hstable : (prefixWord ++ tailWord_7699579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699579).length < 2 ^ (prefixWord ++ tailWord_7699579).sum := by decide
  have hdescent : baseEnd_7699579 < baseStart_7699579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699585 : List Nat := [1, 2, 4, 2, 2, 2, 2, 8]
def baseStart_7699585 : Nat := 118140960795 + 7699585 * 2 ^ 59
def prefixEnd_7699585 : Nat := 4983230072969 + 3 ^ 40 * 7699585 * 2
def baseEnd_7699585 : Nat := 146429183153643076739917

theorem tailTrace_7699585 : CollatzResearch.WordTrace tailWord_7699585 prefixEnd_7699585 146429183153643076739917 := by
  unfold tailWord_7699585
  simp only [CollatzResearch.WordTrace]
  refine ⟨280826935810726004271852209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187217957207150669514568139 280826935810726004271852209)
  ·
    refine ⟨210620201858044503203889157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280826935810726004271852209 210620201858044503203889157)
    ·
      refine ⟨39491287848383344350729217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210620201858044503203889157 39491287848383344350729217)
      ·
        refine ⟨29618465886287508263046913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39491287848383344350729217 29618465886287508263046913)
        ·
          refine ⟨22213849414715631197285185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29618465886287508263046913 22213849414715631197285185)
          ·
            refine ⟨16660387061036723397963889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22213849414715631197285185 16660387061036723397963889)
            ·
              refine ⟨12495290295777542548472917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16660387061036723397963889 12495290295777542548472917)
              ·
                refine ⟨146429183153643076739917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12495290295777542548472917 146429183153643076739917)
                ·
                  rfl

theorem cell23_7699585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 8].length) (baseStart_7699585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699585 prefixEnd_7699585 := by exact prefixLift 7699585
  have htrace : WordTrace (prefixWord ++ tailWord_7699585) baseStart_7699585 baseEnd_7699585 := by
    simpa [prefixWord, tailWord_7699585, baseEnd_7699585] using wordTrace_append hprefix tailTrace_7699585
  have hstable : (prefixWord ++ tailWord_7699585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699585).length < 2 ^ (prefixWord ++ tailWord_7699585).sum := by decide
  have hdescent : baseEnd_7699585 < baseStart_7699585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699612 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_7699612 : Nat := 118140960795 + 7699612 * 2 ^ 59
def prefixEnd_7699612 : Nat := 4983230072969 + 3 ^ 40 * 7699612 * 2
def baseEnd_7699612 : Nat := 3953601809126034466340135

theorem tailTrace_7699612 : CollatzResearch.WordTrace tailWord_7699612 prefixEnd_7699612 3953601809126034466340135 := by
  unfold tailWord_7699612
  simp only [CollatzResearch.WordTrace]
  refine ⟨140413960290814093941542545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187218613721085458588723393 140413960290814093941542545)
  ·
    refine ⟨105310470218110570456156909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140413960290814093941542545 105310470218110570456156909)
    ·
      refine ⟨39491426331791463921058841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105310470218110570456156909 39491426331791463921058841)
      ·
        refine ⟨29618569748843597940794131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39491426331791463921058841 29618569748843597940794131)
        ·
          refine ⟨44427854623265396911191197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29618569748843597940794131 44427854623265396911191197)
          ·
            refine ⟨16660445483724523841696699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44427854623265396911191197 16660445483724523841696699)
            ·
              refine ⟨24990668225586785762545049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16660445483724523841696699 24990668225586785762545049)
              ·
                refine ⟨18743001169190089321908787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24990668225586785762545049 18743001169190089321908787)
                ·
                  refine ⟨28114501753785133982863181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18743001169190089321908787 28114501753785133982863181)
                  ·
                    refine ⟨10542938157669425243573693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28114501753785133982863181 10542938157669425243573693)
                    ·
                      refine ⟨3953601809126034466340135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10542938157669425243573693 3953601809126034466340135)
                      ·
                        rfl

theorem cell23_7699612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_7699612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699612 prefixEnd_7699612 := by exact prefixLift 7699612
  have htrace : WordTrace (prefixWord ++ tailWord_7699612) baseStart_7699612 baseEnd_7699612 := by
    simpa [prefixWord, tailWord_7699612, baseEnd_7699612] using wordTrace_append hprefix tailTrace_7699612
  have hstable : (prefixWord ++ tailWord_7699612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699612).length < 2 ^ (prefixWord ++ tailWord_7699612).sum := by decide
  have hdescent : baseEnd_7699612 < baseStart_7699612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699669 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7699669 : Nat := 118140960795 + 7699669 * 2 ^ 59
def prefixEnd_7699669 : Nat := 4983230072969 + 3 ^ 40 * 7699669 * 2
def baseEnd_7699669 : Nat := 3953631077523340743327373

theorem tailTrace_7699669 : CollatzResearch.WordTrace tailWord_7699669 prefixEnd_7699669 3953631077523340743327373 := by
  unfold tailWord_7699669
  simp only [CollatzResearch.WordTrace]
  refine ⟨280829999542421686617910061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187219999694947791078606707 280829999542421686617910061)
  ·
    refine ⟨105311249828408132481716273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280829999542421686617910061 105311249828408132481716273)
    ·
      refine ⟨78983437371306099361287205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105311249828408132481716273 78983437371306099361287205)
      ·
        refine ⟨14809394507119893630241351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78983437371306099361287205 14809394507119893630241351)
        ·
          refine ⟨22214091760679840445362027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14809394507119893630241351 22214091760679840445362027)
          ·
            refine ⟨33321137641019760668043041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22214091760679840445362027 33321137641019760668043041)
            ·
              refine ⟨24990853230764820501032281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33321137641019760668043041 24990853230764820501032281)
              ·
                refine ⟨18743139923073615375774211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24990853230764820501032281 18743139923073615375774211)
                ·
                  refine ⟨28114709884610423063661317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18743139923073615375774211 28114709884610423063661317)
                  ·
                    refine ⟨5271508103364454324436497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28114709884610423063661317 5271508103364454324436497)
                    ·
                      refine ⟨3953631077523340743327373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271508103364454324436497 3953631077523340743327373)
                      ·
                        rfl

theorem cell23_7699669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7699669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699669 prefixEnd_7699669 := by exact prefixLift 7699669
  have htrace : WordTrace (prefixWord ++ tailWord_7699669) baseStart_7699669 baseEnd_7699669 := by
    simpa [prefixWord, tailWord_7699669, baseEnd_7699669] using wordTrace_append hprefix tailTrace_7699669
  have hstable : (prefixWord ++ tailWord_7699669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699669).length < 2 ^ (prefixWord ++ tailWord_7699669).sum := by decide
  have hdescent : baseEnd_7699669 < baseStart_7699669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699692 : List Nat := [2, 2, 1, 1, 2, 4, 2, 4, 5]
def baseStart_7699692 : Nat := 118140960795 + 7699692 * 2 ^ 59
def prefixEnd_7699692 : Nat := 4983230072969 + 3 ^ 40 * 7699692 * 2
def baseEnd_7699692 : Nat := 439293654175377128148863

theorem tailTrace_7699692 : CollatzResearch.WordTrace tailWord_7699692 prefixEnd_7699692 439293654175377128148863 := by
  unfold tailWord_7699692
  simp only [CollatzResearch.WordTrace]
  refine ⟨140415419210669180772998665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187220558947558907697331553 140415419210669180772998665)
  ·
    refine ⟨105311564408001885579748999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140415419210669180772998665 105311564408001885579748999)
    ·
      refine ⟨157967346612002828369623499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105311564408001885579748999 157967346612002828369623499)
      ·
        refine ⟨236951019918004242554435249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157967346612002828369623499 236951019918004242554435249)
        ·
          refine ⟨177713264938503181915826437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236951019918004242554435249 177713264938503181915826437)
          ·
            refine ⟨33321237175969346609217457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177713264938503181915826437 33321237175969346609217457)
            ·
              refine ⟨24990927881977009956913093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33321237175969346609217457 24990927881977009956913093)
              ·
                refine ⟨4685798977870689366921205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24990927881977009956913093 4685798977870689366921205)
                ·
                  refine ⟨439293654175377128148863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4685798977870689366921205 439293654175377128148863)
                  ·
                    rfl

theorem cell23_7699692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_7699692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699692 prefixEnd_7699692 := by exact prefixLift 7699692
  have htrace : WordTrace (prefixWord ++ tailWord_7699692) baseStart_7699692 baseEnd_7699692 := by
    simpa [prefixWord, tailWord_7699692, baseEnd_7699692] using wordTrace_append hprefix tailTrace_7699692
  have hstable : (prefixWord ++ tailWord_7699692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699692).length < 2 ^ (prefixWord ++ tailWord_7699692).sum := by decide
  have hdescent : baseEnd_7699692 < baseStart_7699692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699812 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_7699812 : Nat := 118140960795 + 7699812 * 2 ^ 59
def prefixEnd_7699812 : Nat := 4983230072969 + 3 ^ 40 * 7699812 * 2
def baseEnd_7699812 : Nat := 1317901501752311227946405

theorem tailTrace_7699812 : CollatzResearch.WordTrace tailWord_7699812 prefixEnd_7699812 1317901501752311227946405 := by
  unfold tailWord_7699812
  simp only [CollatzResearch.WordTrace]
  refine ⟨140417607590451811020182845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187223476787269081360243793 140417607590451811020182845)
  ·
    refine ⟨52656602846419429132568567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140417607590451811020182845 52656602846419429132568567)
    ·
      refine ⟨78984904269629143698852851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52656602846419429132568567 78984904269629143698852851)
      ·
        refine ⟨118477356404443715548279277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78984904269629143698852851 118477356404443715548279277)
        ·
          refine ⟨44429008651666393330604729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118477356404443715548279277 44429008651666393330604729)
          ·
            refine ⟨33321756488749794997953547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44429008651666393330604729 33321756488749794997953547)
            ·
              refine ⟨49982634733124692496930321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33321756488749794997953547 49982634733124692496930321)
              ·
                refine ⟨37486976049843519372697741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49982634733124692496930321 37486976049843519372697741)
                ·
                  refine ⟨14057616018691319764761653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37486976049843519372697741 14057616018691319764761653)
                  ·
                    refine ⟨1317901501752311227946405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14057616018691319764761653 1317901501752311227946405)
                    ·
                      rfl

theorem cell23_7699812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_7699812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699812 prefixEnd_7699812 := by exact prefixLift 7699812
  have htrace : WordTrace (prefixWord ++ tailWord_7699812) baseStart_7699812 baseEnd_7699812 := by
    simpa [prefixWord, tailWord_7699812, baseEnd_7699812] using wordTrace_append hprefix tailTrace_7699812
  have hstable : (prefixWord ++ tailWord_7699812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699812).length < 2 ^ (prefixWord ++ tailWord_7699812).sum := by decide
  have hdescent : baseEnd_7699812 < baseStart_7699812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699843 : List Nat := [1, 1, 1, 3, 5, 2, 2, 3, 1, 1, 3]
def baseStart_7699843 : Nat := 118140960795 + 7699843 * 2 ^ 59
def prefixEnd_7699843 : Nat := 4983230072969 + 3 ^ 40 * 7699843 * 2
def baseEnd_7699843 : Nat := 3953720423157223062551573

theorem tailTrace_7699843 : CollatzResearch.WordTrace tailWord_7699843 prefixEnd_7699843 3953720423157223062551573 := by
  unfold tailWord_7699843
  simp only [CollatzResearch.WordTrace]
  refine ⟨280836345843791314334744183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187224230562527542889829455 280836345843791314334744183)
  ·
    refine ⟨421254518765686971502116275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280836345843791314334744183 421254518765686971502116275)
    ·
      refine ⟨631881778148530457253174413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421254518765686971502116275 631881778148530457253174413)
      ·
        refine ⟨236955666805698921469940405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631881778148530457253174413 236955666805698921469940405)
        ·
          refine ⟨22214593763034273887806913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236955666805698921469940405 22214593763034273887806913)
          ·
            refine ⟨16660945322275705415855185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22214593763034273887806913 16660945322275705415855185)
            ·
              refine ⟨12495708991706779061891389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16660945322275705415855185 12495708991706779061891389)
              ·
                refine ⟨4685890871890042148209271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12495708991706779061891389 4685890871890042148209271)
                ·
                  refine ⟨7028836307835063222313907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4685890871890042148209271 7028836307835063222313907)
                  ·
                    refine ⟨10543254461752594833470861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7028836307835063222313907 10543254461752594833470861)
                    ·
                      refine ⟨3953720423157223062551573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10543254461752594833470861 3953720423157223062551573)
                      ·
                        rfl

theorem cell23_7699843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_7699843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699843 prefixEnd_7699843 := by exact prefixLift 7699843
  have htrace : WordTrace (prefixWord ++ tailWord_7699843) baseStart_7699843 baseEnd_7699843 := by
    simpa [prefixWord, tailWord_7699843, baseEnd_7699843] using wordTrace_append hprefix tailTrace_7699843
  have hstable : (prefixWord ++ tailWord_7699843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699843).length < 2 ^ (prefixWord ++ tailWord_7699843).sum := by decide
  have hdescent : baseEnd_7699843 < baseStart_7699843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699852 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_7699852 : Nat := 118140960795 + 7699852 * 2 ^ 59
def prefixEnd_7699852 : Nat := 4983230072969 + 3 ^ 40 * 7699852 * 2
def baseEnd_7699852 : Nat := 3953725044483113527339031

theorem tailTrace_7699852 : CollatzResearch.WordTrace tailWord_7699852 prefixEnd_7699852 3953725044483113527339031 := by
  unfold tailWord_7699852
  simp only [CollatzResearch.WordTrace]
  refine ⟨140418337050379354435910905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187224449400505805914547873 140418337050379354435910905)
  ·
    refine ⟨105313752787784515826933179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140418337050379354435910905 105313752787784515826933179)
    ·
      refine ⟨157970629181676773740399769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105313752787784515826933179 157970629181676773740399769)
      ·
        refine ⟨118477971886257580305299827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157970629181676773740399769 118477971886257580305299827)
        ·
          refine ⟨177716957829386370457949741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118477971886257580305299827 177716957829386370457949741)
          ·
            refine ⟨66643859186019888921731153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177716957829386370457949741 66643859186019888921731153)
            ·
              refine ⟨49982894389514916691298365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66643859186019888921731153 49982894389514916691298365)
              ·
                refine ⟨18743585396068093759236887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49982894389514916691298365 18743585396068093759236887)
                ·
                  refine ⟨28115378094102140638855331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18743585396068093759236887 28115378094102140638855331)
                  ·
                    refine ⟨42173067141153210958282997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28115378094102140638855331 42173067141153210958282997)
                    ·
                      refine ⟨3953725044483113527339031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42173067141153210958282997 3953725044483113527339031)
                      ·
                        rfl

theorem cell23_7699852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_7699852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699852 prefixEnd_7699852 := by exact prefixLift 7699852
  have htrace : WordTrace (prefixWord ++ tailWord_7699852) baseStart_7699852 baseEnd_7699852 := by
    simpa [prefixWord, tailWord_7699852, baseEnd_7699852] using wordTrace_append hprefix tailTrace_7699852
  have hstable : (prefixWord ++ tailWord_7699852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699852).length < 2 ^ (prefixWord ++ tailWord_7699852).sum := by decide
  have hdescent : baseEnd_7699852 < baseStart_7699852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699869 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_7699869 : Nat := 118140960795 + 7699869 * 2 ^ 59
def prefixEnd_7699869 : Nat := 4983230072969 + 3 ^ 40 * 7699869 * 2
def baseEnd_7699869 : Nat := 3953733773654239960826453

theorem tailTrace_7699869 : CollatzResearch.WordTrace tailWord_7699869 prefixEnd_7699869 3953733773654239960826453 := by
  unfold tailWord_7699869
  simp only [CollatzResearch.WordTrace]
  refine ⟨280837294141697120775190661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187224862761131413850127107 280837294141697120775190661)
  ·
    refine ⟨52656992651568210145348249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280837294141697120775190661 52656992651568210145348249)
    ·
      refine ⟨39492744488676157609011187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52656992651568210145348249 39492744488676157609011187)
      ·
        refine ⟨59239116733014236413516781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39492744488676157609011187 59239116733014236413516781)
        ·
          refine ⟨22214668774880338655068793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59239116733014236413516781 22214668774880338655068793)
          ·
            refine ⟨16661001581160253991301595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22214668774880338655068793 16661001581160253991301595)
            ·
              refine ⟨24991502371740380986952393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16661001581160253991301595 24991502371740380986952393)
              ·
                refine ⟨18743626778805285740214295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24991502371740380986952393 18743626778805285740214295)
                ·
                  refine ⟨28115440168207928610321443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18743626778805285740214295 28115440168207928610321443)
                  ·
                    refine ⟨42173160252311892915482165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28115440168207928610321443 42173160252311892915482165)
                    ·
                      refine ⟨3953733773654239960826453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42173160252311892915482165 3953733773654239960826453)
                      ·
                        rfl

theorem cell23_7699869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_7699869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699869 prefixEnd_7699869 := by exact prefixLift 7699869
  have htrace : WordTrace (prefixWord ++ tailWord_7699869) baseStart_7699869 baseEnd_7699869 := by
    simpa [prefixWord, tailWord_7699869, baseEnd_7699869] using wordTrace_append hprefix tailTrace_7699869
  have hstable : (prefixWord ++ tailWord_7699869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699869).length < 2 ^ (prefixWord ++ tailWord_7699869).sum := by decide
  have hdescent : baseEnd_7699869 < baseStart_7699869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699902 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_7699902 : Nat := 118140960795 + 7699902 * 2 ^ 59
def prefixEnd_7699902 : Nat := 4983230072969 + 3 ^ 40 * 7699902 * 2
def baseEnd_7699902 : Nat := 1317916906171946110571267

theorem tailTrace_7699902 : CollatzResearch.WordTrace tailWord_7699902 prefixEnd_7699902 1317916906171946110571267 := by
  unfold tailWord_7699902
  simp only [CollatzResearch.WordTrace]
  refine ⟨35104812218822195926392745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187225665167051711607427973 35104812218822195926392745)
  ·
    refine ⟨26328609164116646944794559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35104812218822195926392745 26328609164116646944794559)
    ·
      refine ⟨39492913746174970417191839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26328609164116646944794559 39492913746174970417191839)
      ·
        refine ⟨59239370619262455625787759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39492913746174970417191839 59239370619262455625787759)
        ·
          refine ⟨88859055928893683438681639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59239370619262455625787759 88859055928893683438681639)
          ·
            refine ⟨133288583893340525158022459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88859055928893683438681639 133288583893340525158022459)
            ·
              refine ⟨199932875840010787737033689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133288583893340525158022459 199932875840010787737033689)
              ·
                refine ⟨149949656880008090802775267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199932875840010787737033689 149949656880008090802775267)
                ·
                  refine ⟨224924485320012136204162901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149949656880008090802775267 224924485320012136204162901)
                  ·
                    refine ⟨1317916906171946110571267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224924485320012136204162901 1317916906171946110571267)
                    ·
                      rfl

theorem cell23_7699902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_7699902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699902 prefixEnd_7699902 := by exact prefixLift 7699902
  have htrace : WordTrace (prefixWord ++ tailWord_7699902) baseStart_7699902 baseEnd_7699902 := by
    simpa [prefixWord, tailWord_7699902, baseEnd_7699902] using wordTrace_append hprefix tailTrace_7699902
  have hstable : (prefixWord ++ tailWord_7699902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699902).length < 2 ^ (prefixWord ++ tailWord_7699902).sum := by decide
  have hdescent : baseEnd_7699902 < baseStart_7699902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699912 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_7699912 : Nat := 118140960795 + 7699912 * 2 ^ 59
def prefixEnd_7699912 : Nat := 4983230072969 + 3 ^ 40 * 7699912 * 2
def baseEnd_7699912 : Nat := 3953755853322383292588755

theorem tailTrace_7699912 : CollatzResearch.WordTrace tailWord_7699912 prefixEnd_7699912 3953755853322383292588755 := by
  unfold tailWord_7699912
  simp only [CollatzResearch.WordTrace]
  refine ⟨140419431240270669559502995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187225908320360892746003993 140419431240270669559502995)
  ·
    refine ⟨210629146860406004339254493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140419431240270669559502995 210629146860406004339254493)
    ·
      refine ⟨78985930072652251627220435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210629146860406004339254493 78985930072652251627220435)
      ·
        refine ⟨118478895108978377440830653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78985930072652251627220435 118478895108978377440830653)
        ·
          refine ⟨44429585665866891540311495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118478895108978377440830653 44429585665866891540311495)
          ·
            refine ⟨66644378498800337310467243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44429585665866891540311495 66644378498800337310467243)
            ·
              refine ⟨99966567748200505965700865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66644378498800337310467243 99966567748200505965700865)
              ·
                refine ⟨74974925811150379474275649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99966567748200505965700865 74974925811150379474275649)
                ·
                  refine ⟨56231194358362784605706737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74974925811150379474275649 56231194358362784605706737)
                  ·
                    refine ⟨42173395768772088454280053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56231194358362784605706737 42173395768772088454280053)
                    ·
                      refine ⟨3953755853322383292588755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42173395768772088454280053 3953755853322383292588755)
                      ·
                        rfl

theorem cell23_7699912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_7699912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699912 prefixEnd_7699912 := by exact prefixLift 7699912
  have htrace : WordTrace (prefixWord ++ tailWord_7699912) baseStart_7699912 baseEnd_7699912 := by
    simpa [prefixWord, tailWord_7699912, baseEnd_7699912] using wordTrace_append hprefix tailTrace_7699912
  have hstable : (prefixWord ++ tailWord_7699912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699912).length < 2 ^ (prefixWord ++ tailWord_7699912).sum := by decide
  have hdescent : baseEnd_7699912 < baseStart_7699912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699916 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_7699916 : Nat := 118140960795 + 7699916 * 2 ^ 59
def prefixEnd_7699916 : Nat := 4983230072969 + 3 ^ 40 * 7699916 * 2
def baseEnd_7699916 : Nat := 3953757907245001276938737

theorem tailTrace_7699916 : CollatzResearch.WordTrace tailWord_7699916 prefixEnd_7699916 3953757907245001276938737 := by
  unfold tailWord_7699916
  simp only [CollatzResearch.WordTrace]
  refine ⟨140419504186263423901075801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187226005581684565201434401 140419504186263423901075801)
  ·
    refine ⟨105314628139697567925806851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140419504186263423901075801 105314628139697567925806851)
    ·
      refine ⟨157971942209546351888710277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105314628139697567925806851 157971942209546351888710277)
      ·
        refine ⟨29619739164289940979133177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157971942209546351888710277 29619739164289940979133177)
        ·
          refine ⟨22214804373217455734349883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29619739164289940979133177 22214804373217455734349883)
          ·
            refine ⟨33322206559826183601524825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22214804373217455734349883 33322206559826183601524825)
            ·
              refine ⟨24991654919869637701143619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33322206559826183601524825 24991654919869637701143619)
              ·
                refine ⟨37487482379804456551715429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24991654919869637701143619 37487482379804456551715429)
                ·
                  refine ⟨7028902946213335603446643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37487482379804456551715429 7028902946213335603446643)
                  ·
                    refine ⟨10543354419320003405169965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7028902946213335603446643 10543354419320003405169965)
                    ·
                      refine ⟨3953757907245001276938737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10543354419320003405169965 3953757907245001276938737)
                      ·
                        rfl

theorem cell23_7699916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_7699916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699916 prefixEnd_7699916 := by exact prefixLift 7699916
  have htrace : WordTrace (prefixWord ++ tailWord_7699916) baseStart_7699916 baseEnd_7699916 := by
    simpa [prefixWord, tailWord_7699916, baseEnd_7699916] using wordTrace_append hprefix tailTrace_7699916
  have hstable : (prefixWord ++ tailWord_7699916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699916).length < 2 ^ (prefixWord ++ tailWord_7699916).sum := by decide
  have hdescent : baseEnd_7699916 < baseStart_7699916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699933 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_7699933 : Nat := 118140960795 + 7699933 * 2 ^ 59
def prefixEnd_7699933 : Nat := 4983230072969 + 3 ^ 40 * 7699933 * 2
def baseEnd_7699933 : Nat := 3953766636416127710426159

theorem tailTrace_7699933 : CollatzResearch.WordTrace tailWord_7699933 prefixEnd_7699933 3953766636416127710426159 := by
  unfold tailWord_7699933
  simp only [CollatzResearch.WordTrace]
  refine ⟨280839628413465259705520453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187226418942310173137013635 280839628413465259705520453)
  ·
    refine ⟨52657430327524736194785085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280839628413465259705520453 52657430327524736194785085)
    ·
      refine ⟨19746536372821776073044407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52657430327524736194785085 19746536372821776073044407)
      ·
        refine ⟨29619804559232664109566611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19746536372821776073044407 29619804559232664109566611)
        ·
          refine ⟨44429706838848996164349917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29619804559232664109566611 44429706838848996164349917)
          ·
            refine ⟨16661140064568373561631219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44429706838848996164349917 16661140064568373561631219)
            ·
              refine ⟨24991710096852560342446829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16661140064568373561631219 24991710096852560342446829)
              ·
                refine ⟨9371891286319710128417561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24991710096852560342446829 9371891286319710128417561)
                ·
                  refine ⟨7028918464739782596313171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9371891286319710128417561 7028918464739782596313171)
                  ·
                    refine ⟨10543377697109673894469757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7028918464739782596313171 10543377697109673894469757)
                    ·
                      refine ⟨3953766636416127710426159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10543377697109673894469757 3953766636416127710426159)
                      ·
                        rfl

theorem cell23_7699933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_7699933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699933 prefixEnd_7699933 := by exact prefixLift 7699933
  have htrace : WordTrace (prefixWord ++ tailWord_7699933) baseStart_7699933 baseEnd_7699933 := by
    simpa [prefixWord, tailWord_7699933, baseEnd_7699933] using wordTrace_append hprefix tailTrace_7699933
  have hstable : (prefixWord ++ tailWord_7699933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699933).length < 2 ^ (prefixWord ++ tailWord_7699933).sum := by decide
  have hdescent : baseEnd_7699933 < baseStart_7699933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699943 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_7699943 : Nat := 118140960795 + 7699943 * 2 ^ 59
def prefixEnd_7699943 : Nat := 4983230072969 + 3 ^ 40 * 7699943 * 2
def baseEnd_7699943 : Nat := 3953771771222672671301113

theorem tailTrace_7699943 : CollatzResearch.WordTrace tailWord_7699943 prefixEnd_7699943 3953771771222672671301113 := by
  unfold tailWord_7699943
  simp only [CollatzResearch.WordTrace]
  refine ⟨280839993143429031413384483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187226662095619354275589655 280839993143429031413384483)
  ·
    refine ⟨421259989715143547120076725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280839993143429031413384483 421259989715143547120076725)
    ·
      refine ⟨39493124035794707542507193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 421259989715143547120076725 39493124035794707542507193)
      ·
        refine ⟨29619843026846030656880395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39493124035794707542507193 29619843026846030656880395)
        ·
          refine ⟨44429764540269045985320593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29619843026846030656880395 44429764540269045985320593)
          ·
            refine ⟨33322323405201784488990445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44429764540269045985320593 33322323405201784488990445)
            ·
              refine ⟨12495871276950669183371417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33322323405201784488990445 12495871276950669183371417)
              ·
                refine ⟨9371903457713001887528563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12495871276950669183371417 9371903457713001887528563)
                ·
                  refine ⟨14057855186569502831292845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9371903457713001887528563 14057855186569502831292845)
                  ·
                    refine ⟨5271695694963563561734817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14057855186569502831292845 5271695694963563561734817)
                    ·
                      refine ⟨3953771771222672671301113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271695694963563561734817 3953771771222672671301113)
                      ·
                        rfl

theorem cell23_7699943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_7699943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699943 prefixEnd_7699943 := by exact prefixLift 7699943
  have htrace : WordTrace (prefixWord ++ tailWord_7699943) baseStart_7699943 baseEnd_7699943 := by
    simpa [prefixWord, tailWord_7699943, baseEnd_7699943] using wordTrace_append hprefix tailTrace_7699943
  have hstable : (prefixWord ++ tailWord_7699943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699943).length < 2 ^ (prefixWord ++ tailWord_7699943).sum := by decide
  have hdescent : baseEnd_7699943 < baseStart_7699943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7699989 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_7699989 : Nat := 118140960795 + 7699989 * 2 ^ 59
def prefixEnd_7699989 : Nat := 4983230072969 + 3 ^ 40 * 7699989 * 2
def baseEnd_7699989 : Nat := 3953795391332779491325901

theorem tailTrace_7699989 : CollatzResearch.WordTrace tailWord_7699989 prefixEnd_7699989 3953795391332779491325901 := by
  unfold tailWord_7699989
  simp only [CollatzResearch.WordTrace]
  refine ⟨280841670901262381269559021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187227780600841587513039347 280841670901262381269559021)
  ·
    refine ⟨105315626587973392976084633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280841670901262381269559021 105315626587973392976084633)
    ·
      refine ⟨78986719940980044732063475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105315626587973392976084633 78986719940980044732063475)
      ·
        refine ⟨118480079911470067098095213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78986719940980044732063475 118480079911470067098095213)
        ·
          refine ⟨44430029966801275161785705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118480079911470067098095213 44430029966801275161785705)
          ·
            refine ⟨33322522475100956371339279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44430029966801275161785705 33322522475100956371339279)
            ·
              refine ⟨49983783712651434557008919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33322522475100956371339279 49983783712651434557008919)
              ·
                refine ⟨74975675568977151835513379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49983783712651434557008919 74975675568977151835513379)
                ·
                  refine ⟨112463513353465727753270069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74975675568977151835513379 112463513353465727753270069)
                  ·
                    refine ⟨10543454376887411976869069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112463513353465727753270069 10543454376887411976869069)
                    ·
                      refine ⟨3953795391332779491325901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10543454376887411976869069 3953795391332779491325901)
                      ·
                        rfl

theorem cell23_7699989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_7699989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7699989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7699989 prefixEnd_7699989 := by exact prefixLift 7699989
  have htrace : WordTrace (prefixWord ++ tailWord_7699989) baseStart_7699989 baseEnd_7699989 := by
    simpa [prefixWord, tailWord_7699989, baseEnd_7699989] using wordTrace_append hprefix tailTrace_7699989
  have hstable : (prefixWord ++ tailWord_7699989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7699989).length < 2 ^ (prefixWord ++ tailWord_7699989).sum := by decide
  have hdescent : baseEnd_7699989 < baseStart_7699989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7699989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700049 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_7700049 : Nat := 118140960795 + 7700049 * 2 ^ 59
def prefixEnd_7700049 : Nat := 4983230072969 + 3 ^ 40 * 7700049 * 2
def baseEnd_7700049 : Nat := 3953826200172049256575625

theorem tailTrace_7700049 : CollatzResearch.WordTrace tailWord_7700049 prefixEnd_7700049 3953826200172049256575625 := by
  unfold tailWord_7700049
  simp only [CollatzResearch.WordTrace]
  refine ⟨280843859281045011516743201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187229239520696674344495467 280843859281045011516743201)
  ·
    refine ⟨210632894460783758637557401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280843859281045011516743201 210632894460783758637557401)
    ·
      refine ⟨157974670845587818978168051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210632894460783758637557401 157974670845587818978168051)
      ·
        refine ⟨236962006268381728467252077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157974670845587818978168051 236962006268381728467252077)
        ·
          refine ⟨88860752350643148175219529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236962006268381728467252077 88860752350643148175219529)
          ·
            refine ⟨66645564262982361131414647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88860752350643148175219529 66645564262982361131414647)
            ·
              refine ⟨99968346394473541697121971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66645564262982361131414647 99968346394473541697121971)
              ·
                refine ⟨149952519591710312545682957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99968346394473541697121971 149952519591710312545682957)
                ·
                  refine ⟨56232194846891367204631109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149952519591710312545682957 56232194846891367204631109)
                  ·
                    refine ⟨10543536533792131350868333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56232194846891367204631109 10543536533792131350868333)
                    ·
                      refine ⟨3953826200172049256575625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10543536533792131350868333 3953826200172049256575625)
                      ·
                        rfl

theorem cell23_7700049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_7700049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700049 prefixEnd_7700049 := by exact prefixLift 7700049
  have htrace : WordTrace (prefixWord ++ tailWord_7700049) baseStart_7700049 baseEnd_7700049 := by
    simpa [prefixWord, tailWord_7700049, baseEnd_7700049] using wordTrace_append hprefix tailTrace_7700049
  have hstable : (prefixWord ++ tailWord_7700049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700049).length < 2 ^ (prefixWord ++ tailWord_7700049).sum := by decide
  have hdescent : baseEnd_7700049 < baseStart_7700049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700069 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 8]
def baseStart_7700069 : Nat := 118140960795 + 7700069 * 2 ^ 59
def prefixEnd_7700069 : Nat := 4983230072969 + 3 ^ 40 * 7700069 * 2
def baseEnd_7700069 : Nat := 439315163309459908702837

theorem tailTrace_7700069 : CollatzResearch.WordTrace tailWord_7700069 prefixEnd_7700069 439315163309459908702837 := by
  unfold tailWord_7700069
  simp only [CollatzResearch.WordTrace]
  refine ⟨280844588740972554932471261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187229725827315036621647507 280844588740972554932471261)
  ·
    refine ⟨105316720777864708099676723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280844588740972554932471261 105316720777864708099676723)
    ·
      refine ⟨157975081166797062149515085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105316720777864708099676723 157975081166797062149515085)
      ·
        refine ⟨59240655437548898306068157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157975081166797062149515085 59240655437548898306068157)
        ·
          refine ⟨22215245789080836864775559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59240655437548898306068157 22215245789080836864775559)
          ·
            refine ⟨33322868683621255297163339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22215245789080836864775559 33322868683621255297163339)
            ·
              refine ⟨49984303025431882945745009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33322868683621255297163339 49984303025431882945745009)
              ·
                refine ⟨37488227269073912209308757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49984303025431882945745009 37488227269073912209308757)
                ·
                  refine ⟨439315163309459908702837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37488227269073912209308757 439315163309459908702837)
                  ·
                    rfl

theorem cell23_7700069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_7700069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700069 prefixEnd_7700069 := by exact prefixLift 7700069
  have htrace : WordTrace (prefixWord ++ tailWord_7700069) baseStart_7700069 baseEnd_7700069 := by
    simpa [prefixWord, tailWord_7700069, baseEnd_7700069] using wordTrace_append hprefix tailTrace_7700069
  have hstable : (prefixWord ++ tailWord_7700069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700069).length < 2 ^ (prefixWord ++ tailWord_7700069).sum := by decide
  have hdescent : baseEnd_7700069 < baseStart_7700069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700073 : List Nat := [1, 2, 1, 1, 1, 4, 5, 3, 1, 4]
def baseStart_7700073 : Nat := 118140960795 + 7700073 * 2 ^ 59
def prefixEnd_7700073 : Nat := 4983230072969 + 3 ^ 40 * 7700073 * 2
def baseEnd_7700073 : Nat := 1317946174569252387558505

theorem tailTrace_7700073 : CollatzResearch.WordTrace tailWord_7700073 prefixEnd_7700073 1317946174569252387558505 := by
  unfold tailWord_7700073
  simp only [CollatzResearch.WordTrace]
  refine ⟨280844734632958063615616873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187229823088638709077077915 280844734632958063615616873)
  ·
    refine ⟨210633550974718547711712655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280844734632958063615616873 210633550974718547711712655)
    ·
      refine ⟨315950326462077821567568983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210633550974718547711712655 315950326462077821567568983)
      ·
        refine ⟨473925489693116732351353475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315950326462077821567568983 473925489693116732351353475)
        ·
          refine ⟨710888234539675098527030213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473925489693116732351353475 710888234539675098527030213)
          ·
            refine ⟨133291543976189080973818165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 710888234539675098527030213 133291543976189080973818165)
            ·
              refine ⟨12496082247767726341295453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133291543976189080973818165 12496082247767726341295453)
              ·
                refine ⟨4686030842912897377985795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12496082247767726341295453 4686030842912897377985795)
                ·
                  refine ⟨7029046264369346066978693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686030842912897377985795 7029046264369346066978693)
                  ·
                    refine ⟨1317946174569252387558505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7029046264369346066978693 1317946174569252387558505)
                    ·
                      rfl

theorem cell23_7700073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 1, 4].length) (baseStart_7700073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700073 prefixEnd_7700073 := by exact prefixLift 7700073
  have htrace : WordTrace (prefixWord ++ tailWord_7700073) baseStart_7700073 baseEnd_7700073 := by
    simpa [prefixWord, tailWord_7700073, baseEnd_7700073] using wordTrace_append hprefix tailTrace_7700073
  have hstable : (prefixWord ++ tailWord_7700073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700073).length < 2 ^ (prefixWord ++ tailWord_7700073).sum := by decide
  have hdescent : baseEnd_7700073 < baseStart_7700073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700086 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_7700086 : Nat := 118140960795 + 7700086 * 2 ^ 59
def prefixEnd_7700086 : Nat := 4983230072969 + 3 ^ 40 * 7700086 * 2
def baseEnd_7700086 : Nat := 439316133217362845756995

theorem tailTrace_7700086 : CollatzResearch.WordTrace tailWord_7700086 prefixEnd_7700086 439316133217362845756995 := by
  unfold tailWord_7700086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17552825548869435427240007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187230139187940644557226741 17552825548869435427240007)
  ·
    refine ⟨26329238323304153140860011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17552825548869435427240007 26329238323304153140860011)
    ·
      refine ⟨39493857484956229711290017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26329238323304153140860011 39493857484956229711290017)
      ·
        refine ⟨29620393113717172283467513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39493857484956229711290017 29620393113717172283467513)
        ·
          refine ⟨22215294835287879212600635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29620393113717172283467513 22215294835287879212600635)
          ·
            refine ⟨33322942252931818818900953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22215294835287879212600635 33322942252931818818900953)
            ·
              refine ⟨24992206689698864114175715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33322942252931818818900953 24992206689698864114175715)
              ·
                refine ⟨37488310034548296171263573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24992206689698864114175715 37488310034548296171263573)
                ·
                  refine ⟨439316133217362845756995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37488310034548296171263573 439316133217362845756995)
                  ·
                    rfl

theorem cell23_7700086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_7700086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700086 prefixEnd_7700086 := by exact prefixLift 7700086
  have htrace : WordTrace (prefixWord ++ tailWord_7700086) baseStart_7700086 baseEnd_7700086 := by
    simpa [prefixWord, tailWord_7700086, baseEnd_7700086] using wordTrace_append hprefix tailTrace_7700086
  have hstable : (prefixWord ++ tailWord_7700086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700086).length < 2 ^ (prefixWord ++ tailWord_7700086).sum := by decide
  have hdescent : baseEnd_7700086 < baseStart_7700086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700099 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 3, 5]
def baseStart_7700099 : Nat := 118140960795 + 7700099 * 2 ^ 59
def prefixEnd_7700099 : Nat := 4983230072969 + 3 ^ 40 * 7700099 * 2
def baseEnd_7700099 : Nat := 1317950624734924686983465

theorem tailTrace_7700099 : CollatzResearch.WordTrace tailWord_7700099 prefixEnd_7700099 1317950624734924686983465 := by
  unfold tailWord_7700099
  simp only [CollatzResearch.WordTrace]
  refine ⟨280845682930863870056063351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187230455287242580037375567 280845682930863870056063351)
  ·
    refine ⟨421268524396295805084095027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280845682930863870056063351 421268524396295805084095027)
    ·
      refine ⟨631902786594443707626142541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421268524396295805084095027 631902786594443707626142541)
      ·
        refine ⟨236963544972916390359803453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631902786594443707626142541 236963544972916390359803453)
        ·
          refine ⟨88861329364843646384926295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236963544972916390359803453 88861329364843646384926295)
          ·
            refine ⟨133291994047265469577389443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88861329364843646384926295 133291994047265469577389443)
            ·
              refine ⟨199937991070898204366084165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133291994047265469577389443 199937991070898204366084165)
              ·
                refine ⟨37488373325793413318640781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199937991070898204366084165 37488373325793413318640781)
                ·
                  refine ⟨14058139997172529994490293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37488373325793413318640781 14058139997172529994490293)
                  ·
                    refine ⟨1317950624734924686983465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14058139997172529994490293 1317950624734924686983465)
                    ·
                      rfl

theorem cell23_7700099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 5].length) (baseStart_7700099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700099 prefixEnd_7700099 := by exact prefixLift 7700099
  have htrace : WordTrace (prefixWord ++ tailWord_7700099) baseStart_7700099 baseEnd_7700099 := by
    simpa [prefixWord, tailWord_7700099, baseEnd_7700099] using wordTrace_append hprefix tailTrace_7700099
  have hstable : (prefixWord ++ tailWord_7700099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700099).length < 2 ^ (prefixWord ++ tailWord_7700099).sum := by decide
  have hdescent : baseEnd_7700099 < baseStart_7700099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700103 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 6]
def baseStart_7700103 : Nat := 118140960795 + 7700103 * 2 ^ 59
def prefixEnd_7700103 : Nat := 4983230072969 + 3 ^ 40 * 7700103 * 2
def baseEnd_7700103 : Nat := 439317103125265782811153

theorem tailTrace_7700103 : CollatzResearch.WordTrace tailWord_7700103 prefixEnd_7700103 439317103125265782811153 := by
  unfold tailWord_7700103
  simp only [CollatzResearch.WordTrace]
  refine ⟨280845828822849378739208963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187230552548566252492805975 280845828822849378739208963)
  ·
    refine ⟨421268743234274068108813445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280845828822849378739208963 421268743234274068108813445)
    ·
      refine ⟨78987889356426387770402521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421268743234274068108813445 78987889356426387770402521)
      ·
        refine ⟨59240917017319790827801891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78987889356426387770402521 59240917017319790827801891)
        ·
          refine ⟨88861375525979686241702837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59240917017319790827801891 88861375525979686241702837)
          ·
            refine ⟨8330753955560595585159641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88861375525979686241702837 8330753955560595585159641)
            ·
              refine ⟨6248065466670446688869731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8330753955560595585159641 6248065466670446688869731)
              ·
                refine ⟨9372098200005670033304597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6248065466670446688869731 9372098200005670033304597)
                ·
                  refine ⟨439317103125265782811153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9372098200005670033304597 439317103125265782811153)
                  ·
                    rfl

theorem cell23_7700103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 6].length) (baseStart_7700103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700103 prefixEnd_7700103 := by exact prefixLift 7700103
  have htrace : WordTrace (prefixWord ++ tailWord_7700103) baseStart_7700103 baseEnd_7700103 := by
    simpa [prefixWord, tailWord_7700103, baseEnd_7700103] using wordTrace_append hprefix tailTrace_7700103
  have hstable : (prefixWord ++ tailWord_7700103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700103).length < 2 ^ (prefixWord ++ tailWord_7700103).sum := by decide
  have hdescent : baseEnd_7700103 < baseStart_7700103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700146 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_7700146 : Nat := 118140960795 + 7700146 * 2 ^ 59
def prefixEnd_7700146 : Nat := 4983230072969 + 3 ^ 40 * 7700146 * 2
def baseEnd_7700146 : Nat := 1317958669265178459020893

theorem tailTrace_7700146 : CollatzResearch.WordTrace tailWord_7700146 prefixEnd_7700146 1317958669265178459020893 := by
  unfold tailWord_7700146
  simp only [CollatzResearch.WordTrace]
  refine ⟨70211849290423399270756073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187231598107795731388682861 70211849290423399270756073)
  ·
    refine ⟨52658886967817549453067055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70211849290423399270756073 52658886967817549453067055)
    ·
      refine ⟨78988330451726324179600583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52658886967817549453067055 78988330451726324179600583)
      ·
        refine ⟨118482495677589486269400875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78988330451726324179600583 118482495677589486269400875)
        ·
          refine ⟨177723743516384229404101313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118482495677589486269400875 177723743516384229404101313)
          ·
            refine ⟨133292807637288172053075985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177723743516384229404101313 133292807637288172053075985)
            ·
              refine ⟨99969605727966129039806989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133292807637288172053075985 99969605727966129039806989)
              ·
                refine ⟨37488602147987298389927621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99969605727966129039806989 37488602147987298389927621)
                ·
                  refine ⟨7029112902747618448111429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37488602147987298389927621 7029112902747618448111429)
                  ·
                    refine ⟨1317958669265178459020893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7029112902747618448111429 1317958669265178459020893)
                    ·
                      rfl

theorem cell23_7700146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_7700146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700146 prefixEnd_7700146 := by exact prefixLift 7700146
  have htrace : WordTrace (prefixWord ++ tailWord_7700146) baseStart_7700146 baseEnd_7700146 := by
    simpa [prefixWord, tailWord_7700146, baseEnd_7700146] using wordTrace_append hprefix tailTrace_7700146
  have hstable : (prefixWord ++ tailWord_7700146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700146).length < 2 ^ (prefixWord ++ tailWord_7700146).sum := by decide
  have hdescent : baseEnd_7700146 < baseStart_7700146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700219 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 1, 8]
def baseStart_7700219 : Nat := 118140960795 + 7700219 * 2 ^ 59
def prefixEnd_7700219 : Nat := 4983230072969 + 3 ^ 40 * 7700219 * 2
def baseEnd_7700219 : Nat := 1317971163961104530483281

theorem tailTrace_7700219 : CollatzResearch.WordTrace tailWord_7700219 prefixEnd_7700219 1317971163961104530483281 := by
  unfold tailWord_7700219
  simp only [CollatzResearch.WordTrace]
  refine ⟨280850059690429130550431711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187233373126952753700287807 280850059690429130550431711)
  ·
    refine ⟨421275089535643695825647567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280850059690429130550431711 421275089535643695825647567)
    ·
      refine ⟨631912634303465543738471351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421275089535643695825647567 631912634303465543738471351)
      ·
        refine ⟨947868951455198315607707027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631912634303465543738471351 947868951455198315607707027)
        ·
          refine ⟨1421803427182797473411560541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947868951455198315607707027 1421803427182797473411560541)
          ·
            refine ⟨533176285193549052529335203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1421803427182797473411560541 533176285193549052529335203)
            ·
              refine ⟨799764427790323578794002805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533176285193549052529335203 799764427790323578794002805)
              ·
                refine ⟨74977915105342835511937763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 799764427790323578794002805 74977915105342835511937763)
                ·
                  refine ⟨112466872658014253267906645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74977915105342835511937763 112466872658014253267906645)
                  ·
                    refine ⟨1317971163961104530483281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112466872658014253267906645 1317971163961104530483281)
                    ·
                      rfl

theorem cell23_7700219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 8].length) (baseStart_7700219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700219 prefixEnd_7700219 := by exact prefixLift 7700219
  have htrace : WordTrace (prefixWord ++ tailWord_7700219) baseStart_7700219 baseEnd_7700219 := by
    simpa [prefixWord, tailWord_7700219, baseEnd_7700219] using wordTrace_append hprefix tailTrace_7700219
  have hstable : (prefixWord ++ tailWord_7700219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700219).length < 2 ^ (prefixWord ++ tailWord_7700219).sum := by decide
  have hdescent : baseEnd_7700219 < baseStart_7700219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700281 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7700281 : Nat := 118140960795 + 7700281 * 2 ^ 59
def prefixEnd_7700281 : Nat := 4983230072969 + 3 ^ 40 * 7700281 * 2
def baseEnd_7700281 : Nat := 3953945327683892348874559

theorem tailTrace_7700281 : CollatzResearch.WordTrace tailWord_7700281 prefixEnd_7700281 3953945327683892348874559 := by
  unfold tailWord_7700281
  simp only [CollatzResearch.WordTrace]
  refine ⟨280852321016204515139188697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187234880677469676759459131 280852321016204515139188697)
  ·
    refine ⟨210639240762153386354391523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280852321016204515139188697 210639240762153386354391523)
    ·
      refine ⟨315958861143230079531587285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210639240762153386354391523 315958861143230079531587285)
      ·
        refine ⟨7405285808044454989021577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 315958861143230079531587285 7405285808044454989021577)
        ·
          refine ⟨5553964356033341241766183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7405285808044454989021577 5553964356033341241766183)
          ·
            refine ⟨8330946534050011862649275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553964356033341241766183 8330946534050011862649275)
            ·
              refine ⟨12496419801075017793973913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8330946534050011862649275 12496419801075017793973913)
              ·
                refine ⟨9372314850806263345480435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12496419801075017793973913 9372314850806263345480435)
                ·
                  refine ⟨14058472276209395018220653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9372314850806263345480435 14058472276209395018220653)
                  ·
                    refine ⟨5271927103578523131832745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14058472276209395018220653 5271927103578523131832745)
                    ·
                      refine ⟨3953945327683892348874559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271927103578523131832745 3953945327683892348874559)
                      ·
                        rfl

theorem cell23_7700281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7700281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700281 prefixEnd_7700281 := by exact prefixLift 7700281
  have htrace : WordTrace (prefixWord ++ tailWord_7700281) baseStart_7700281 baseEnd_7700281 := by
    simpa [prefixWord, tailWord_7700281, baseEnd_7700281] using wordTrace_append hprefix tailTrace_7700281
  have hstable : (prefixWord ++ tailWord_7700281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700281).length < 2 ^ (prefixWord ++ tailWord_7700281).sum := by decide
  have hdescent : baseEnd_7700281 < baseStart_7700281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700294 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7700294 : Nat := 118140960795 + 7700294 * 2 ^ 59
def prefixEnd_7700294 : Nat := 4983230072969 + 3 ^ 40 * 7700294 * 2
def baseEnd_7700294 : Nat := 3953952002932400798011999

theorem tailTrace_7700294 : CollatzResearch.WordTrace tailWord_7700294 prefixEnd_7700294 3953952002932400798011999 := by
  unfold tailWord_7700294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776649848911169323731623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187235196776771612239607957 8776649848911169323731623)
  ·
    refine ⟨13164974773366753985597435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8776649848911169323731623 13164974773366753985597435)
    ·
      refine ⟨19747462160050130978396153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13164974773366753985597435 19747462160050130978396153)
      ·
        refine ⟨14810596620037598233797115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19747462160050130978396153 14810596620037598233797115)
        ·
          refine ⟨22215894930056397350695673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14810596620037598233797115 22215894930056397350695673)
          ·
            refine ⟨16661921197542298013021755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22215894930056397350695673 16661921197542298013021755)
            ·
              refine ⟨24992881796313447019532633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16661921197542298013021755 24992881796313447019532633)
              ·
                refine ⟨18744661347235085264649475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24992881796313447019532633 18744661347235085264649475)
                ·
                  refine ⟨28116992020852627896974213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18744661347235085264649475 28116992020852627896974213)
                  ·
                    refine ⟨5271936003909867730682665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28116992020852627896974213 5271936003909867730682665)
                    ·
                      refine ⟨3953952002932400798011999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5271936003909867730682665 3953952002932400798011999)
                      ·
                        rfl

theorem cell23_7700294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7700294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700294 prefixEnd_7700294 := by exact prefixLift 7700294
  have htrace : WordTrace (prefixWord ++ tailWord_7700294) baseStart_7700294 baseEnd_7700294 := by
    simpa [prefixWord, tailWord_7700294, baseEnd_7700294] using wordTrace_append hprefix tailTrace_7700294
  have hstable : (prefixWord ++ tailWord_7700294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700294).length < 2 ^ (prefixWord ++ tailWord_7700294).sum := by decide
  have hdescent : baseEnd_7700294 < baseStart_7700294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700333 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_7700333 : Nat := 118140960795 + 7700333 * 2 ^ 59
def prefixEnd_7700333 : Nat := 4983230072969 + 3 ^ 40 * 7700333 * 2
def baseEnd_7700333 : Nat := 3953972028677926145424319

theorem tailTrace_7700333 : CollatzResearch.WordTrace tailWord_7700333 prefixEnd_7700333 3953972028677926145424319 := by
  unfold tailWord_7700333
  simp only [CollatzResearch.WordTrace]
  refine ⟨280854217612016128020081653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187236145074677418680054435 280854217612016128020081653)
  ·
    refine ⟨26330082901126512001882655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280854217612016128020081653 26330082901126512001882655)
    ·
      refine ⟨39495124351689768002823983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26330082901126512001882655 39495124351689768002823983)
      ·
        refine ⟨59242686527534652004235975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39495124351689768002823983 59242686527534652004235975)
        ·
          refine ⟨88864029791301978006353963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59242686527534652004235975 88864029791301978006353963)
          ·
            refine ⟨133296044686952967009530945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88864029791301978006353963 133296044686952967009530945)
            ·
              refine ⟨99972033515214725257148209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133296044686952967009530945 99972033515214725257148209)
              ·
                refine ⟨74979025136411043942861157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99972033515214725257148209 74979025136411043942861157)
                ·
                  refine ⟨14058567213077070739286467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74979025136411043942861157 14058567213077070739286467)
                  ·
                    refine ⟨21087850819615606108929701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14058567213077070739286467 21087850819615606108929701)
                    ·
                      refine ⟨3953972028677926145424319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21087850819615606108929701 3953972028677926145424319)
                      ·
                        rfl

theorem cell23_7700333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_7700333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700333 prefixEnd_7700333 := by exact prefixLift 7700333
  have htrace : WordTrace (prefixWord ++ tailWord_7700333) baseStart_7700333 baseEnd_7700333 := by
    simpa [prefixWord, tailWord_7700333, baseEnd_7700333] using wordTrace_append hprefix tailTrace_7700333
  have hstable : (prefixWord ++ tailWord_7700333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700333).length < 2 ^ (prefixWord ++ tailWord_7700333).sum := by decide
  have hdescent : baseEnd_7700333 < baseStart_7700333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700423 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_7700423 : Nat := 118140960795 + 7700423 * 2 ^ 59
def prefixEnd_7700423 : Nat := 4983230072969 + 3 ^ 40 * 7700423 * 2
def baseEnd_7700423 : Nat := 3954018241936830793298905

theorem tailTrace_7700423 : CollatzResearch.WordTrace tailWord_7700423 prefixEnd_7700423 3954018241936830793298905 := by
  unfold tailWord_7700423
  simp only [CollatzResearch.WordTrace]
  refine ⟨280857500181690073390857923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187238333454460048927238615 280857500181690073390857923)
  ·
    refine ⟨421286250272535110086286885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280857500181690073390857923 421286250272535110086286885)
    ·
      refine ⟨78991171926100333141178791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421286250272535110086286885 78991171926100333141178791)
      ·
        refine ⟨118486757889150499711768187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78991171926100333141178791 118486757889150499711768187)
        ·
          refine ⟨177730136833725749567652281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118486757889150499711768187 177730136833725749567652281)
          ·
            refine ⟨133297602625294312175739211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177730136833725749567652281 133297602625294312175739211)
            ·
              refine ⟨199946403937941468263608817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133297602625294312175739211 199946403937941468263608817)
              ·
                refine ⟨149959802953456101197706613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199946403937941468263608817 149959802953456101197706613)
                ·
                  refine ⟨14058731526886509487284995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149959802953456101197706613 14058731526886509487284995)
                  ·
                    refine ⟨21088097290329764230927493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14058731526886509487284995 21088097290329764230927493)
                    ·
                      refine ⟨3954018241936830793298905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21088097290329764230927493 3954018241936830793298905)
                      ·
                        rfl

theorem cell23_7700423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_7700423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700423 prefixEnd_7700423 := by exact prefixLift 7700423
  have htrace : WordTrace (prefixWord ++ tailWord_7700423) baseStart_7700423 baseEnd_7700423 := by
    simpa [prefixWord, tailWord_7700423, baseEnd_7700423] using wordTrace_append hprefix tailTrace_7700423
  have hstable : (prefixWord ++ tailWord_7700423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700423).length < 2 ^ (prefixWord ++ tailWord_7700423).sum := by decide
  have hdescent : baseEnd_7700423 < baseStart_7700423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700461 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7700461 : Nat := 118140960795 + 7700461 * 2 ^ 59
def prefixEnd_7700461 : Nat := 4983230072969 + 3 ^ 40 * 7700461 * 2
def baseEnd_7700461 : Nat := 3954037754201701644623731

theorem tailTrace_7700461 : CollatzResearch.WordTrace tailWord_7700461 prefixEnd_7700461 3954037754201701644623731 := by
  unfold tailWord_7700461
  simp only [CollatzResearch.WordTrace]
  refine ⟨280858886155552405880741237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187239257437034937253827491 280858886155552405880741237)
  ·
    refine ⟨26330520577083038051319491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280858886155552405880741237 26330520577083038051319491)
    ·
      refine ⟨39495780865624557076979237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26330520577083038051319491 39495780865624557076979237)
      ·
        refine ⟨7405458912304604451933607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39495780865624557076979237 7405458912304604451933607)
        ·
          refine ⟨11108188368456906677900411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7405458912304604451933607 11108188368456906677900411)
          ·
            refine ⟨16662282552685360016850617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11108188368456906677900411 16662282552685360016850617)
            ·
              refine ⟨12496711914514020012637963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16662282552685360016850617 12496711914514020012637963)
              ·
                refine ⟨18745067871771030018956945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12496711914514020012637963 18745067871771030018956945)
                ·
                  refine ⟨14058800903828272514217709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18745067871771030018956945 14058800903828272514217709)
                  ·
                    refine ⟨5272050338935602192831641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14058800903828272514217709 5272050338935602192831641)
                    ·
                      refine ⟨3954037754201701644623731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272050338935602192831641 3954037754201701644623731)
                      ·
                        rfl

theorem cell23_7700461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7700461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700461 prefixEnd_7700461 := by exact prefixLift 7700461
  have htrace : WordTrace (prefixWord ++ tailWord_7700461) baseStart_7700461 baseEnd_7700461 := by
    simpa [prefixWord, tailWord_7700461, baseEnd_7700461] using wordTrace_append hprefix tailTrace_7700461
  have hstable : (prefixWord ++ tailWord_7700461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700461).length < 2 ^ (prefixWord ++ tailWord_7700461).sum := by decide
  have hdescent : baseEnd_7700461 < baseStart_7700461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700517 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 3, 3, 2]
def baseStart_7700517 : Nat := 118140960795 + 7700517 * 2 ^ 59
def prefixEnd_7700517 : Nat := 4983230072969 + 3 ^ 40 * 7700517 * 2
def baseEnd_7700517 : Nat := 3954066509118353425523473

theorem tailTrace_7700517 : CollatzResearch.WordTrace tailWord_7700517 prefixEnd_7700517 3954066509118353425523473 := by
  unfold tailWord_7700517
  simp only [CollatzResearch.WordTrace]
  refine ⟨280860928643349527444779805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187240619095566351629853203 280860928643349527444779805)
  ·
    refine ⟨105322848241256072791792427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280860928643349527444779805 105322848241256072791792427)
    ·
      refine ⟨157984272361884109187688641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105322848241256072791792427 157984272361884109187688641)
      ·
        refine ⟨118488204271413081890766481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157984272361884109187688641 118488204271413081890766481)
        ·
          refine ⟨88866153203559811418074861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118488204271413081890766481 88866153203559811418074861)
          ·
            refine ⟨33324807451334929281778073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88866153203559811418074861 33324807451334929281778073)
            ·
              refine ⟨24993605588501196961333555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33324807451334929281778073 24993605588501196961333555)
              ·
                refine ⟨37490408382751795442000333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24993605588501196961333555 37490408382751795442000333)
                ·
                  refine ⟨14058903143531923290750125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37490408382751795442000333 14058903143531923290750125)
                  ·
                    refine ⟨5272088678824471234031297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14058903143531923290750125 5272088678824471234031297)
                    ·
                      refine ⟨3954066509118353425523473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272088678824471234031297 3954066509118353425523473)
                      ·
                        rfl

theorem cell23_7700517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_7700517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700517 prefixEnd_7700517 := by exact prefixLift 7700517
  have htrace : WordTrace (prefixWord ++ tailWord_7700517) baseStart_7700517 baseEnd_7700517 := by
    simpa [prefixWord, tailWord_7700517, baseEnd_7700517] using wordTrace_append hprefix tailTrace_7700517
  have hstable : (prefixWord ++ tailWord_7700517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700517).length < 2 ^ (prefixWord ++ tailWord_7700517).sum := by decide
  have hdescent : baseEnd_7700517 < baseStart_7700517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700580 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_7700580 : Nat := 118140960795 + 7700580 * 2 ^ 59
def prefixEnd_7700580 : Nat := 4983230072969 + 3 ^ 40 * 7700580 * 2
def baseEnd_7700580 : Nat := 3954098858399586679035683

theorem tailTrace_7700580 : CollatzResearch.WordTrace tailWord_7700580 prefixEnd_7700580 3954098858399586679035683 := by
  unfold tailWord_7700580
  simp only [CollatzResearch.WordTrace]
  refine ⟨140431613221060644602161597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187242150961414192802882129 140431613221060644602161597)
  ·
    refine ⟨52661854957897741725810599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140431613221060644602161597 52661854957897741725810599)
    ·
      refine ⟨78992782436846612588715899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52661854957897741725810599 78992782436846612588715899)
      ·
        refine ⟨118489173655269918883073849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78992782436846612588715899 118489173655269918883073849)
        ·
          refine ⟨88866880241452439162305387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118489173655269918883073849 88866880241452439162305387)
          ·
            refine ⟨133300320362178658743458081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88866880241452439162305387 133300320362178658743458081)
            ·
              refine ⟨99975240271633994057593561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133300320362178658743458081 99975240271633994057593561)
              ·
                refine ⟨74981430203725495543195171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99975240271633994057593561 74981430203725495543195171)
                ·
                  refine ⟨112472145305588243314792757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74981430203725495543195171 112472145305588243314792757)
                  ·
                    refine ⟨10544263622398897810761821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112472145305588243314792757 10544263622398897810761821)
                    ·
                      refine ⟨3954098858399586679035683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10544263622398897810761821 3954098858399586679035683)
                      ·
                        rfl

theorem cell23_7700580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_7700580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700580 prefixEnd_7700580 := by exact prefixLift 7700580
  have htrace : WordTrace (prefixWord ++ tailWord_7700580) baseStart_7700580 baseEnd_7700580 := by
    simpa [prefixWord, tailWord_7700580, baseEnd_7700580] using wordTrace_append hprefix tailTrace_7700580
  have hstable : (prefixWord ++ tailWord_7700580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700580).length < 2 ^ (prefixWord ++ tailWord_7700580).sum := by decide
  have hdescent : baseEnd_7700580 < baseStart_7700580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700603 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 8]
def baseStart_7700603 : Nat := 118140960795 + 7700603 * 2 ^ 59
def prefixEnd_7700603 : Nat := 4983230072969 + 3 ^ 40 * 7700603 * 2
def baseEnd_7700603 : Nat := 3954110668454640089048077

theorem tailTrace_7700603 : CollatzResearch.WordTrace tailWord_7700603 prefixEnd_7700603 3954110668454640089048077 := by
  unfold tailWord_7700603
  simp only [CollatzResearch.WordTrace]
  refine ⟨280864065321037964132410463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187242710214025309421606975 280864065321037964132410463)
  ·
    refine ⟨421296097981556946198615695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280864065321037964132410463 421296097981556946198615695)
    ·
      refine ⟨631944146972335419297923543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421296097981556946198615695 631944146972335419297923543)
      ·
        refine ⟨947916220458503128946885315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631944146972335419297923543 947916220458503128946885315)
        ·
          refine ⟨1421874330687754693420327973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947916220458503128946885315 1421874330687754693420327973)
          ·
            refine ⟨266601437003954005016311495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1421874330687754693420327973 266601437003954005016311495)
            ·
              refine ⟨399902155505931007524467243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266601437003954005016311495 399902155505931007524467243)
              ·
                refine ⟨599853233258896511286700865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399902155505931007524467243 599853233258896511286700865)
                ·
                  refine ⟨449889924944172383465025649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599853233258896511286700865 449889924944172383465025649)
                  ·
                    refine ⟨337417443708129287598769237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 449889924944172383465025649 337417443708129287598769237)
                    ·
                      refine ⟨3954110668454640089048077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 337417443708129287598769237 3954110668454640089048077)
                      ·
                        rfl

theorem cell23_7700603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_7700603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700603 prefixEnd_7700603 := by exact prefixLift 7700603
  have htrace : WordTrace (prefixWord ++ tailWord_7700603) baseStart_7700603 baseEnd_7700603 := by
    simpa [prefixWord, tailWord_7700603, baseEnd_7700603] using wordTrace_append hprefix tailTrace_7700603
  have hstable : (prefixWord ++ tailWord_7700603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700603).length < 2 ^ (prefixWord ++ tailWord_7700603).sum := by decide
  have hdescent : baseEnd_7700603 < baseStart_7700603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700604 : List Nat := [2, 2, 2, 1, 1, 5, 3, 2, 5]
def baseStart_7700604 : Nat := 118140960795 + 7700604 * 2 ^ 59
def prefixEnd_7700604 : Nat := 4983230072969 + 3 ^ 40 * 7700604 * 2
def baseEnd_7700604 : Nat := 439345686881699398348397

theorem tailTrace_7700604 : CollatzResearch.WordTrace tailWord_7700604 prefixEnd_7700604 439345686881699398348397 := by
  unfold tailWord_7700604
  simp only [CollatzResearch.WordTrace]
  refine ⟨140432050897017170651598433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187242734529356227535464577 140432050897017170651598433)
  ·
    refine ⟨105324038172762877988698825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140432050897017170651598433 105324038172762877988698825)
    ·
      refine ⟨78993028629572158491524119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105324038172762877988698825 78993028629572158491524119)
      ·
        refine ⟨118489542944358237737286179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78993028629572158491524119 118489542944358237737286179)
        ·
          refine ⟨177734314416537356605929269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118489542944358237737286179 177734314416537356605929269)
          ·
            refine ⟨16662591976550377181805869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177734314416537356605929269 16662591976550377181805869)
            ·
              refine ⟨6248471991206391443177201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16662591976550377181805869 6248471991206391443177201)
              ·
                refine ⟨4686353993404793582382901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6248471991206391443177201 4686353993404793582382901)
                ·
                  refine ⟨439345686881699398348397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4686353993404793582382901 439345686881699398348397)
                  ·
                    rfl

theorem cell23_7700604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_7700604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700604 prefixEnd_7700604 := by exact prefixLift 7700604
  have htrace : WordTrace (prefixWord ++ tailWord_7700604) baseStart_7700604 baseEnd_7700604 := by
    simpa [prefixWord, tailWord_7700604, baseEnd_7700604] using wordTrace_append hprefix tailTrace_7700604
  have hstable : (prefixWord ++ tailWord_7700604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700604).length < 2 ^ (prefixWord ++ tailWord_7700604).sum := by decide
  have hdescent : baseEnd_7700604 < baseStart_7700604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700634 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_7700634 : Nat := 118140960795 + 7700634 * 2 ^ 59
def prefixEnd_7700634 : Nat := 4983230072969 + 3 ^ 40 * 7700634 * 2
def baseEnd_7700634 : Nat := 1318042195451643155920145

theorem tailTrace_7700634 : CollatzResearch.WordTrace tailWord_7700634 prefixEnd_7700634 1318042195451643155920145 := by
  unfold tailWord_7700634
  simp only [CollatzResearch.WordTrace]
  refine ⟨70216298995981414106697239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187243463989283770951192637 70216298995981414106697239)
  ·
    refine ⟨105324448493972121160045859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70216298995981414106697239 105324448493972121160045859)
    ·
      refine ⟨157986672740958181740068789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105324448493972121160045859 157986672740958181740068789)
      ·
        refine ⟨14811250569464829538131449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157986672740958181740068789 14811250569464829538131449)
        ·
          refine ⟨11108437927098622153598587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14811250569464829538131449 11108437927098622153598587)
          ·
            refine ⟨16662656890647933230397881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11108437927098622153598587 16662656890647933230397881)
            ·
              refine ⟨12496992667985949922798411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16662656890647933230397881 12496992667985949922798411)
              ·
                refine ⟨18745489001978924884197617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12496992667985949922798411 18745489001978924884197617)
                ·
                  refine ⟨14059116751484193663148213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18745489001978924884197617 14059116751484193663148213)
                  ·
                    refine ⟨1318042195451643155920145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14059116751484193663148213 1318042195451643155920145)
                    ·
                      rfl

theorem cell23_7700634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_7700634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700634 prefixEnd_7700634 := by exact prefixLift 7700634
  have htrace : WordTrace (prefixWord ++ tailWord_7700634) baseStart_7700634 baseEnd_7700634 := by
    simpa [prefixWord, tailWord_7700634, baseEnd_7700634] using wordTrace_append hprefix tailTrace_7700634
  have hstable : (prefixWord ++ tailWord_7700634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700634).length < 2 ^ (prefixWord ++ tailWord_7700634).sum := by decide
  have hdescent : baseEnd_7700634 < baseStart_7700634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700637 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_7700637 : Nat := 118140960795 + 7700637 * 2 ^ 59
def prefixEnd_7700637 : Nat := 4983230072969 + 3 ^ 40 * 7700637 * 2
def baseEnd_7700637 : Nat := 3954128126796892956022921

theorem tailTrace_7700637 : CollatzResearch.WordTrace tailWord_7700637 prefixEnd_7700637 3954128126796892956022921 := by
  unfold tailWord_7700637
  simp only [CollatzResearch.WordTrace]
  refine ⟨280865305402914787939148165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187243536935276525292765443 280865305402914787939148165)
  ·
    refine ⟨52662244763046522738590281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280865305402914787939148165 52662244763046522738590281)
    ·
      refine ⟨39496683572284892053942711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52662244763046522738590281 39496683572284892053942711)
      ·
        refine ⟨59245025358427338080914067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39496683572284892053942711 59245025358427338080914067)
        ·
          refine ⟨88867538037641007121371101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59245025358427338080914067 88867538037641007121371101)
          ·
            refine ⟨33325326764115377670514163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88867538037641007121371101 33325326764115377670514163)
            ·
              refine ⟨49987990146173066505771245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33325326764115377670514163 49987990146173066505771245)
              ·
                refine ⟨18745496304814899939664217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49987990146173066505771245 18745496304814899939664217)
                ·
                  refine ⟨14059122228611174954748163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18745496304814899939664217 14059122228611174954748163)
                  ·
                    refine ⟨21088683342916762432122245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14059122228611174954748163 21088683342916762432122245)
                    ·
                      refine ⟨3954128126796892956022921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21088683342916762432122245 3954128126796892956022921)
                      ·
                        rfl

theorem cell23_7700637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_7700637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700637 prefixEnd_7700637 := by exact prefixLift 7700637
  have htrace : WordTrace (prefixWord ++ tailWord_7700637) baseStart_7700637 baseEnd_7700637 := by
    simpa [prefixWord, tailWord_7700637, baseEnd_7700637] using wordTrace_append hprefix tailTrace_7700637
  have hstable : (prefixWord ++ tailWord_7700637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700637).length < 2 ^ (prefixWord ++ tailWord_7700637).sum := by decide
  have hdescent : baseEnd_7700637 < baseStart_7700637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700664 : List Nat := [2, 1, 2, 1, 2, 1, 5, 4, 1, 4]
def baseStart_7700664 : Nat := 118140960795 + 7700664 * 2 ^ 59
def prefixEnd_7700664 : Nat := 4983230072969 + 3 ^ 40 * 7700664 * 2
def baseEnd_7700664 : Nat := 1318047330258188116795099

theorem tailTrace_7700664 : CollatzResearch.WordTrace tailWord_7700664 prefixEnd_7700664 1318047330258188116795099 := by
  unfold tailWord_7700664
  simp only [CollatzResearch.WordTrace]
  refine ⟨140433145086908485775190523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187244193449211314366920697 140433145086908485775190523)
  ·
    refine ⟨210649717630362728662785785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140433145086908485775190523 210649717630362728662785785)
    ·
      refine ⟨157987288222772046497089339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210649717630362728662785785 157987288222772046497089339)
      ·
        refine ⟨236980932334158069745634009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157987288222772046497089339 236980932334158069745634009)
        ·
          refine ⟨177735699250618552309225507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236980932334158069745634009 177735699250618552309225507)
          ·
            refine ⟨266603548875927828463838261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177735699250618552309225507 266603548875927828463838261)
            ·
              refine ⟨24994082707118233918484837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266603548875927828463838261 24994082707118233918484837)
              ·
                refine ⟨4686390507584668859715907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24994082707118233918484837 4686390507584668859715907)
                ·
                  refine ⟨7029585761377003289573861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686390507584668859715907 7029585761377003289573861)
                  ·
                    refine ⟨1318047330258188116795099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7029585761377003289573861 1318047330258188116795099)
                    ·
                      rfl

theorem cell23_7700664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_7700664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700664 prefixEnd_7700664 := by exact prefixLift 7700664
  have htrace : WordTrace (prefixWord ++ tailWord_7700664) baseStart_7700664 baseEnd_7700664 := by
    simpa [prefixWord, tailWord_7700664, baseEnd_7700664] using wordTrace_append hprefix tailTrace_7700664
  have hstable : (prefixWord ++ tailWord_7700664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700664).length < 2 ^ (prefixWord ++ tailWord_7700664).sum := by decide
  have hdescent : baseEnd_7700664 < baseStart_7700664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700714 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_7700714 : Nat := 118140960795 + 7700714 * 2 ^ 59
def prefixEnd_7700714 : Nat := 4983230072969 + 3 ^ 40 * 7700714 * 2
def baseEnd_7700714 : Nat := 3954167664807289154760067

theorem tailTrace_7700714 : CollatzResearch.WordTrace tailWord_7700714 prefixEnd_7700714 3954167664807289154760067 := by
  unfold tailWord_7700714
  simp only [CollatzResearch.WordTrace]
  refine ⟨70217028455908957522425299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187245409215757220059800797 70217028455908957522425299)
  ·
    refine ⟨105325542683863436283637949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70217028455908957522425299 105325542683863436283637949)
    ·
      refine ⟨39497078506448788606364231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105325542683863436283637949 39497078506448788606364231)
      ·
        refine ⟨59245617759673182909546347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39497078506448788606364231 59245617759673182909546347)
        ·
          refine ⟨88868426639509774364319521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59245617759673182909546347 88868426639509774364319521)
          ·
            refine ⟨66651319979632330773239641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88868426639509774364319521 66651319979632330773239641)
            ·
              refine ⟨49988489984724248079929731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66651319979632330773239641 49988489984724248079929731)
              ·
                refine ⟨74982734977086372119894597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49988489984724248079929731 74982734977086372119894597)
                ·
                  refine ⟨14059262808203694772480237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74982734977086372119894597 14059262808203694772480237)
                  ·
                    refine ⟨5272223553076385539680089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14059262808203694772480237 5272223553076385539680089)
                    ·
                      refine ⟨3954167664807289154760067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272223553076385539680089 3954167664807289154760067)
                      ·
                        rfl

theorem cell23_7700714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_7700714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700714 prefixEnd_7700714 := by exact prefixLift 7700714
  have htrace : WordTrace (prefixWord ++ tailWord_7700714) baseStart_7700714 baseEnd_7700714 := by
    simpa [prefixWord, tailWord_7700714, baseEnd_7700714] using wordTrace_append hprefix tailTrace_7700714
  have hstable : (prefixWord ++ tailWord_7700714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700714).length < 2 ^ (prefixWord ++ tailWord_7700714).sum := by decide
  have hdescent : baseEnd_7700714 < baseStart_7700714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700720 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 3, 6]
def baseStart_7700720 : Nat := 118140960795 + 7700720 * 2 ^ 59
def prefixEnd_7700720 : Nat := 4983230072969 + 3 ^ 40 * 7700720 * 2
def baseEnd_7700720 : Nat := 1318056915230405377095013

theorem tailTrace_7700720 : CollatzResearch.WordTrace tailWord_7700720 prefixEnd_7700720 1318056915230405377095013 := by
  unfold tailWord_7700720
  simp only [CollatzResearch.WordTrace]
  refine ⟨140434166330807046557209807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187245555107742728742946409 140434166330807046557209807)
  ·
    refine ⟨210651249496210569835814711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140434166330807046557209807 210651249496210569835814711)
    ·
      refine ⟨315976874244315854753722067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210651249496210569835814711 315976874244315854753722067)
      ·
        refine ⟨473965311366473782130583101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315976874244315854753722067 473965311366473782130583101)
        ·
          refine ⟨177736991762427668298968663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473965311366473782130583101 177736991762427668298968663)
          ·
            refine ⟨266605487643641502448452995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177736991762427668298968663 266605487643641502448452995)
            ·
              refine ⟨399908231465462253672679493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266605487643641502448452995 399908231465462253672679493)
              ·
                refine ⟨74982793399774172563627405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399908231465462253672679493 74982793399774172563627405)
                ·
                  refine ⟨28118547524915314711360277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74982793399774172563627405 28118547524915314711360277)
                  ·
                    refine ⟨1318056915230405377095013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28118547524915314711360277 1318056915230405377095013)
                    ·
                      rfl

theorem cell23_7700720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_7700720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700720 prefixEnd_7700720 := by exact prefixLift 7700720
  have htrace : WordTrace (prefixWord ++ tailWord_7700720) baseStart_7700720 baseEnd_7700720 := by
    simpa [prefixWord, tailWord_7700720, baseEnd_7700720] using wordTrace_append hprefix tailTrace_7700720
  have hstable : (prefixWord ++ tailWord_7700720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700720).length < 2 ^ (prefixWord ++ tailWord_7700720).sum := by decide
  have hdescent : baseEnd_7700720 < baseStart_7700720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700721 : List Nat := [1, 2, 2, 2, 2, 1, 4, 4, 1, 1, 3]
def baseStart_7700721 : Nat := 118140960795 + 7700721 * 2 ^ 59
def prefixEnd_7700721 : Nat := 4983230072969 + 3 ^ 40 * 7700721 * 2
def baseEnd_7700721 : Nat := 3954171259171870627372535

theorem tailTrace_7700721 : CollatzResearch.WordTrace tailWord_7700721 prefixEnd_7700721 3954171259171870627372535 := by
  unfold tailWord_7700721
  simp only [CollatzResearch.WordTrace]
  refine ⟨280868369134610470285206017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187245579423073646856804011 280868369134610470285206017)
  ·
    refine ⟨210651276850957852713904513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280868369134610470285206017 210651276850957852713904513)
    ·
      refine ⟨157988457638218389535428385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210651276850957852713904513 157988457638218389535428385)
      ·
        refine ⟨118491343228663792151571289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157988457638218389535428385 118491343228663792151571289)
        ·
          refine ⟨88868507421497844113678467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118491343228663792151571289 88868507421497844113678467)
          ·
            refine ⟨133302761132246766170517701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88868507421497844113678467 133302761132246766170517701)
            ·
              refine ⟨24994267712296268656972069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133302761132246766170517701 24994267712296268656972069)
              ·
                refine ⟨4686425196055550373182263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24994267712296268656972069 4686425196055550373182263)
                ·
                  refine ⟨7029637794083325559773395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686425196055550373182263 7029637794083325559773395)
                  ·
                    refine ⟨10544456691124988339660093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7029637794083325559773395 10544456691124988339660093)
                    ·
                      refine ⟨3954171259171870627372535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10544456691124988339660093 3954171259171870627372535)
                      ·
                        rfl

theorem cell23_7700721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_7700721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700721 prefixEnd_7700721 := by exact prefixLift 7700721
  have htrace : WordTrace (prefixWord ++ tailWord_7700721) baseStart_7700721 baseEnd_7700721 := by
    simpa [prefixWord, tailWord_7700721, baseEnd_7700721] using wordTrace_append hprefix tailTrace_7700721
  have hstable : (prefixWord ++ tailWord_7700721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700721).length < 2 ^ (prefixWord ++ tailWord_7700721).sum := by decide
  have hdescent : baseEnd_7700721 < baseStart_7700721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700727 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 4, 6, 2]
def baseStart_7700727 : Nat := 118140960795 + 7700727 * 2 ^ 59
def prefixEnd_7700727 : Nat := 4983230072969 + 3 ^ 40 * 7700727 * 2
def baseEnd_7700727 : Nat := 3954174340055797603897507

theorem tailTrace_7700727 : CollatzResearch.WordTrace tailWord_7700727 prefixEnd_7700727 3954174340055797603897507 := by
  unfold tailWord_7700727
  simp only [CollatzResearch.WordTrace]
  refine ⟨280868587972588733309924435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187245725315059155539949623 280868587972588733309924435)
  ·
    refine ⟨421302881958883099964886653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280868587972588733309924435 421302881958883099964886653)
    ·
      refine ⟨157988580734581162486832495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421302881958883099964886653 157988580734581162486832495)
      ·
        refine ⟨236982871101871743730248743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157988580734581162486832495 236982871101871743730248743)
        ·
          refine ⟨355474306652807615595373115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236982871101871743730248743 355474306652807615595373115)
          ·
            refine ⟨533211459979211423393059673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355474306652807615595373115 533211459979211423393059673)
            ·
              refine ⟨399908594984408567544794755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533211459979211423393059673 399908594984408567544794755)
              ·
                refine ⟨599862892476612851317192133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399908594984408567544794755 599862892476612851317192133)
                ·
                  refine ⟨112474292339364909621973525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599862892476612851317192133 112474292339364909621973525)
                  ·
                    refine ⟨5272232453407730138530009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112474292339364909621973525 5272232453407730138530009)
                    ·
                      refine ⟨3954174340055797603897507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272232453407730138530009 3954174340055797603897507)
                      ·
                        rfl

theorem cell23_7700727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_7700727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700727 prefixEnd_7700727 := by exact prefixLift 7700727
  have htrace : WordTrace (prefixWord ++ tailWord_7700727) baseStart_7700727 baseEnd_7700727 := by
    simpa [prefixWord, tailWord_7700727, baseEnd_7700727] using wordTrace_append hprefix tailTrace_7700727
  have hstable : (prefixWord ++ tailWord_7700727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700727).length < 2 ^ (prefixWord ++ tailWord_7700727).sum := by decide
  have hdescent : baseEnd_7700727 < baseStart_7700727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700744 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_7700744 : Nat := 118140960795 + 7700744 * 2 ^ 59
def prefixEnd_7700744 : Nat := 4983230072969 + 3 ^ 40 * 7700744 * 2
def baseEnd_7700744 : Nat := 3954183069226924037384929

theorem tailTrace_7700744 : CollatzResearch.WordTrace tailWord_7700744 prefixEnd_7700744 3954183069226924037384929 := by
  unfold tailWord_7700744
  simp only [CollatzResearch.WordTrace]
  refine ⟨140434604006763572606646643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187246138675684763475528857 140434604006763572606646643)
  ·
    refine ⟨210651906010145358909969965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140434604006763572606646643 210651906010145358909969965)
    ·
      refine ⟨78994464753804509591238737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210651906010145358909969965 78994464753804509591238737)
      ·
        refine ⟨59245848565353382193429053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78994464753804509591238737 59245848565353382193429053)
        ·
          refine ⟨22217193212007518322535895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59245848565353382193429053 22217193212007518322535895)
          ·
            refine ⟨33325789818011277483803843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22217193212007518322535895 33325789818011277483803843)
            ·
              refine ⟨49988684727016916225705765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33325789818011277483803843 49988684727016916225705765)
              ·
                refine ⟨9372878386315671792319831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49988684727016916225705765 9372878386315671792319831)
                ·
                  refine ⟨14059317579473507688479747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9372878386315671792319831 14059317579473507688479747)
                  ·
                    refine ⟨21088976369210261532719621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14059317579473507688479747 21088976369210261532719621)
                    ·
                      refine ⟨3954183069226924037384929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21088976369210261532719621 3954183069226924037384929)
                      ·
                        rfl

theorem cell23_7700744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_7700744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700744 prefixEnd_7700744 := by exact prefixLift 7700744
  have htrace : WordTrace (prefixWord ++ tailWord_7700744) baseStart_7700744 baseEnd_7700744 := by
    simpa [prefixWord, tailWord_7700744, baseEnd_7700744] using wordTrace_append hprefix tailTrace_7700744
  have hstable : (prefixWord ++ tailWord_7700744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700744).length < 2 ^ (prefixWord ++ tailWord_7700744).sum := by decide
  have hdescent : baseEnd_7700744 < baseStart_7700744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700757 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_7700757 : Nat := 118140960795 + 7700757 * 2 ^ 59
def prefixEnd_7700757 : Nat := 4983230072969 + 3 ^ 40 * 7700757 * 2
def baseEnd_7700757 : Nat := 3954189744475432486522369

theorem tailTrace_7700757 : CollatzResearch.WordTrace tailWord_7700757 prefixEnd_7700757 3954189744475432486522369 := by
  unfold tailWord_7700757
  simp only [CollatzResearch.WordTrace]
  refine ⟨280869682162480048433516525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187246454774986698955677683 280869682162480048433516525)
  ·
    refine ⟨105326130810930018162568697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280869682162480048433516525 105326130810930018162568697)
    ·
      refine ⟨78994598108197513621926523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105326130810930018162568697 78994598108197513621926523)
      ·
        refine ⟨118491897162296270432889785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78994598108197513621926523 118491897162296270432889785)
        ·
          refine ⟨88868922871722202824667339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118491897162296270432889785 88868922871722202824667339)
          ·
            refine ⟨133303384307583304237001009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88868922871722202824667339 133303384307583304237001009)
            ·
              refine ⟨99977538230687478177750757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133303384307583304237001009 99977538230687478177750757)
              ·
                refine ⟨18745788418253902158328267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99977538230687478177750757 18745788418253902158328267)
                ·
                  refine ⟨28118682627380853237492401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18745788418253902158328267 28118682627380853237492401)
                  ·
                    refine ⟨21089011970535639928119301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28118682627380853237492401 21089011970535639928119301)
                    ·
                      refine ⟨3954189744475432486522369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21089011970535639928119301 3954189744475432486522369)
                      ·
                        rfl

theorem cell23_7700757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_7700757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700757 prefixEnd_7700757 := by exact prefixLift 7700757
  have htrace : WordTrace (prefixWord ++ tailWord_7700757) baseStart_7700757 baseEnd_7700757 := by
    simpa [prefixWord, tailWord_7700757, baseEnd_7700757] using wordTrace_append hprefix tailTrace_7700757
  have hstable : (prefixWord ++ tailWord_7700757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700757).length < 2 ^ (prefixWord ++ tailWord_7700757).sum := by decide
  have hdescent : baseEnd_7700757 < baseStart_7700757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700767 : List Nat := [1, 1, 2, 4, 3, 3, 9]
def baseStart_7700767 : Nat := 118140960795 + 7700767 * 2 ^ 59
def prefixEnd_7700767 : Nat := 4983230072969 + 3 ^ 40 * 7700767 * 2
def baseEnd_7700767 : Nat := 48817220731876264782683

theorem tailTrace_7700767 : CollatzResearch.WordTrace tailWord_7700767 prefixEnd_7700767 48817220731876264782683 := by
  unfold tailWord_7700767
  simp only [CollatzResearch.WordTrace]
  refine ⟨280870046892443820141380555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187246697928295880094253703 280870046892443820141380555)
  ·
    refine ⟨421305070338665730212070833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280870046892443820141380555 421305070338665730212070833)
    ·
      refine ⟨315978802753999297659053125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421305070338665730212070833 315978802753999297659053125)
      ·
        refine ⟨59246025516374868311072461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315978802753999297659053125 59246025516374868311072461)
        ·
          refine ⟨22217259568640575616652173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59246025516374868311072461 22217259568640575616652173)
          ·
            refine ⟨8331472338240215856244565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22217259568640575616652173 8331472338240215856244565)
            ·
              refine ⟨48817220731876264782683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8331472338240215856244565 48817220731876264782683)
              ·
                rfl

theorem cell23_7700767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 9].length) (baseStart_7700767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700767 prefixEnd_7700767 := by exact prefixLift 7700767
  have htrace : WordTrace (prefixWord ++ tailWord_7700767) baseStart_7700767 baseEnd_7700767 := by
    simpa [prefixWord, tailWord_7700767, baseEnd_7700767] using wordTrace_append hprefix tailTrace_7700767
  have hstable : (prefixWord ++ tailWord_7700767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700767).length < 2 ^ (prefixWord ++ tailWord_7700767).sum := by decide
  have hdescent : baseEnd_7700767 < baseStart_7700767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700788 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_7700788 : Nat := 118140960795 + 7700788 * 2 ^ 59
def prefixEnd_7700788 : Nat := 4983230072969 + 3 ^ 40 * 7700788 * 2
def baseEnd_7700788 : Nat := 1318068554125240621744909

theorem tailTrace_7700788 : CollatzResearch.WordTrace tailWord_7700788 prefixEnd_7700788 1318068554125240621744909 := by
  unfold tailWord_7700788
  simp only [CollatzResearch.WordTrace]
  refine ⟨140435406412683870363947509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187247208550245160485263345 140435406412683870363947509)
  ·
    refine ⟨13165819351189112846620079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140435406412683870363947509 13165819351189112846620079)
    ·
      refine ⟨19748729026783669269930119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13165819351189112846620079 19748729026783669269930119)
      ·
        refine ⟨29623093540175503904895179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19748729026783669269930119 29623093540175503904895179)
        ·
          refine ⟨44434640310263255857342769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29623093540175503904895179 44434640310263255857342769)
          ·
            refine ⟨33325980232697441893007077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44434640310263255857342769 33325980232697441893007077)
            ·
              refine ⟨6248621293630770354938827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33325980232697441893007077 6248621293630770354938827)
              ·
                refine ⟨9372931940446155532408241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6248621293630770354938827 9372931940446155532408241)
                ·
                  refine ⟨7029698955334616649306181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9372931940446155532408241 7029698955334616649306181)
                  ·
                    refine ⟨1318068554125240621744909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7029698955334616649306181 1318068554125240621744909)
                    ·
                      rfl

theorem cell23_7700788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_7700788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700788 prefixEnd_7700788 := by exact prefixLift 7700788
  have htrace : WordTrace (prefixWord ++ tailWord_7700788) baseStart_7700788 baseEnd_7700788 := by
    simpa [prefixWord, tailWord_7700788, baseEnd_7700788] using wordTrace_append hprefix tailTrace_7700788
  have hstable : (prefixWord ++ tailWord_7700788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700788).length < 2 ^ (prefixWord ++ tailWord_7700788).sum := by decide
  have hdescent : baseEnd_7700788 < baseStart_7700788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700798 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_7700798 : Nat := 118140960795 + 7700798 * 2 ^ 59
def prefixEnd_7700798 : Nat := 4983230072969 + 3 ^ 40 * 7700798 * 2
def baseEnd_7700798 : Nat := 3954210797182266826109681

theorem tailTrace_7700798 : CollatzResearch.WordTrace tailWord_7700798 prefixEnd_7700798 3954210797182266826109681 := by
  unfold tailWord_7700798
  simp only [CollatzResearch.WordTrace]
  refine ⟨35108897194416439054469881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187247451703554341623839365 35108897194416439054469881)
  ·
    refine ⟨26331672895812329290852411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35108897194416439054469881 26331672895812329290852411)
    ·
      refine ⟨39497509343718493936278617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26331672895812329290852411 39497509343718493936278617)
      ·
        refine ⟨29623132007788870452208963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39497509343718493936278617 29623132007788870452208963)
        ·
          refine ⟨44434698011683305678313445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29623132007788870452208963 44434698011683305678313445)
          ·
            refine ⟨8331505877190619814683771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44434698011683305678313445 8331505877190619814683771)
            ·
              refine ⟨12497258815785929722025657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8331505877190619814683771 12497258815785929722025657)
              ·
                refine ⟨9372944111839447291519243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12497258815785929722025657 9372944111839447291519243)
                ·
                  refine ⟨14059416167759170937278865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9372944111839447291519243 14059416167759170937278865)
                  ·
                    refine ⟨10544562125819378202959149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14059416167759170937278865 10544562125819378202959149)
                    ·
                      refine ⟨3954210797182266826109681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10544562125819378202959149 3954210797182266826109681)
                      ·
                        rfl

theorem cell23_7700798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_7700798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700798 prefixEnd_7700798 := by exact prefixLift 7700798
  have htrace : WordTrace (prefixWord ++ tailWord_7700798) baseStart_7700798 baseEnd_7700798 := by
    simpa [prefixWord, tailWord_7700798, baseEnd_7700798] using wordTrace_append hprefix tailTrace_7700798
  have hstable : (prefixWord ++ tailWord_7700798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700798).length < 2 ^ (prefixWord ++ tailWord_7700798).sum := by decide
  have hdescent : baseEnd_7700798 < baseStart_7700798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700834 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_7700834 : Nat := 118140960795 + 7700834 * 2 ^ 59
def prefixEnd_7700834 : Nat := 4983230072969 + 3 ^ 40 * 7700834 * 2
def baseEnd_7700834 : Nat := 3954229282485828685259515

theorem tailTrace_7700834 : CollatzResearch.WordTrace tailWord_7700834 prefixEnd_7700834 3954229282485828685259515 := by
  unfold tailWord_7700834
  simp only [CollatzResearch.WordTrace]
  refine ⟨70218122645800272646017389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187248327055467393722713037 70218122645800272646017389)
  ·
    refine ⟨26331795992175102242256521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70218122645800272646017389 26331795992175102242256521)
    ·
      refine ⟨19748846994131326681692391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26331795992175102242256521 19748846994131326681692391)
      ·
        refine ⟨29623270491196990022538587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19748846994131326681692391 29623270491196990022538587)
        ·
          refine ⟨44434905736795485033807881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29623270491196990022538587 44434905736795485033807881)
          ·
            refine ⟨33326179302596613775355911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44434905736795485033807881 33326179302596613775355911)
            ·
              refine ⟨49989268953894920663033867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33326179302596613775355911 49989268953894920663033867)
              ·
                refine ⟨74983903430842380994550801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49989268953894920663033867 74983903430842380994550801)
                ·
                  refine ⟨56237927573131785745913101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74983903430842380994550801 56237927573131785745913101)
                  ·
                    refine ⟨21089222839924419654717413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56237927573131785745913101 21089222839924419654717413)
                    ·
                      refine ⟨3954229282485828685259515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21089222839924419654717413 3954229282485828685259515)
                      ·
                        rfl

theorem cell23_7700834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_7700834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700834 prefixEnd_7700834 := by exact prefixLift 7700834
  have htrace : WordTrace (prefixWord ++ tailWord_7700834) baseStart_7700834 baseEnd_7700834 := by
    simpa [prefixWord, tailWord_7700834, baseEnd_7700834] using wordTrace_append hprefix tailTrace_7700834
  have hstable : (prefixWord ++ tailWord_7700834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700834).length < 2 ^ (prefixWord ++ tailWord_7700834).sum := by decide
  have hdescent : baseEnd_7700834 < baseStart_7700834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700844 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_7700844 : Nat := 118140960795 + 7700844 * 2 ^ 59
def prefixEnd_7700844 : Nat := 4983230072969 + 3 ^ 40 * 7700844 * 2
def baseEnd_7700844 : Nat := 1318078139097457882044823

theorem tailTrace_7700844 : CollatzResearch.WordTrace tailWord_7700844 prefixEnd_7700844 1318078139097457882044823 := by
  unfold tailWord_7700844
  simp only [CollatzResearch.WordTrace]
  refine ⟨140436427656582431145966793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187248570208776574861289057 140436427656582431145966793)
  ·
    refine ⟨105327320742436823359475095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140436427656582431145966793 105327320742436823359475095)
    ·
      refine ⟨157990981113655235039212643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105327320742436823359475095 157990981113655235039212643)
      ·
        refine ⟨236986471670482852558818965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157990981113655235039212643 236986471670482852558818965)
        ·
          refine ⟨11108740859553883713694639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236986471670482852558818965 11108740859553883713694639)
          ·
            refine ⟨16663111289330825570541959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11108740859553883713694639 16663111289330825570541959)
            ·
              refine ⟨24994666933996238355812939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16663111289330825570541959 24994666933996238355812939)
              ·
                refine ⟨37492000400994357533719409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24994666933996238355812939 37492000400994357533719409)
                ·
                  refine ⟨28119000300745768150289557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37492000400994357533719409 28119000300745768150289557)
                  ·
                    refine ⟨1318078139097457882044823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28119000300745768150289557 1318078139097457882044823)
                    ·
                      rfl

theorem cell23_7700844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_7700844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700844 prefixEnd_7700844 := by exact prefixLift 7700844
  have htrace : WordTrace (prefixWord ++ tailWord_7700844) baseStart_7700844 baseEnd_7700844 := by
    simpa [prefixWord, tailWord_7700844, baseEnd_7700844] using wordTrace_append hprefix tailTrace_7700844
  have hstable : (prefixWord ++ tailWord_7700844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700844).length < 2 ^ (prefixWord ++ tailWord_7700844).sum := by decide
  have hdescent : baseEnd_7700844 < baseStart_7700844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700927 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_7700927 : Nat := 118140960795 + 7700927 * 2 ^ 59
def prefixEnd_7700927 : Nat := 4983230072969 + 3 ^ 40 * 7700927 * 2
def baseEnd_7700927 : Nat := 3954277036186696821396587

theorem tailTrace_7700927 : CollatzResearch.WordTrace tailWord_7700927 prefixEnd_7700927 3954277036186696821396587 := by
  unfold tailWord_7700927
  simp only [CollatzResearch.WordTrace]
  refine ⟨280875882571864167467205035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187250588381242778311470023 280875882571864167467205035)
  ·
    refine ⟨421313823857796251200807553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280875882571864167467205035 421313823857796251200807553)
    ·
      refine ⟨315985367893347188400605665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421313823857796251200807553 315985367893347188400605665)
      ·
        refine ⟨236989025920010391300454249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315985367893347188400605665 236989025920010391300454249)
        ·
          refine ⟨177741769440007793475340687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236989025920010391300454249 177741769440007793475340687)
          ·
            refine ⟨266612654160011690213011031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177741769440007793475340687 266612654160011690213011031)
            ·
              refine ⟨399918981240017535319516547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266612654160011690213011031 399918981240017535319516547)
              ·
                refine ⟨599878471860026302979274821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399918981240017535319516547 599878471860026302979274821)
                ·
                  refine ⟨112477213473754931808614029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599878471860026302979274821 112477213473754931808614029)
                  ·
                    refine ⟨42178955052658099428230261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112477213473754931808614029 42178955052658099428230261)
                    ·
                      refine ⟨3954277036186696821396587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42178955052658099428230261 3954277036186696821396587)
                      ·
                        rfl

theorem cell23_7700927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_7700927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700927 prefixEnd_7700927 := by exact prefixLift 7700927
  have htrace : WordTrace (prefixWord ++ tailWord_7700927) baseStart_7700927 baseEnd_7700927 := by
    simpa [prefixWord, tailWord_7700927, baseEnd_7700927] using wordTrace_append hprefix tailTrace_7700927
  have hstable : (prefixWord ++ tailWord_7700927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700927).length < 2 ^ (prefixWord ++ tailWord_7700927).sum := by decide
  have hdescent : baseEnd_7700927 < baseStart_7700927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7700937 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_7700937 : Nat := 118140960795 + 7700937 * 2 ^ 59
def prefixEnd_7700937 : Nat := 4983230072969 + 3 ^ 40 * 7700937 * 2
def baseEnd_7700937 : Nat := 3954282170993241782271541

theorem tailTrace_7700937 : CollatzResearch.WordTrace tailWord_7700937 prefixEnd_7700937 3954282170993241782271541 := by
  unfold tailWord_7700937
  simp only [CollatzResearch.WordTrace]
  refine ⟨280876247301827939175069065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187250831534551959450046043 280876247301827939175069065)
  ·
    refine ⟨210657185476370954381301799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280876247301827939175069065 210657185476370954381301799)
    ·
      refine ⟨315985778214556431571952699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210657185476370954381301799 315985778214556431571952699)
      ·
        refine ⟨473978667321834647357929049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315985778214556431571952699 473978667321834647357929049)
        ·
          refine ⟨355484000491375985518446787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473978667321834647357929049 355484000491375985518446787)
          ·
            refine ⟨533226000737063978277670181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355484000491375985518446787 533226000737063978277670181)
            ·
              refine ⟨99979875138199495927063159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 533226000737063978277670181 99979875138199495927063159)
              ·
                refine ⟨149969812707299243890594739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99979875138199495927063159 149969812707299243890594739)
                ·
                  refine ⟨224954719060948865835892109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149969812707299243890594739 224954719060948865835892109)
                  ·
                    refine ⟨84358019647855824688459541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224954719060948865835892109 84358019647855824688459541)
                    ·
                      refine ⟨3954282170993241782271541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84358019647855824688459541 3954282170993241782271541)
                      ·
                        rfl

theorem cell23_7700937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_7700937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7700937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7700937 prefixEnd_7700937 := by exact prefixLift 7700937
  have htrace : WordTrace (prefixWord ++ tailWord_7700937) baseStart_7700937 baseEnd_7700937 := by
    simpa [prefixWord, tailWord_7700937, baseEnd_7700937] using wordTrace_append hprefix tailTrace_7700937
  have hstable : (prefixWord ++ tailWord_7700937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7700937).length < 2 ^ (prefixWord ++ tailWord_7700937).sum := by decide
  have hdescent : baseEnd_7700937 < baseStart_7700937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7700937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701001 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 4, 3, 2]
def baseStart_7701001 : Nat := 118140960795 + 7701001 * 2 ^ 59
def prefixEnd_7701001 : Nat := 4983230072969 + 3 ^ 40 * 7701001 * 2
def baseEnd_7701001 : Nat := 3954315033755129531871247

theorem tailTrace_7701001 : CollatzResearch.WordTrace tailWord_7701001 prefixEnd_7701001 3954315033755129531871247 := by
  unfold tailWord_7701001
  simp only [CollatzResearch.WordTrace]
  refine ⟨280878581573596078105398857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187252387715730718736932571 280878581573596078105398857)
  ·
    refine ⟨210658936180197058579049143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280878581573596078105398857 210658936180197058579049143)
    ·
      refine ⟨315988404270295587868573715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210658936180197058579049143 315988404270295587868573715)
      ·
        refine ⟨473982606405443381802860573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315988404270295587868573715 473982606405443381802860573)
        ·
          refine ⟨177743477402041268176072715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473982606405443381802860573 177743477402041268176072715)
          ·
            refine ⟨266615216103061902264109073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177743477402041268176072715 266615216103061902264109073)
            ·
              refine ⟨199961412077296426698081805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266615216103061902264109073 199961412077296426698081805)
              ·
                refine ⟨74985529528986160011780677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199961412077296426698081805 74985529528986160011780677)
                ·
                  refine ⟨14059786786684905002208877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74985529528986160011780677 14059786786684905002208877)
                  ·
                    refine ⟨5272420045006839375828329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14059786786684905002208877 5272420045006839375828329)
                    ·
                      refine ⟨3954315033755129531871247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272420045006839375828329 3954315033755129531871247)
                      ·
                        rfl

theorem cell23_7701001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 3, 2].length) (baseStart_7701001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701001 prefixEnd_7701001 := by exact prefixLift 7701001
  have htrace : WordTrace (prefixWord ++ tailWord_7701001) baseStart_7701001 baseEnd_7701001 := by
    simpa [prefixWord, tailWord_7701001, baseEnd_7701001] using wordTrace_append hprefix tailTrace_7701001
  have hstable : (prefixWord ++ tailWord_7701001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701001).length < 2 ^ (prefixWord ++ tailWord_7701001).sum := by decide
  have hdescent : baseEnd_7701001 < baseStart_7701001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701048 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 5, 2, 2]
def baseStart_7701048 : Nat := 118140960795 + 7701048 * 2 ^ 59
def prefixEnd_7701048 : Nat := 4983230072969 + 3 ^ 40 * 7701048 * 2
def baseEnd_7701048 : Nat := 3954339167345890847983531

theorem tailTrace_7701048 : CollatzResearch.WordTrace tailWord_7701048 prefixEnd_7701048 3954339167345890847983531 := by
  unfold tailWord_7701048
  simp only [CollatzResearch.WordTrace]
  refine ⟨140440147902212902566179899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187253530536283870088239865 140440147902212902566179899)
  ·
    refine ⟨210660221853319353849269849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140440147902212902566179899 210660221853319353849269849)
    ·
      refine ⟨157995166389989515386952387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210660221853319353849269849 157995166389989515386952387)
      ·
        refine ⟨236992749584984273080428581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157995166389989515386952387 236992749584984273080428581)
        ·
          refine ⟨44436140547184551202580359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236992749584984273080428581 44436140547184551202580359)
          ·
            refine ⟨66654210820776826803870539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44436140547184551202580359 66654210820776826803870539)
            ·
              refine ⟨99981316231165240205805809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66654210820776826803870539 99981316231165240205805809)
              ·
                refine ⟨74985987173373930154354357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99981316231165240205805809 74985987173373930154354357)
                ·
                  refine ⟨7029936297503805951970721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74985987173373930154354357 7029936297503805951970721)
                  ·
                    refine ⟨5272452223127854463978041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7029936297503805951970721 5272452223127854463978041)
                    ·
                      refine ⟨3954339167345890847983531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272452223127854463978041 3954339167345890847983531)
                      ·
                        rfl

theorem cell23_7701048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_7701048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701048 prefixEnd_7701048 := by exact prefixLift 7701048
  have htrace : WordTrace (prefixWord ++ tailWord_7701048) baseStart_7701048 baseEnd_7701048 := by
    simpa [prefixWord, tailWord_7701048, baseEnd_7701048] using wordTrace_append hprefix tailTrace_7701048
  have hstable : (prefixWord ++ tailWord_7701048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701048).length < 2 ^ (prefixWord ++ tailWord_7701048).sum := by decide
  have hdescent : baseEnd_7701048 < baseStart_7701048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701098 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_7701098 : Nat := 118140960795 + 7701098 * 2 ^ 59
def prefixEnd_7701098 : Nat := 4983230072969 + 3 ^ 40 * 7701098 * 2
def baseEnd_7701098 : Nat := 3954364841378615652358301

theorem tailTrace_7701098 : CollatzResearch.WordTrace tailWord_7701098 prefixEnd_7701098 3954364841378615652358301 := by
  unfold tailWord_7701098
  simp only [CollatzResearch.WordTrace]
  refine ⟨70220529863561165917919987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187254746302829775781119965 70220529863561165917919987)
  ·
    refine ⟨105330794795341748876879981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70220529863561165917919987 105330794795341748876879981)
    ·
      refine ⟨39499048048253155828829993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105330794795341748876879981 39499048048253155828829993)
      ·
        refine ⟨29624286036189866871622495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39499048048253155828829993 29624286036189866871622495)
        ·
          refine ⟨44436429054284800307433743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29624286036189866871622495 44436429054284800307433743)
          ·
            refine ⟨66654643581427200461150615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44436429054284800307433743 66654643581427200461150615)
            ·
              refine ⟨99981965372140800691725923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66654643581427200461150615 99981965372140800691725923)
              ·
                refine ⟨149972948058211201037588885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99981965372140800691725923 149972948058211201037588885)
                ·
                  refine ⟨7029981940228650048636979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149972948058211201037588885 7029981940228650048636979)
                  ·
                    refine ⟨10544972910342975072955469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7029981940228650048636979 10544972910342975072955469)
                    ·
                      refine ⟨3954364841378615652358301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10544972910342975072955469 3954364841378615652358301)
                      ·
                        rfl

theorem cell23_7701098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_7701098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701098 prefixEnd_7701098 := by exact prefixLift 7701098
  have htrace : WordTrace (prefixWord ++ tailWord_7701098) baseStart_7701098 baseEnd_7701098 := by
    simpa [prefixWord, tailWord_7701098, baseEnd_7701098] using wordTrace_append hprefix tailTrace_7701098
  have hstable : (prefixWord ++ tailWord_7701098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701098).length < 2 ^ (prefixWord ++ tailWord_7701098).sum := by decide
  have hdescent : baseEnd_7701098 < baseStart_7701098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701121 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7701121 : Nat := 118140960795 + 7701121 * 2 ^ 59
def prefixEnd_7701121 : Nat := 4983230072969 + 3 ^ 40 * 7701121 * 2
def baseEnd_7701121 : Nat := 3954376651433669062370695

theorem tailTrace_7701121 : CollatzResearch.WordTrace tailWord_7701121 prefixEnd_7701121 3954376651433669062370695 := by
  unfold tailWord_7701121
  simp only [CollatzResearch.WordTrace]
  refine ⟨280882958333161338599767217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187255305555440892399844811 280882958333161338599767217)
  ·
    refine ⟨210662218749871003949825413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280882958333161338599767217 210662218749871003949825413)
    ·
      refine ⟨39499166015600813240592265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210662218749871003949825413 39499166015600813240592265)
      ·
        refine ⟨29624374511700609930444199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39499166015600813240592265 29624374511700609930444199)
        ·
          refine ⟨44436561767550914895666299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29624374511700609930444199 44436561767550914895666299)
          ·
            refine ⟨66654842651326372343499449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44436561767550914895666299 66654842651326372343499449)
            ·
              refine ⟨49991131988494779257624587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66654842651326372343499449 49991131988494779257624587)
              ·
                refine ⟨74986697982742168886436881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49991131988494779257624587 74986697982742168886436881)
                ·
                  refine ⟨56240023487056626664827661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74986697982742168886436881 56240023487056626664827661)
                  ·
                    refine ⟨21090008807646234999310373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56240023487056626664827661 21090008807646234999310373)
                    ·
                      refine ⟨3954376651433669062370695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21090008807646234999310373 3954376651433669062370695)
                      ·
                        rfl

theorem cell23_7701121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7701121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701121 prefixEnd_7701121 := by exact prefixLift 7701121
  have htrace : WordTrace (prefixWord ++ tailWord_7701121) baseStart_7701121 baseEnd_7701121 := by
    simpa [prefixWord, tailWord_7701121, baseEnd_7701121] using wordTrace_append hprefix tailTrace_7701121
  have hstable : (prefixWord ++ tailWord_7701121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701121).length < 2 ^ (prefixWord ++ tailWord_7701121).sum := by decide
  have hdescent : baseEnd_7701121 < baseStart_7701121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701122 : List Nat := [3, 4, 3, 1, 1, 1, 2, 8]
def baseStart_7701122 : Nat := 118140960795 + 7701122 * 2 ^ 59
def prefixEnd_7701122 : Nat := 4983230072969 + 3 ^ 40 * 7701122 * 2
def baseEnd_7701122 : Nat := 146458413515345316979933

theorem tailTrace_7701122 : CollatzResearch.WordTrace tailWord_7701122 prefixEnd_7701122 146458413515345316979933 := by
  unfold tailWord_7701122
  simp only [CollatzResearch.WordTrace]
  refine ⟨70220748701539428942638405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187255329870771810513702413 70220748701539428942638405)
  ·
    refine ⟨13166390381538642926744701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70220748701539428942638405 13166390381538642926744701)
    ·
      refine ⟨4937396393076991097529263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13166390381538642926744701 4937396393076991097529263)
      ·
        refine ⟨7406094589615486646293895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937396393076991097529263 7406094589615486646293895)
        ·
          refine ⟨11109141884423229969440843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7406094589615486646293895 11109141884423229969440843)
          ·
            refine ⟨16663712826634844954161265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109141884423229969440843 16663712826634844954161265)
            ·
              refine ⟨12497784619976133715620949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16663712826634844954161265 12497784619976133715620949)
              ·
                refine ⟨146458413515345316979933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12497784619976133715620949 146458413515345316979933)
                ·
                  rfl

theorem cell23_7701122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 8].length) (baseStart_7701122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701122 prefixEnd_7701122 := by exact prefixLift 7701122
  have htrace : WordTrace (prefixWord ++ tailWord_7701122) baseStart_7701122 baseEnd_7701122 := by
    simpa [prefixWord, tailWord_7701122, baseEnd_7701122] using wordTrace_append hprefix tailTrace_7701122
  have hstable : (prefixWord ++ tailWord_7701122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701122).length < 2 ^ (prefixWord ++ tailWord_7701122).sum := by decide
  have hdescent : baseEnd_7701122 < baseStart_7701122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701178 : List Nat := [3, 1, 1, 1, 2, 3, 3, 4, 5]
def baseStart_7701178 : Nat := 118140960795 + 7701178 * 2 ^ 59
def prefixEnd_7701178 : Nat := 4983230072969 + 3 ^ 40 * 7701178 * 2
def baseEnd_7701178 : Nat := 439378435536775037706437

theorem tailTrace_7701178 : CollatzResearch.WordTrace tailWord_7701178 prefixEnd_7701178 439378435536775037706437 := by
  unfold tailWord_7701178
  simp only [CollatzResearch.WordTrace]
  refine ⟨70221259323488709333648047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187256691529303224889728125 70221259323488709333648047)
  ·
    refine ⟨105331888985233064000472071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70221259323488709333648047 105331888985233064000472071)
    ·
      refine ⟨157997833477849596000708107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105331888985233064000472071 157997833477849596000708107)
      ·
        refine ⟨236996750216774394001062161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157997833477849596000708107 236996750216774394001062161)
        ·
          refine ⟨177747562662580795500796621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236996750216774394001062161 177747562662580795500796621)
          ·
            refine ⟨66655335998467798312798733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177747562662580795500796621 66655335998467798312798733)
            ·
              refine ⟨24995750999425424367299525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66655335998467798312798733 24995750999425424367299525)
              ·
                refine ⟨4686703312392267068868661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24995750999425424367299525 4686703312392267068868661)
                ·
                  refine ⟨439378435536775037706437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4686703312392267068868661 439378435536775037706437)
                  ·
                    rfl

theorem cell23_7701178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_7701178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701178 prefixEnd_7701178 := by exact prefixLift 7701178
  have htrace : WordTrace (prefixWord ++ tailWord_7701178) baseStart_7701178 baseEnd_7701178 := by
    simpa [prefixWord, tailWord_7701178, baseEnd_7701178] using wordTrace_append hprefix tailTrace_7701178
  have hstable : (prefixWord ++ tailWord_7701178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701178).length < 2 ^ (prefixWord ++ tailWord_7701178).sum := by decide
  have hdescent : baseEnd_7701178 < baseStart_7701178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701188 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_7701188 : Nat := 118140960795 + 7701188 * 2 ^ 59
def prefixEnd_7701188 : Nat := 4983230072969 + 3 ^ 40 * 7701188 * 2
def baseEnd_7701188 : Nat := 3954411054637520300232887

theorem tailTrace_7701188 : CollatzResearch.WordTrace tailWord_7701188 prefixEnd_7701188 3954411054637520300232887 := by
  unfold tailWord_7701188
  simp only [CollatzResearch.WordTrace]
  refine ⟨140442701011959304521228109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187256934682612406028304145 140442701011959304521228109)
  ·
    refine ⟨52666012879484739195460541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140442701011959304521228109 52666012879484739195460541)
    ·
      refine ⟨19749754829806777198297703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52666012879484739195460541 19749754829806777198297703)
      ·
        refine ⟨29624632244710165797446555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19749754829806777198297703 29624632244710165797446555)
        ·
          refine ⟨44436948367065248696169833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29624632244710165797446555 44436948367065248696169833)
          ·
            refine ⟨33327711275298936522127375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44436948367065248696169833 33327711275298936522127375)
            ·
              refine ⟨49991566912948404783191063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33327711275298936522127375 49991566912948404783191063)
              ·
                refine ⟨74987350369422607174786595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49991566912948404783191063 74987350369422607174786595)
                ·
                  refine ⟨112481025554133910762179893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74987350369422607174786595 112481025554133910762179893)
                  ·
                    refine ⟨10545096145700054133954365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112481025554133910762179893 10545096145700054133954365)
                    ·
                      refine ⟨3954411054637520300232887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10545096145700054133954365 3954411054637520300232887)
                      ·
                        rfl

theorem cell23_7701188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_7701188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701188 prefixEnd_7701188 := by exact prefixLift 7701188
  have htrace : WordTrace (prefixWord ++ tailWord_7701188) baseStart_7701188 baseEnd_7701188 := by
    simpa [prefixWord, tailWord_7701188, baseEnd_7701188] using wordTrace_append hprefix tailTrace_7701188
  have hstable : (prefixWord ++ tailWord_7701188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701188).length < 2 ^ (prefixWord ++ tailWord_7701188).sum := by decide
  have hdescent : baseEnd_7701188 < baseStart_7701188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701208 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 2, 5]
def baseStart_7701208 : Nat := 118140960795 + 7701208 * 2 ^ 59
def prefixEnd_7701208 : Nat := 4983230072969 + 3 ^ 40 * 7701208 * 2
def baseEnd_7701208 : Nat := 1318140441416870073994265

theorem tailTrace_7701208 : CollatzResearch.WordTrace tailWord_7701208 prefixEnd_7701208 1318140441416870073994265 := by
  unfold tailWord_7701208
  simp only [CollatzResearch.WordTrace]
  refine ⟨140443065741923076229092139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187257420989230768305456185 140443065741923076229092139)
  ·
    refine ⟨210664598612884614343638209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140443065741923076229092139 210664598612884614343638209)
    ·
      refine ⟨157998448959663460757728657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210664598612884614343638209 157998448959663460757728657)
      ·
        refine ⟨118498836719747595568296493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157998448959663460757728657 118498836719747595568296493)
        ·
          refine ⟨44437063769905348338111185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118498836719747595568296493 44437063769905348338111185)
          ·
            refine ⟨33327797827429011253583389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44437063769905348338111185 33327797827429011253583389)
            ·
              refine ⟨12497924185285879220093771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33327797827429011253583389 12497924185285879220093771)
              ·
                refine ⟨18746886277928818830140657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12497924185285879220093771 18746886277928818830140657)
                ·
                  refine ⟨14060164708446614122605493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18746886277928818830140657 14060164708446614122605493)
                  ·
                    refine ⟨1318140441416870073994265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14060164708446614122605493 1318140441416870073994265)
                    ·
                      rfl

theorem cell23_7701208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_7701208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701208 prefixEnd_7701208 := by exact prefixLift 7701208
  have htrace : WordTrace (prefixWord ++ tailWord_7701208) baseStart_7701208 baseEnd_7701208 := by
    simpa [prefixWord, tailWord_7701208, baseEnd_7701208] using wordTrace_append hprefix tailTrace_7701208
  have hstable : (prefixWord ++ tailWord_7701208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701208).length < 2 ^ (prefixWord ++ tailWord_7701208).sum := by decide
  have hdescent : baseEnd_7701208 < baseStart_7701208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701211 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 4]
def baseStart_7701211 : Nat := 118140960795 + 7701211 * 2 ^ 59
def prefixEnd_7701211 : Nat := 4983230072969 + 3 ^ 40 * 7701211 * 2
def baseEnd_7701211 : Nat := 3954422864692573710245281

theorem tailTrace_7701211 : CollatzResearch.WordTrace tailWord_7701211 prefixEnd_7701211 3954422864692573710245281 := by
  unfold tailWord_7701211
  simp only [CollatzResearch.WordTrace]
  refine ⟨280886240902835283970543487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187257493935223522647028991 280886240902835283970543487)
  ·
    refine ⟨421329361354252925955815231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280886240902835283970543487 421329361354252925955815231)
    ·
      refine ⟨631994042031379388933722847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421329361354252925955815231 631994042031379388933722847)
      ·
        refine ⟨947991063047069083400584271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631994042031379388933722847 947991063047069083400584271)
        ·
          refine ⟨1421986594570603625100876407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947991063047069083400584271 1421986594570603625100876407)
          ·
            refine ⟨2132979891855905437651314611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421986594570603625100876407 2132979891855905437651314611)
            ·
              refine ⟨3199469837783858156476971917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132979891855905437651314611 3199469837783858156476971917)
              ·
                refine ⟨1199801189168946808678864469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3199469837783858156476971917 1199801189168946808678864469)
                ·
                  refine ⟨14060170185573595414205443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1199801189168946808678864469 14060170185573595414205443)
                  ·
                    refine ⟨21090255278360393121308165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14060170185573595414205443 21090255278360393121308165)
                    ·
                      refine ⟨3954422864692573710245281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21090255278360393121308165 3954422864692573710245281)
                      ·
                        rfl

theorem cell23_7701211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 4].length) (baseStart_7701211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701211 prefixEnd_7701211 := by exact prefixLift 7701211
  have htrace : WordTrace (prefixWord ++ tailWord_7701211) baseStart_7701211 baseEnd_7701211 := by
    simpa [prefixWord, tailWord_7701211, baseEnd_7701211] using wordTrace_append hprefix tailTrace_7701211
  have hstable : (prefixWord ++ tailWord_7701211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701211).length < 2 ^ (prefixWord ++ tailWord_7701211).sum := by decide
  have hdescent : baseEnd_7701211 < baseStart_7701211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701212 : List Nat := [2, 2, 5, 1, 1, 2, 2, 3, 5]
def baseStart_7701212 : Nat := 118140960795 + 7701212 * 2 ^ 59
def prefixEnd_7701212 : Nat := 4983230072969 + 3 ^ 40 * 7701212 * 2
def baseEnd_7701212 : Nat := 439380375352580911814753

theorem tailTrace_7701212 : CollatzResearch.WordTrace tailWord_7701212 prefixEnd_7701212 439380375352580911814753 := by
  unfold tailWord_7701212
  simp only [CollatzResearch.WordTrace]
  refine ⟨140443138687915830570664945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187257518250554440760886593 140443138687915830570664945)
  ·
    refine ⟨105332354015936872927998709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140443138687915830570664945 105332354015936872927998709)
    ·
      refine ⟨9874908188994081836999879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105332354015936872927998709 9874908188994081836999879)
      ·
        refine ⟨14812362283491122755499819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9874908188994081836999879 14812362283491122755499819)
        ·
          refine ⟨22218543425236684133249729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14812362283491122755499819 22218543425236684133249729)
          ·
            refine ⟨16663907568927513099937297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22218543425236684133249729 16663907568927513099937297)
            ·
              refine ⟨12497930676695634824952973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16663907568927513099937297 12497930676695634824952973)
              ·
                refine ⟨4686724003760863059357365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12497930676695634824952973 4686724003760863059357365)
                ·
                  refine ⟨439380375352580911814753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4686724003760863059357365 439380375352580911814753)
                  ·
                    rfl

theorem cell23_7701212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_7701212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701212 prefixEnd_7701212 := by exact prefixLift 7701212
  have htrace : WordTrace (prefixWord ++ tailWord_7701212) baseStart_7701212 baseEnd_7701212 := by
    simpa [prefixWord, tailWord_7701212, baseEnd_7701212] using wordTrace_append hprefix tailTrace_7701212
  have hstable : (prefixWord ++ tailWord_7701212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701212).length < 2 ^ (prefixWord ++ tailWord_7701212).sum := by decide
  have hdescent : baseEnd_7701212 < baseStart_7701212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701255 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 3, 4]
def baseStart_7701255 : Nat := 118140960795 + 7701255 * 2 ^ 59
def prefixEnd_7701255 : Nat := 4983230072969 + 3 ^ 40 * 7701255 * 2
def baseEnd_7701255 : Nat := 1318148485947123846031693

theorem tailTrace_7701255 : CollatzResearch.WordTrace tailWord_7701255 prefixEnd_7701255 1318148485947123846031693 := by
  unfold tailWord_7701255
  simp only [CollatzResearch.WordTrace]
  refine ⟨280887845714675879485145219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187258563809783919656763479 280887845714675879485145219)
  ·
    refine ⟨421331768572013819227717829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280887845714675879485145219 421331768572013819227717829)
    ·
      refine ⟨78999706607252591105197093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421331768572013819227717829 78999706607252591105197093)
      ·
        refine ⟨14812444988859860832224455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78999706607252591105197093 14812444988859860832224455)
        ·
          refine ⟨22218667483289791248336683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14812444988859860832224455 22218667483289791248336683)
          ·
            refine ⟨33328001224934686872505025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22218667483289791248336683 33328001224934686872505025)
            ·
              refine ⟨24996000918701015154378769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33328001224934686872505025 24996000918701015154378769)
              ·
                refine ⟨18747000689025761365784077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24996000918701015154378769 18747000689025761365784077)
                ·
                  refine ⟨7030125258384660512169029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18747000689025761365784077 7030125258384660512169029)
                  ·
                    refine ⟨1318148485947123846031693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7030125258384660512169029 1318148485947123846031693)
                    ·
                      rfl

theorem cell23_7701255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_7701255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701255 prefixEnd_7701255 := by exact prefixLift 7701255
  have htrace : WordTrace (prefixWord ++ tailWord_7701255) baseStart_7701255 baseEnd_7701255 := by
    simpa [prefixWord, tailWord_7701255, baseEnd_7701255] using wordTrace_append hprefix tailTrace_7701255
  have hstable : (prefixWord ++ tailWord_7701255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701255).length < 2 ^ (prefixWord ++ tailWord_7701255).sum := by decide
  have hdescent : baseEnd_7701255 < baseStart_7701255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701298 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_7701298 : Nat := 118140960795 + 7701298 * 2 ^ 59
def prefixEnd_7701298 : Nat := 4983230072969 + 3 ^ 40 * 7701298 * 2
def baseEnd_7701298 : Nat := 1318155845836504956619127

theorem tailTrace_7701298 : CollatzResearch.WordTrace tailWord_7701298 prefixEnd_7701298 1318155845836504956619127 := by
  unfold tailWord_7701298
  simp only [CollatzResearch.WordTrace]
  refine ⟨70222353513380024457240137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187259609369013398552640365 70222353513380024457240137)
  ·
    refine ⟨52666765135035018342930103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70222353513380024457240137 52666765135035018342930103)
    ·
      refine ⟨79000147702552527514395155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52666765135035018342930103 79000147702552527514395155)
      ·
        refine ⟨118500221553828791271592733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79000147702552527514395155 118500221553828791271592733)
        ·
          refine ⟨44437583082685796726847275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118500221553828791271592733 44437583082685796726847275)
          ·
            refine ⟨66656374624028695090270913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44437583082685796726847275 66656374624028695090270913)
            ·
              refine ⟨49992280968021521317703185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66656374624028695090270913 49992280968021521317703185)
              ·
                refine ⟨37494210726016140988277389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49992280968021521317703185 37494210726016140988277389)
                ·
                  refine ⟨14060329022256052870604021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37494210726016140988277389 14060329022256052870604021)
                  ·
                    refine ⟨1318155845836504956619127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14060329022256052870604021 1318155845836504956619127)
                    ·
                      rfl

theorem cell23_7701298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_7701298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701298 prefixEnd_7701298 := by exact prefixLift 7701298
  have htrace : WordTrace (prefixWord ++ tailWord_7701298) baseStart_7701298 baseEnd_7701298 := by
    simpa [prefixWord, tailWord_7701298, baseEnd_7701298] using wordTrace_append hprefix tailTrace_7701298
  have hstable : (prefixWord ++ tailWord_7701298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701298).length < 2 ^ (prefixWord ++ tailWord_7701298).sum := by decide
  have hdescent : baseEnd_7701298 < baseStart_7701298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701302 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_7701302 : Nat := 118140960795 + 7701302 * 2 ^ 59
def prefixEnd_7701302 : Nat := 4983230072969 + 3 ^ 40 * 7701302 * 2
def baseEnd_7701302 : Nat := 439385510159125872689707

theorem tailTrace_7701302 : CollatzResearch.WordTrace tailWord_7701302 prefixEnd_7701302 439385510159125872689707 := by
  unfold tailWord_7701302
  simp only [CollatzResearch.WordTrace]
  refine ⟨17555597496594100407006635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187259706630337071008070773 17555597496594100407006635)
  ·
    refine ⟨26333396244891150610509953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17555597496594100407006635 26333396244891150610509953)
    ·
      refine ⟨19750047183668362957882465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26333396244891150610509953 19750047183668362957882465)
      ·
        refine ⟨14812535387751272218411849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19750047183668362957882465 14812535387751272218411849)
        ·
          refine ⟨11109401540813454163808887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14812535387751272218411849 11109401540813454163808887)
          ·
            refine ⟨16664102311220181245713331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109401540813454163808887 16664102311220181245713331)
            ·
              refine ⟨24996153466830271868569997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16664102311220181245713331 24996153466830271868569997)
              ·
                refine ⟨9373557550061351950713749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24996153466830271868569997 9373557550061351950713749)
                ·
                  refine ⟨439385510159125872689707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9373557550061351950713749 439385510159125872689707)
                  ·
                    rfl

theorem cell23_7701302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_7701302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701302 prefixEnd_7701302 := by exact prefixLift 7701302
  have htrace : WordTrace (prefixWord ++ tailWord_7701302) baseStart_7701302 baseEnd_7701302 := by
    simpa [prefixWord, tailWord_7701302, baseEnd_7701302] using wordTrace_append hprefix tailTrace_7701302
  have hstable : (prefixWord ++ tailWord_7701302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701302).length < 2 ^ (prefixWord ++ tailWord_7701302).sum := by decide
  have hdescent : baseEnd_7701302 < baseStart_7701302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701328 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 6, 4]
def baseStart_7701328 : Nat := 118140960795 + 7701328 * 2 ^ 59
def prefixEnd_7701328 : Nat := 4983230072969 + 3 ^ 40 * 7701328 * 2
def baseEnd_7701328 : Nat := 1318160980643049917494081

theorem tailTrace_7701328 : CollatzResearch.WordTrace tailWord_7701328 prefixEnd_7701328 1318160980643049917494081 := by
  unfold tailWord_7701328
  simp only [CollatzResearch.WordTrace]
  refine ⟨140445254121705706476276319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187260338828940941968368425 140445254121705706476276319)
  ·
    refine ⟨210667881182558559714414479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140445254121705706476276319 210667881182558559714414479)
    ·
      refine ⟨316001821773837839571621719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210667881182558559714414479 316001821773837839571621719)
      ·
        refine ⟨474002732660756759357432579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316001821773837839571621719 474002732660756759357432579)
        ·
          refine ⟨711004098991135139036148869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474002732660756759357432579 711004098991135139036148869)
          ·
            refine ⟨133313268560837838569277913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 711004098991135139036148869 133313268560837838569277913)
            ·
              refine ⟨99984951420628378926958435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133313268560837838569277913 99984951420628378926958435)
              ·
                refine ⟨149977427130942568390437653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99984951420628378926958435 149977427130942568390437653)
                ·
                  refine ⟨7030191896762932893301765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149977427130942568390437653 7030191896762932893301765)
                  ·
                    refine ⟨1318160980643049917494081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7030191896762932893301765 1318160980643049917494081)
                    ·
                      rfl

theorem cell23_7701328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 4].length) (baseStart_7701328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701328 prefixEnd_7701328 := by exact prefixLift 7701328
  have htrace : WordTrace (prefixWord ++ tailWord_7701328) baseStart_7701328 baseEnd_7701328 := by
    simpa [prefixWord, tailWord_7701328, baseEnd_7701328] using wordTrace_append hprefix tailTrace_7701328
  have hstable : (prefixWord ++ tailWord_7701328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701328).length < 2 ^ (prefixWord ++ tailWord_7701328).sum := by decide
  have hdescent : baseEnd_7701328 < baseStart_7701328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701341 : List Nat := [1, 4, 18]
def baseStart_7701341 : Nat := 118140960795 + 7701341 * 2 ^ 59
def prefixEnd_7701341 : Nat := 4983230072969 + 3 ^ 40 * 7701341 * 2
def baseEnd_7701341 : Nat := 602726660139865600003

theorem tailTrace_7701341 : CollatzResearch.WordTrace tailWord_7701341 prefixEnd_7701341 602726660139865600003 := by
  unfold tailWord_7701341
  simp only [CollatzResearch.WordTrace]
  refine ⟨280890982392364316172775877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187260654928242877448517251 280890982392364316172775877)
  ·
    refine ⟨52667059198568309282395477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280890982392364316172775877 52667059198568309282395477)
    ·
      refine ⟨602726660139865600003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 52667059198568309282395477 602726660139865600003)
      ·
        rfl

theorem cell23_7701341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 18].length) (baseStart_7701341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701341 prefixEnd_7701341 := by exact prefixLift 7701341
  have htrace : WordTrace (prefixWord ++ tailWord_7701341) baseStart_7701341 baseEnd_7701341 := by
    simpa [prefixWord, tailWord_7701341, baseEnd_7701341] using wordTrace_append hprefix tailTrace_7701341
  have hstable : (prefixWord ++ tailWord_7701341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701341).length < 2 ^ (prefixWord ++ tailWord_7701341).sum := by decide
  have hdescent : baseEnd_7701341 < baseStart_7701341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701346 : List Nat := [3, 3, 2, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_7701346 : Nat := 118140960795 + 7701346 * 2 ^ 59
def prefixEnd_7701346 : Nat := 4983230072969 + 3 ^ 40 * 7701346 * 2
def baseEnd_7701346 : Nat := 3954492184580930682057161

theorem tailTrace_7701346 : CollatzResearch.WordTrace tailWord_7701346 prefixEnd_7701346 3954492184580930682057161 := by
  unfold tailWord_7701346
  simp only [CollatzResearch.WordTrace]
  refine ⟨70222791189336550506676973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187260776504897468017805261 70222791189336550506676973)
  ·
    refine ⟨26333546696001206440003865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70222791189336550506676973 26333546696001206440003865)
    ·
      refine ⟨19750160022000904830002899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26333546696001206440003865 19750160022000904830002899)
      ·
        refine ⟨29625240033001357245004349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19750160022000904830002899 29625240033001357245004349)
        ·
          refine ⟨11109465012375508966876631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29625240033001357245004349 11109465012375508966876631)
          ·
            refine ⟨16664197518563263450314947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11109465012375508966876631 16664197518563263450314947)
            ·
              refine ⟨24996296277844895175472421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16664197518563263450314947 24996296277844895175472421)
              ·
                refine ⟨4686805552095917845401079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24996296277844895175472421 4686805552095917845401079)
                ·
                  refine ⟨7030208328143876768101619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686805552095917845401079 7030208328143876768101619)
                  ·
                    refine ⟨10545312492215815152152429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7030208328143876768101619 10545312492215815152152429)
                    ·
                      refine ⟨3954492184580930682057161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10545312492215815152152429 3954492184580930682057161)
                      ·
                        rfl

theorem cell23_7701346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_7701346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701346 prefixEnd_7701346 := by exact prefixLift 7701346
  have htrace : WordTrace (prefixWord ++ tailWord_7701346) baseStart_7701346 baseEnd_7701346 := by
    simpa [prefixWord, tailWord_7701346, baseEnd_7701346] using wordTrace_append hprefix tailTrace_7701346
  have hstable : (prefixWord ++ tailWord_7701346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701346).length < 2 ^ (prefixWord ++ tailWord_7701346).sum := by decide
  have hdescent : baseEnd_7701346 < baseStart_7701346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701365 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_7701365 : Nat := 118140960795 + 7701365 * 2 ^ 59
def prefixEnd_7701365 : Nat := 4983230072969 + 3 ^ 40 * 7701365 * 2
def baseEnd_7701365 : Nat := 3954501940713366107719573

theorem tailTrace_7701365 : CollatzResearch.WordTrace tailWord_7701365 prefixEnd_7701365 3954501940713366107719573 := by
  unfold tailWord_7701365
  simp only [CollatzResearch.WordTrace]
  refine ⟨280891857744277368271649549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187261238496184912181099699 280891857744277368271649549)
  ·
    refine ⟨105334446654104013101868581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280891857744277368271649549 105334446654104013101868581)
    ·
      refine ⟨19750208747644502456600359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105334446654104013101868581 19750208747644502456600359)
      ·
        refine ⟨29625313121466753684900539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19750208747644502456600359 29625313121466753684900539)
        ·
          refine ⟨44437969682200130527350809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29625313121466753684900539 44437969682200130527350809)
          ·
            refine ⟨33328477261650097895513107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44437969682200130527350809 33328477261650097895513107)
            ·
              refine ⟨49992715892475146843269661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33328477261650097895513107 49992715892475146843269661)
              ·
                refine ⟨18747268459678180066226123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49992715892475146843269661 18747268459678180066226123)
                ·
                  refine ⟨28120902689517270099339185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18747268459678180066226123 28120902689517270099339185)
                  ·
                    refine ⟨21090677017137952574504389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28120902689517270099339185 21090677017137952574504389)
                    ·
                      refine ⟨3954501940713366107719573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21090677017137952574504389 3954501940713366107719573)
                      ·
                        rfl

theorem cell23_7701365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_7701365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701365 prefixEnd_7701365 := by exact prefixLift 7701365
  have htrace : WordTrace (prefixWord ++ tailWord_7701365) baseStart_7701365 baseEnd_7701365 := by
    simpa [prefixWord, tailWord_7701365, baseEnd_7701365] using wordTrace_append hprefix tailTrace_7701365
  have hstable : (prefixWord ++ tailWord_7701365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701365).length < 2 ^ (prefixWord ++ tailWord_7701365).sum := by decide
  have hdescent : baseEnd_7701365 < baseStart_7701365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701385 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 3]
def baseStart_7701385 : Nat := 118140960795 + 7701385 * 2 ^ 59
def prefixEnd_7701385 : Nat := 4983230072969 + 3 ^ 40 * 7701385 * 2
def baseEnd_7701385 : Nat := 3954512210326456029469481

theorem tailTrace_7701385 : CollatzResearch.WordTrace tailWord_7701385 prefixEnd_7701385 3954512210326456029469481 := by
  unfold tailWord_7701385
  simp only [CollatzResearch.WordTrace]
  refine ⟨280892587204204911687377609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187261724802803274458251739 280892587204204911687377609)
  ·
    refine ⟨210669440403153683765533207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280892587204204911687377609 210669440403153683765533207)
    ·
      refine ⟨316004160604730525648299811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210669440403153683765533207 316004160604730525648299811)
      ·
        refine ⟨474006240907095788472449717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316004160604730525648299811 474006240907095788472449717)
        ·
          refine ⟨44438085085040230169292161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 474006240907095788472449717 44438085085040230169292161)
          ·
            refine ⟨33328563813780172626969121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44438085085040230169292161 33328563813780172626969121)
            ·
              refine ⟨24996422860335129470226841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33328563813780172626969121 24996422860335129470226841)
              ·
                refine ⟨18747317145251347102670131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24996422860335129470226841 18747317145251347102670131)
                ·
                  refine ⟨28120975717877020654005197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18747317145251347102670131 28120975717877020654005197)
                  ·
                    refine ⟨10545365894203882745251949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28120975717877020654005197 10545365894203882745251949)
                    ·
                      refine ⟨3954512210326456029469481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10545365894203882745251949 3954512210326456029469481)
                      ·
                        rfl

theorem cell23_7701385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_7701385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701385 prefixEnd_7701385 := by exact prefixLift 7701385
  have htrace : WordTrace (prefixWord ++ tailWord_7701385) baseStart_7701385 baseEnd_7701385 := by
    simpa [prefixWord, tailWord_7701385, baseEnd_7701385] using wordTrace_append hprefix tailTrace_7701385
  have hstable : (prefixWord ++ tailWord_7701385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701385).length < 2 ^ (prefixWord ++ tailWord_7701385).sum := by decide
  have hdescent : baseEnd_7701385 < baseStart_7701385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701386 : List Nat := [3, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_7701386 : Nat := 118140960795 + 7701386 * 2 ^ 59
def prefixEnd_7701386 : Nat := 4983230072969 + 3 ^ 40 * 7701386 * 2
def baseEnd_7701386 : Nat := 3954512723807110525556977

theorem tailTrace_7701386 : CollatzResearch.WordTrace tailWord_7701386 prefixEnd_7701386 3954512723807110525556977 := by
  unfold tailWord_7701386
  simp only [CollatzResearch.WordTrace]
  refine ⟨70223155919300322214541003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187261749118134192572109341 70223155919300322214541003)
  ·
    refine ⟨105334733878950483321811505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70223155919300322214541003 105334733878950483321811505)
    ·
      refine ⟨79001050409212862491358629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105334733878950483321811505 79001050409212862491358629)
      ·
        refine ⟨14812696951727411717129743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79001050409212862491358629 14812696951727411717129743)
        ·
          refine ⟨22219045427591117575694615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14812696951727411717129743 22219045427591117575694615)
          ·
            refine ⟨33328568141386676363541923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22219045427591117575694615 33328568141386676363541923)
            ·
              refine ⟨49992852212080014545312885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33328568141386676363541923 49992852212080014545312885)
              ·
                refine ⟨4686829894882501363623083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49992852212080014545312885 4686829894882501363623083)
                ·
                  refine ⟨7030244842323752045434625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686829894882501363623083 7030244842323752045434625)
                  ·
                    refine ⟨5272683631742814034075969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7030244842323752045434625 5272683631742814034075969)
                    ·
                      refine ⟨3954512723807110525556977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272683631742814034075969 3954512723807110525556977)
                      ·
                        rfl

theorem cell23_7701386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_7701386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701386 prefixEnd_7701386 := by exact prefixLift 7701386
  have htrace : WordTrace (prefixWord ++ tailWord_7701386) baseStart_7701386 baseEnd_7701386 := by
    simpa [prefixWord, tailWord_7701386, baseEnd_7701386] using wordTrace_append hprefix tailTrace_7701386
  have hstable : (prefixWord ++ tailWord_7701386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701386).length < 2 ^ (prefixWord ++ tailWord_7701386).sum := by decide
  have hdescent : baseEnd_7701386 < baseStart_7701386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701395 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 5, 3, 2]
def baseStart_7701395 : Nat := 118140960795 + 7701395 * 2 ^ 59
def prefixEnd_7701395 : Nat := 4983230072969 + 3 ^ 40 * 7701395 * 2
def baseEnd_7701395 : Nat := 3954517345133000990344435

theorem tailTrace_7701395 : CollatzResearch.WordTrace tailWord_7701395 prefixEnd_7701395 3954517345133000990344435 := by
  unfold tailWord_7701395
  simp only [CollatzResearch.WordTrace]
  refine ⟨280892951934168683395241639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187261967956112455596827759 280892951934168683395241639)
  ·
    refine ⟨421339427901253025092862459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280892951934168683395241639 421339427901253025092862459)
    ·
      refine ⟨632009141851879537639293689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421339427901253025092862459 632009141851879537639293689)
      ·
        refine ⟨474006856388909653229470267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632009141851879537639293689 474006856388909653229470267)
        ·
          refine ⟨711010284583364479844205401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474006856388909653229470267 711010284583364479844205401)
          ·
            refine ⟨533257713437523359883154051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711010284583364479844205401 533257713437523359883154051)
            ·
              refine ⟨799886570156285039824731077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533257713437523359883154051 799886570156285039824731077)
              ·
                refine ⟨149978731904303444967137077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799886570156285039824731077 149978731904303444967137077)
                ·
                  refine ⟨14060506116028447965669101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149978731904303444967137077 14060506116028447965669101)
                  ·
                    refine ⟨5272689793510667987125913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14060506116028447965669101 5272689793510667987125913)
                    ·
                      refine ⟨3954517345133000990344435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272689793510667987125913 3954517345133000990344435)
                      ·
                        rfl

theorem cell23_7701395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 3, 2].length) (baseStart_7701395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701395 prefixEnd_7701395 := by exact prefixLift 7701395
  have htrace : WordTrace (prefixWord ++ tailWord_7701395) baseStart_7701395 baseEnd_7701395 := by
    simpa [prefixWord, tailWord_7701395, baseEnd_7701395] using wordTrace_append hprefix tailTrace_7701395
  have hstable : (prefixWord ++ tailWord_7701395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701395).length < 2 ^ (prefixWord ++ tailWord_7701395).sum := by decide
  have hdescent : baseEnd_7701395 < baseStart_7701395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701408 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_7701408 : Nat := 118140960795 + 7701408 * 2 ^ 59
def prefixEnd_7701408 : Nat := 4983230072969 + 3 ^ 40 * 7701408 * 2
def baseEnd_7701408 : Nat := 3954524020381509439481875

theorem tailTrace_7701408 : CollatzResearch.WordTrace tailWord_7701408 prefixEnd_7701408 3954524020381509439481875 := by
  unfold tailWord_7701408
  simp only [CollatzResearch.WordTrace]
  refine ⟨140446713041560793307732439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187262284055414391076976585 140446713041560793307732439)
  ·
    refine ⟨210670069562341189961598659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140446713041560793307732439 210670069562341189961598659)
    ·
      refine ⟨316005104343511784942397989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210670069562341189961598659 316005104343511784942397989)
      ·
        refine ⟨59250957064408459676699623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316005104343511784942397989 59250957064408459676699623)
        ·
          refine ⟨88876435596612689515049435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59250957064408459676699623 88876435596612689515049435)
          ·
            refine ⟨133314653394919034272574153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88876435596612689515049435 133314653394919034272574153)
            ·
              refine ⟨99985990046189275704430615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133314653394919034272574153 99985990046189275704430615)
              ·
                refine ⟨149978985069283913556645923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99985990046189275704430615 149978985069283913556645923)
                ·
                  refine ⟨224968477603925870334968885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149978985069283913556645923 224968477603925870334968885)
                  ·
                    refine ⟨21090794775368050343903333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224968477603925870334968885 21090794775368050343903333)
                    ·
                      refine ⟨3954524020381509439481875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21090794775368050343903333 3954524020381509439481875)
                      ·
                        rfl

theorem cell23_7701408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_7701408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701408 prefixEnd_7701408 := by exact prefixLift 7701408
  have htrace : WordTrace (prefixWord ++ tailWord_7701408) baseStart_7701408 baseEnd_7701408 := by
    simpa [prefixWord, tailWord_7701408, baseEnd_7701408] using wordTrace_append hprefix tailTrace_7701408
  have hstable : (prefixWord ++ tailWord_7701408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701408).length < 2 ^ (prefixWord ++ tailWord_7701408).sum := by decide
  have hdescent : baseEnd_7701408 < baseStart_7701408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701429 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_7701429 : Nat := 118140960795 + 7701429 * 2 ^ 59
def prefixEnd_7701429 : Nat := 4983230072969 + 3 ^ 40 * 7701429 * 2
def baseEnd_7701429 : Nat := 3954534803475253857319279

theorem tailTrace_7701429 : CollatzResearch.WordTrace tailWord_7701429 prefixEnd_7701429 3954534803475253857319279 := by
  unfold tailWord_7701429
  simp only [CollatzResearch.WordTrace]
  refine ⟨280894192016045507201979341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187262794677363671467986227 280894192016045507201979341)
  ·
    refine ⟨105335322006017065200742253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280894192016045507201979341 105335322006017065200742253)
    ·
      refine ⟨39500745752256399450278345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105335322006017065200742253 39500745752256399450278345)
      ·
        refine ⟨29625559314192299587708759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39500745752256399450278345 29625559314192299587708759)
        ·
          refine ⟨44438338971288449381563139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29625559314192299587708759 44438338971288449381563139)
          ·
            refine ⟨66657508456932674072344709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44438338971288449381563139 66657508456932674072344709)
            ·
              refine ⟨12498282835674876388564633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66657508456932674072344709 12498282835674876388564633)
              ·
                refine ⟨9373712126756157291423475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12498282835674876388564633 9373712126756157291423475)
                ·
                  refine ⟨14060568190134235937135213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9373712126756157291423475 14060568190134235937135213)
                  ·
                    refine ⟨5272713071300338476425705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14060568190134235937135213 5272713071300338476425705)
                    ·
                      refine ⟨3954534803475253857319279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272713071300338476425705 3954534803475253857319279)
                      ·
                        rfl

theorem cell23_7701429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_7701429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701429 prefixEnd_7701429 := by exact prefixLift 7701429
  have htrace : WordTrace (prefixWord ++ tailWord_7701429) baseStart_7701429 baseEnd_7701429 := by
    simpa [prefixWord, tailWord_7701429, baseEnd_7701429] using wordTrace_append hprefix tailTrace_7701429
  have hstable : (prefixWord ++ tailWord_7701429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701429).length < 2 ^ (prefixWord ++ tailWord_7701429).sum := by decide
  have hdescent : baseEnd_7701429 < baseStart_7701429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701465 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 7]
def baseStart_7701465 : Nat := 118140960795 + 7701465 * 2 ^ 59
def prefixEnd_7701465 : Nat := 4983230072969 + 3 ^ 40 * 7701465 * 2
def baseEnd_7701465 : Nat := 439394809864312857385457

theorem tailTrace_7701465 : CollatzResearch.WordTrace tailWord_7701465 prefixEnd_7701465 439394809864312857385457 := by
  unfold tailWord_7701465
  simp only [CollatzResearch.WordTrace]
  refine ⟨280895505043915085350289849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187263670029276723566859899 280895505043915085350289849)
  ·
    refine ⟨210671628782936314012717387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280895505043915085350289849 210671628782936314012717387)
    ·
      refine ⟨316007443174404471019076081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210671628782936314012717387 316007443174404471019076081)
      ·
        refine ⟨237005582380803353264307061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316007443174404471019076081 237005582380803353264307061)
        ·
          refine ⟨22219273348200314368528787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237005582380803353264307061 22219273348200314368528787)
          ·
            refine ⟨33328910022300471552793181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22219273348200314368528787 33328910022300471552793181)
            ·
              refine ⟨12498341258362676832297443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33328910022300471552793181 12498341258362676832297443)
              ·
                refine ⟨18747511887544015248446165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12498341258362676832297443 18747511887544015248446165)
                ·
                  refine ⟨439394809864312857385457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18747511887544015248446165 439394809864312857385457)
                  ·
                    rfl

theorem cell23_7701465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 7].length) (baseStart_7701465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701465 prefixEnd_7701465 := by exact prefixLift 7701465
  have htrace : WordTrace (prefixWord ++ tailWord_7701465) baseStart_7701465 baseEnd_7701465 := by
    simpa [prefixWord, tailWord_7701465, baseEnd_7701465] using wordTrace_append hprefix tailTrace_7701465
  have hstable : (prefixWord ++ tailWord_7701465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701465).length < 2 ^ (prefixWord ++ tailWord_7701465).sum := by decide
  have hdescent : baseEnd_7701465 < baseStart_7701465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701475 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 3]
def baseStart_7701475 : Nat := 118140960795 + 7701475 * 2 ^ 59
def prefixEnd_7701475 : Nat := 4983230072969 + 3 ^ 40 * 7701475 * 2
def baseEnd_7701475 : Nat := 3954558423585360677344067

theorem tailTrace_7701475 : CollatzResearch.WordTrace tailWord_7701475 prefixEnd_7701475 3954558423585360677344067 := by
  unfold tailWord_7701475
  simp only [CollatzResearch.WordTrace]
  refine ⟨280895869773878857058153879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187263913182585904705435919 280895869773878857058153879)
  ·
    refine ⟨421343804660818285587230819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280895869773878857058153879 421343804660818285587230819)
    ·
      refine ⟨632015706991227428380846229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421343804660818285587230819 632015706991227428380846229)
      ·
        refine ⟨29625736265213785705352167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 632015706991227428380846229 29625736265213785705352167)
        ·
          refine ⟨44438604397820678558028251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29625736265213785705352167 44438604397820678558028251)
          ·
            refine ⟨66657906596731017837042377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44438604397820678558028251 66657906596731017837042377)
            ·
              refine ⟨49993429947548263377781783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66657906596731017837042377 49993429947548263377781783)
              ·
                refine ⟨74990144921322395066672675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49993429947548263377781783 74990144921322395066672675)
                ·
                  refine ⟨112485217381983592600009013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74990144921322395066672675 112485217381983592600009013)
                  ·
                    refine ⟨10545489129560961806250845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112485217381983592600009013 10545489129560961806250845)
                    ·
                      refine ⟨3954558423585360677344067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10545489129560961806250845 3954558423585360677344067)
                      ·
                        rfl

theorem cell23_7701475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_7701475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701475 prefixEnd_7701475 := by exact prefixLift 7701475
  have htrace : WordTrace (prefixWord ++ tailWord_7701475) baseStart_7701475 baseEnd_7701475 := by
    simpa [prefixWord, tailWord_7701475, baseEnd_7701475] using wordTrace_append hprefix tailTrace_7701475
  have hstable : (prefixWord ++ tailWord_7701475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701475).length < 2 ^ (prefixWord ++ tailWord_7701475).sum := by decide
  have hdescent : baseEnd_7701475 < baseStart_7701475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701488 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_7701488 : Nat := 118140960795 + 7701488 * 2 ^ 59
def prefixEnd_7701488 : Nat := 4983230072969 + 3 ^ 40 * 7701488 * 2
def baseEnd_7701488 : Nat := 3954565098833869126481507

theorem tailTrace_7701488 : CollatzResearch.WordTrace tailWord_7701488 prefixEnd_7701488 3954565098833869126481507 := by
  unfold tailWord_7701488
  simp only [CollatzResearch.WordTrace]
  refine ⟨140448171961415880139188559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187264229281887840185584745 140448171961415880139188559)
  ·
    refine ⟨210672257942123820208782839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140448171961415880139188559 210672257942123820208782839)
    ·
      refine ⟨316008386913185730313174259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210672257942123820208782839 316008386913185730313174259)
      ·
        refine ⟨474012580369778595469761389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316008386913185730313174259 474012580369778595469761389)
        ·
          refine ⟨177754717638666973301160521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474012580369778595469761389 177754717638666973301160521)
          ·
            refine ⟨133316038229000229975870391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177754717638666973301160521 133316038229000229975870391)
            ·
              refine ⟨199974057343500344963805587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133316038229000229975870391 199974057343500344963805587)
              ·
                refine ⟨299961086015250517445708381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199974057343500344963805587 299961086015250517445708381)
                ·
                  refine ⟨112485407255718944042140643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299961086015250517445708381 112485407255718944042140643)
                  ·
                    refine ⟨168728110883578416063210965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112485407255718944042140643 168728110883578416063210965)
                    ·
                      refine ⟨3954565098833869126481507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168728110883578416063210965 3954565098833869126481507)
                      ·
                        rfl

theorem cell23_7701488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_7701488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701488 prefixEnd_7701488 := by exact prefixLift 7701488
  have htrace : WordTrace (prefixWord ++ tailWord_7701488) baseStart_7701488 baseEnd_7701488 := by
    simpa [prefixWord, tailWord_7701488, baseEnd_7701488] using wordTrace_append hprefix tailTrace_7701488
  have hstable : (prefixWord ++ tailWord_7701488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701488).length < 2 ^ (prefixWord ++ tailWord_7701488).sum := by decide
  have hdescent : baseEnd_7701488 < baseStart_7701488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701505 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7701505 : Nat := 118140960795 + 7701505 * 2 ^ 59
def prefixEnd_7701505 : Nat := 4983230072969 + 3 ^ 40 * 7701505 * 2
def baseEnd_7701505 : Nat := 3954573828004995559968929

theorem tailTrace_7701505 : CollatzResearch.WordTrace tailWord_7701505 prefixEnd_7701505 3954573828004995559968929 := by
  unfold tailWord_7701505
  simp only [CollatzResearch.WordTrace]
  refine ⟨280896963963770172181745969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187264642642513448121163979 280896963963770172181745969)
  ·
    refine ⟨210672722972827629136309477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280896963963770172181745969 210672722972827629136309477)
    ·
      refine ⟨39501135557405180463058027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210672722972827629136309477 39501135557405180463058027)
      ·
        refine ⟨59251703336107770694587041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39501135557405180463058027 59251703336107770694587041)
        ·
          refine ⟨44438777502080828020940281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59251703336107770694587041 44438777502080828020940281)
          ·
            refine ⟨33329083126560621015705211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44438777502080828020940281 33329083126560621015705211)
            ·
              refine ⟨49993624689840931523557817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33329083126560621015705211 49993624689840931523557817)
              ·
                refine ⟨37495218517380698642668363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49993624689840931523557817 37495218517380698642668363)
                ·
                  refine ⟨56242827776071047964002545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37495218517380698642668363 56242827776071047964002545)
                  ·
                    refine ⟨42182120832053285973001909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56242827776071047964002545 42182120832053285973001909)
                    ·
                      refine ⟨3954573828004995559968929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42182120832053285973001909 3954573828004995559968929)
                      ·
                        rfl

theorem cell23_7701505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7701505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701505 prefixEnd_7701505 := by exact prefixLift 7701505
  have htrace : WordTrace (prefixWord ++ tailWord_7701505) baseStart_7701505 baseEnd_7701505 := by
    simpa [prefixWord, tailWord_7701505, baseEnd_7701505] using wordTrace_append hprefix tailTrace_7701505
  have hstable : (prefixWord ++ tailWord_7701505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701505).length < 2 ^ (prefixWord ++ tailWord_7701505).sum := by decide
  have hdescent : baseEnd_7701505 < baseStart_7701505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701546 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_7701546 : Nat := 118140960795 + 7701546 * 2 ^ 59
def prefixEnd_7701546 : Nat := 4983230072969 + 3 ^ 40 * 7701546 * 2
def baseEnd_7701546 : Nat := 1318198293570609966518747

theorem tailTrace_7701546 : CollatzResearch.WordTrace tailWord_7701546 prefixEnd_7701546 1318198293570609966518747 := by
  unfold tailWord_7701546
  simp only [CollatzResearch.WordTrace]
  refine ⟨70224614839155409045997123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187265639571081090789325661 70224614839155409045997123)
  ·
    refine ⟨105336922258733113568995685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70224614839155409045997123 105336922258733113568995685)
    ·
      refine ⟨19750672923512458794186691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105336922258733113568995685 19750672923512458794186691)
      ·
        refine ⟨29626009385268688191280037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19750672923512458794186691 29626009385268688191280037)
        ·
          refine ⟨5554876759737879035865007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29626009385268688191280037 5554876759737879035865007)
          ·
            refine ⟨8332315139606818553797511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554876759737879035865007 8332315139606818553797511)
            ·
              refine ⟨12498472709410227830696267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8332315139606818553797511 12498472709410227830696267)
              ·
                refine ⟨18747709064115341746044401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12498472709410227830696267 18747709064115341746044401)
                ·
                  refine ⟨14060781798086506309533301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18747709064115341746044401 14060781798086506309533301)
                  ·
                    refine ⟨1318198293570609966518747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14060781798086506309533301 1318198293570609966518747)
                    ·
                      rfl

theorem cell23_7701546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_7701546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701546 prefixEnd_7701546 := by exact prefixLift 7701546
  have htrace : WordTrace (prefixWord ++ tailWord_7701546) baseStart_7701546 baseEnd_7701546 := by
    simpa [prefixWord, tailWord_7701546, baseEnd_7701546] using wordTrace_append hprefix tailTrace_7701546
  have hstable : (prefixWord ++ tailWord_7701546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701546).length < 2 ^ (prefixWord ++ tailWord_7701546).sum := by decide
  have hdescent : baseEnd_7701546 < baseStart_7701546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701575 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_7701575 : Nat := 118140960795 + 7701575 * 2 ^ 59
def prefixEnd_7701575 : Nat := 4983230072969 + 3 ^ 40 * 7701575 * 2
def baseEnd_7701575 : Nat := 3954609771650810286093607

theorem tailTrace_7701575 : CollatzResearch.WordTrace tailWord_7701575 prefixEnd_7701575 3954609771650810286093607 := by
  unfold tailWord_7701575
  simp only [CollatzResearch.WordTrace]
  refine ⟨280899517073516574136794179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187266344715677716091196119 280899517073516574136794179)
  ·
    refine ⟨421349275610274861205191269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280899517073516574136794179 421349275610274861205191269)
    ·
      refine ⟨79002989176926536475973363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421349275610274861205191269 79002989176926536475973363)
      ·
        refine ⟨118504483765389804713960045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79002989176926536475973363 118504483765389804713960045)
        ·
          refine ⟨44439181412021176767735017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118504483765389804713960045 44439181412021176767735017)
          ·
            refine ⟨33329386059015882575801263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44439181412021176767735017 33329386059015882575801263)
            ·
              refine ⟨49994079088523823863701895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33329386059015882575801263 49994079088523823863701895)
              ·
                refine ⟨74991118632785735795552843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49994079088523823863701895 74991118632785735795552843)
                ·
                  refine ⟨112486677949178603693329265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74991118632785735795552843 112486677949178603693329265)
                  ·
                    refine ⟨84365008461883952769996949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112486677949178603693329265 84365008461883952769996949)
                    ·
                      refine ⟨3954609771650810286093607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84365008461883952769996949 3954609771650810286093607)
                      ·
                        rfl

theorem cell23_7701575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_7701575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701575 prefixEnd_7701575 := by exact prefixLift 7701575
  have htrace : WordTrace (prefixWord ++ tailWord_7701575) baseStart_7701575 baseEnd_7701575 := by
    simpa [prefixWord, tailWord_7701575, baseEnd_7701575] using wordTrace_append hprefix tailTrace_7701575
  have hstable : (prefixWord ++ tailWord_7701575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701575).length < 2 ^ (prefixWord ++ tailWord_7701575).sum := by decide
  have hdescent : baseEnd_7701575 < baseStart_7701575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701585 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 5, 5]
def baseStart_7701585 : Nat := 118140960795 + 7701585 * 2 ^ 59
def prefixEnd_7701585 : Nat := 4983230072969 + 3 ^ 40 * 7701585 * 2
def baseEnd_7701585 : Nat := 1318204968819118415656187

theorem tailTrace_7701585 : CollatzResearch.WordTrace tailWord_7701585 prefixEnd_7701585 1318204968819118415656187 := by
  unfold tailWord_7701585
  simp only [CollatzResearch.WordTrace]
  refine ⟨280899881803480345844658209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187266587868986897229772139 280899881803480345844658209)
  ·
    refine ⟨210674911352610259383493657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280899881803480345844658209 210674911352610259383493657)
    ·
      refine ⟨158006183514457694537620243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210674911352610259383493657 158006183514457694537620243)
      ·
        refine ⟨237009275271686541806430365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158006183514457694537620243 237009275271686541806430365)
        ·
          refine ⟨88878478226882453177411387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237009275271686541806430365 88878478226882453177411387)
          ·
            refine ⟨133317717340323679766117081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88878478226882453177411387 133317717340323679766117081)
            ·
              refine ⟨99988288005242759824587811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133317717340323679766117081 99988288005242759824587811)
              ·
                refine ⟨149982432007864139736881717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99988288005242759824587811 149982432007864139736881717)
                ·
                  refine ⟨14060853000737263100332661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149982432007864139736881717 14060853000737263100332661)
                  ·
                    refine ⟨1318204968819118415656187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14060853000737263100332661 1318204968819118415656187)
                    ·
                      rfl

theorem cell23_7701585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_7701585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701585 prefixEnd_7701585 := by exact prefixLift 7701585
  have htrace : WordTrace (prefixWord ++ tailWord_7701585) baseStart_7701585 baseEnd_7701585 := by
    simpa [prefixWord, tailWord_7701585, baseEnd_7701585] using wordTrace_append hprefix tailTrace_7701585
  have hstable : (prefixWord ++ tailWord_7701585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701585).length < 2 ^ (prefixWord ++ tailWord_7701585).sum := by decide
  have hdescent : baseEnd_7701585 < baseStart_7701585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701592 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 3, 5, 2]
def baseStart_7701592 : Nat := 118140960795 + 7701592 * 2 ^ 59
def prefixEnd_7701592 : Nat := 4983230072969 + 3 ^ 40 * 7701592 * 2
def baseEnd_7701592 : Nat := 3954618500821936719581029

theorem tailTrace_7701592 : CollatzResearch.WordTrace tailWord_7701592 prefixEnd_7701592 3954618500821936719581029 := by
  unfold tailWord_7701592
  simp only [CollatzResearch.WordTrace]
  refine ⟨140450068557227493020081515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187266758076303324026775353 140450068557227493020081515)
  ·
    refine ⟨210675102835841239530122273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140450068557227493020081515 210675102835841239530122273)
    ·
      refine ⟨158006327126880929647591705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210675102835841239530122273 158006327126880929647591705)
      ·
        refine ⟨118504745345160697235693779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158006327126880929647591705 118504745345160697235693779)
        ·
          refine ⟨177757118017741045853540669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118504745345160697235693779 177757118017741045853540669)
          ·
            refine ⟨66658919256652892195077751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177757118017741045853540669 66658919256652892195077751)
            ·
              refine ⟨99988378884979338292616627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66658919256652892195077751 99988378884979338292616627)
              ·
                refine ⟨149982568327469007438924941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99988378884979338292616627 149982568327469007438924941)
                ·
                  refine ⟨56243463122800877789596853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149982568327469007438924941 56243463122800877789596853)
                  ·
                    refine ⟨5272824667762582292774705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56243463122800877789596853 5272824667762582292774705)
                    ·
                      refine ⟨3954618500821936719581029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272824667762582292774705 3954618500821936719581029)
                      ·
                        rfl

theorem cell23_7701592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_7701592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701592 prefixEnd_7701592 := by exact prefixLift 7701592
  have htrace : WordTrace (prefixWord ++ tailWord_7701592) baseStart_7701592 baseEnd_7701592 := by
    simpa [prefixWord, tailWord_7701592, baseEnd_7701592] using wordTrace_append hprefix tailTrace_7701592
  have hstable : (prefixWord ++ tailWord_7701592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701592).length < 2 ^ (prefixWord ++ tailWord_7701592).sum := by decide
  have hdescent : baseEnd_7701592 < baseStart_7701592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701615 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 3, 6]
def baseStart_7701615 : Nat := 118140960795 + 7701615 * 2 ^ 59
def prefixEnd_7701615 : Nat := 4983230072969 + 3 ^ 40 * 7701615 * 2
def baseEnd_7701615 : Nat := 1318210103625663376531141

theorem tailTrace_7701615 : CollatzResearch.WordTrace tailWord_7701615 prefixEnd_7701615 1318210103625663376531141 := by
  unfold tailWord_7701615
  simp only [CollatzResearch.WordTrace]
  refine ⟨280900975993371660968250299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187267317328914440645500199 280900975993371660968250299)
  ·
    refine ⟨421351463990057491452375449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280900975993371660968250299 421351463990057491452375449)
    ·
      refine ⟨316013597992543118589281587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421351463990057491452375449 316013597992543118589281587)
      ·
        refine ⟨474020396988814677883922381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316013597992543118589281587 474020396988814677883922381)
        ·
          refine ⟨177757648870805504206470893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474020396988814677883922381 177757648870805504206470893)
          ·
            refine ⟨66659118326552064077426585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177757648870805504206470893 66659118326552064077426585)
            ·
              refine ⟨49994338744914048058069939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66659118326552064077426585 49994338744914048058069939)
              ·
                refine ⟨74991508117371072087104909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49994338744914048058069939 74991508117371072087104909)
                ·
                  refine ⟨28121815544014152032664341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74991508117371072087104909 28121815544014152032664341)
                  ·
                    refine ⟨1318210103625663376531141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28121815544014152032664341 1318210103625663376531141)
                    ·
                      rfl

theorem cell23_7701615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_7701615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701615 prefixEnd_7701615 := by exact prefixLift 7701615
  have htrace : WordTrace (prefixWord ++ tailWord_7701615) baseStart_7701615 baseEnd_7701615 := by
    simpa [prefixWord, tailWord_7701615, baseEnd_7701615] using wordTrace_append hprefix tailTrace_7701615
  have hstable : (prefixWord ++ tailWord_7701615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701615).length < 2 ^ (prefixWord ++ tailWord_7701615).sum := by decide
  have hdescent : baseEnd_7701615 < baseStart_7701615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701632 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 4, 4]
def baseStart_7701632 : Nat := 118140960795 + 7701632 * 2 ^ 59
def prefixEnd_7701632 : Nat := 4983230072969 + 3 ^ 40 * 7701632 * 2
def baseEnd_7701632 : Nat := 1318213013349372187693615

theorem tailTrace_7701632 : CollatzResearch.WordTrace tailWord_7701632 prefixEnd_7701632 1318213013349372187693615 := by
  unfold tailWord_7701632
  simp only [CollatzResearch.WordTrace]
  refine ⟨140450798017155036435809575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187267730689540048581079433 140450798017155036435809575)
  ·
    refine ⟨210676197025732554653714363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140450798017155036435809575 210676197025732554653714363)
    ·
      refine ⟨316014295538598831980571545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210676197025732554653714363 316014295538598831980571545)
      ·
        refine ⟨237010721653949123985428659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316014295538598831980571545 237010721653949123985428659)
        ·
          refine ⟨355516082480923685978142989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237010721653949123985428659 355516082480923685978142989)
          ·
            refine ⟨133318530930346382241803621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355516082480923685978142989 133318530930346382241803621)
            ·
              refine ⟨24997224549439946670338179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133318530930346382241803621 24997224549439946670338179)
              ·
                refine ⟨37495836824159920005507269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24997224549439946670338179 37495836824159920005507269)
                ·
                  refine ⟨7030469404529985001032613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37495836824159920005507269 7030469404529985001032613)
                  ·
                    refine ⟨1318213013349372187693615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7030469404529985001032613 1318213013349372187693615)
                    ·
                      rfl

theorem cell23_7701632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 4].length) (baseStart_7701632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701632 prefixEnd_7701632 := by exact prefixLift 7701632
  have htrace : WordTrace (prefixWord ++ tailWord_7701632) baseStart_7701632 baseEnd_7701632 := by
    simpa [prefixWord, tailWord_7701632, baseEnd_7701632] using wordTrace_append hprefix tailTrace_7701632
  have hstable : (prefixWord ++ tailWord_7701632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701632).length < 2 ^ (prefixWord ++ tailWord_7701632).sum := by decide
  have hdescent : baseEnd_7701632 < baseStart_7701632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701635 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 6]
def baseStart_7701635 : Nat := 118140960795 + 7701635 * 2 ^ 59
def prefixEnd_7701635 : Nat := 4983230072969 + 3 ^ 40 * 7701635 * 2
def baseEnd_7701635 : Nat := 3954640580490080051343331

theorem tailTrace_7701635 : CollatzResearch.WordTrace tailWord_7701635 prefixEnd_7701635 3954640580490080051343331 := by
  unfold tailWord_7701635
  simp only [CollatzResearch.WordTrace]
  refine ⟨280901705453299204383978359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187267803635532802922652239 280901705453299204383978359)
  ·
    refine ⟨421352558179948806575967539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280901705453299204383978359 421352558179948806575967539)
    ·
      refine ⟨632028837269923209863951309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421352558179948806575967539 632028837269923209863951309)
      ·
        refine ⟨237010813976221203698981741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 632028837269923209863951309 237010813976221203698981741)
        ·
          refine ⟨88879055241082951387118153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237010813976221203698981741 88879055241082951387118153)
          ·
            refine ⟨66659291430812213540338615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88879055241082951387118153 66659291430812213540338615)
            ·
              refine ⟨99988937146218320310507923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66659291430812213540338615 99988937146218320310507923)
              ·
                refine ⟨149983405719327480465761885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99988937146218320310507923 149983405719327480465761885)
                ·
                  refine ⟨56243777144747805174660707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149983405719327480465761885 56243777144747805174660707)
                  ·
                    refine ⟨84365665717121707761991061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56243777144747805174660707 84365665717121707761991061)
                    ·
                      refine ⟨3954640580490080051343331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84365665717121707761991061 3954640580490080051343331)
                      ·
                        rfl

theorem cell23_7701635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_7701635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701635 prefixEnd_7701635 := by exact prefixLift 7701635
  have htrace : WordTrace (prefixWord ++ tailWord_7701635) baseStart_7701635 baseEnd_7701635 := by
    simpa [prefixWord, tailWord_7701635, baseEnd_7701635] using wordTrace_append hprefix tailTrace_7701635
  have hstable : (prefixWord ++ tailWord_7701635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701635).length < 2 ^ (prefixWord ++ tailWord_7701635).sum := by decide
  have hdescent : baseEnd_7701635 < baseStart_7701635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701642 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_7701642 : Nat := 118140960795 + 7701642 * 2 ^ 59
def prefixEnd_7701642 : Nat := 4983230072969 + 3 ^ 40 * 7701642 * 2
def baseEnd_7701642 : Nat := 3954644174854661523955799

theorem tailTrace_7701642 : CollatzResearch.WordTrace tailWord_7701642 prefixEnd_7701642 3954644174854661523955799 := by
  unfold tailWord_7701642
  simp only [CollatzResearch.WordTrace]
  refine ⟨70225490191068461144870795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187267973842849229719655453 70225490191068461144870795)
  ·
    refine ⟨105338235286602691717306193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70225490191068461144870795 105338235286602691717306193)
    ·
      refine ⟨79003676464952018787979645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105338235286602691717306193 79003676464952018787979645)
      ·
        refine ⟨29626378674357007045492367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79003676464952018787979645 29626378674357007045492367)
        ·
          refine ⟨44439568011535510568238551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29626378674357007045492367 44439568011535510568238551)
          ·
            refine ⟨66659352017303265852357827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44439568011535510568238551 66659352017303265852357827)
            ·
              refine ⟨99989028025954898778536741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66659352017303265852357827 99989028025954898778536741)
              ·
                refine ⟨18747942754866543520975639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99989028025954898778536741 18747942754866543520975639)
                ·
                  refine ⟨28121914132299815281463459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18747942754866543520975639 28121914132299815281463459)
                  ·
                    refine ⟨42182871198449722922195189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28121914132299815281463459 42182871198449722922195189)
                    ·
                      refine ⟨3954644174854661523955799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42182871198449722922195189 3954644174854661523955799)
                      ·
                        rfl

theorem cell23_7701642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_7701642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701642 prefixEnd_7701642 := by exact prefixLift 7701642
  have htrace : WordTrace (prefixWord ++ tailWord_7701642) baseStart_7701642 baseEnd_7701642 := by
    simpa [prefixWord, tailWord_7701642, baseEnd_7701642] using wordTrace_append hprefix tailTrace_7701642
  have hstable : (prefixWord ++ tailWord_7701642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701642).length < 2 ^ (prefixWord ++ tailWord_7701642).sum := by decide
  have hdescent : baseEnd_7701642 < baseStart_7701642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701656 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_7701656 : Nat := 118140960795 + 7701656 * 2 ^ 59
def prefixEnd_7701656 : Nat := 4983230072969 + 3 ^ 40 * 7701656 * 2
def baseEnd_7701656 : Nat := 3954651363583824469180735

theorem tailTrace_7701656 : CollatzResearch.WordTrace tailWord_7701656 prefixEnd_7701656 3954651363583824469180735 := by
  unfold tailWord_7701656
  simp only [CollatzResearch.WordTrace]
  refine ⟨140451235693111562485246411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187268314257482083313661881 140451235693111562485246411)
  ·
    refine ⟨210676853539667343727869617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140451235693111562485246411 210676853539667343727869617)
    ·
      refine ⟨158007640154750507795902213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210676853539667343727869617 158007640154750507795902213)
      ·
        refine ⟨29626432529015720211731665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158007640154750507795902213 29626432529015720211731665)
        ·
          refine ⟨22219824396761790158798749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29626432529015720211731665 22219824396761790158798749)
          ·
            refine ⟨8332434148785671309549531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22219824396761790158798749 8332434148785671309549531)
            ·
              refine ⟨12498651223178506964324297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8332434148785671309549531 12498651223178506964324297)
              ·
                refine ⟨9373988417383880223243223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12498651223178506964324297 9373988417383880223243223)
                ·
                  refine ⟨14060982626075820334864835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9373988417383880223243223 14060982626075820334864835)
                  ·
                    refine ⟨21091473939113730502297253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14060982626075820334864835 21091473939113730502297253)
                    ·
                      refine ⟨3954651363583824469180735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21091473939113730502297253 3954651363583824469180735)
                      ·
                        rfl

theorem cell23_7701656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_7701656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701656 prefixEnd_7701656 := by exact prefixLift 7701656
  have htrace : WordTrace (prefixWord ++ tailWord_7701656) baseStart_7701656 baseEnd_7701656 := by
    simpa [prefixWord, tailWord_7701656, baseEnd_7701656] using wordTrace_append hprefix tailTrace_7701656
  have hstable : (prefixWord ++ tailWord_7701656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701656).length < 2 ^ (prefixWord ++ tailWord_7701656).sum := by decide
  have hdescent : baseEnd_7701656 < baseStart_7701656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701692 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_7701692 : Nat := 118140960795 + 7701692 * 2 ^ 59
def prefixEnd_7701692 : Nat := 4983230072969 + 3 ^ 40 * 7701692 * 2
def baseEnd_7701692 : Nat := 1318223282962462109443523

theorem tailTrace_7701692 : CollatzResearch.WordTrace tailWord_7701692 prefixEnd_7701692 1318223282962462109443523 := by
  unfold tailWord_7701692
  simp only [CollatzResearch.WordTrace]
  refine ⟨140451892207046351559401665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187269189609395135412535553 140451892207046351559401665)
  ·
    refine ⟨105338919155284763669551249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140451892207046351559401665 105338919155284763669551249)
    ·
      refine ⟨79004189366463572752163437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105338919155284763669551249 79004189366463572752163437)
      ·
        refine ⟨29626571012423839782061289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79004189366463572752163437 29626571012423839782061289)
        ·
          refine ⟨22219928259317879836545967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29626571012423839782061289 22219928259317879836545967)
          ·
            refine ⟨33329892388976819754818951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22219928259317879836545967 33329892388976819754818951)
            ·
              refine ⟨49994838583465229632228427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33329892388976819754818951 49994838583465229632228427)
              ·
                refine ⟨74992257875197844448342641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49994838583465229632228427 74992257875197844448342641)
                ·
                  refine ⟨56244193406398383336256981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74992257875197844448342641 56244193406398383336256981)
                  ·
                    refine ⟨1318223282962462109443523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56244193406398383336256981 1318223282962462109443523)
                    ·
                      rfl

theorem cell23_7701692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_7701692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701692 prefixEnd_7701692 := by exact prefixLift 7701692
  have htrace : WordTrace (prefixWord ++ tailWord_7701692) baseStart_7701692 baseEnd_7701692 := by
    simpa [prefixWord, tailWord_7701692, baseEnd_7701692] using wordTrace_append hprefix tailTrace_7701692
  have hstable : (prefixWord ++ tailWord_7701692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701692).length < 2 ^ (prefixWord ++ tailWord_7701692).sum := by decide
  have hdescent : baseEnd_7701692 < baseStart_7701692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701706 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_7701706 : Nat := 118140960795 + 7701706 * 2 ^ 59
def prefixEnd_7701706 : Nat := 4983230072969 + 3 ^ 40 * 7701706 * 2
def baseEnd_7701706 : Nat := 3954677037616549273555505

theorem tailTrace_7701706 : CollatzResearch.WordTrace tailWord_7701706 prefixEnd_7701706 3954677037616549273555505 := by
  unfold tailWord_7701706
  simp only [CollatzResearch.WordTrace]
  refine ⟨70226073759010495877453243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187269530024027989006541981 70226073759010495877453243)
  ·
    refine ⟨105339110638515743816179865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70226073759010495877453243 105339110638515743816179865)
    ·
      refine ⟨79004332978886807862134899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105339110638515743816179865 79004332978886807862134899)
      ·
        refine ⟨118506499468330211793202349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79004332978886807862134899 118506499468330211793202349)
        ·
          refine ⟨44439937300623829422450881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118506499468330211793202349 44439937300623829422450881)
          ·
            refine ⟨33329952975467872066838161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44439937300623829422450881 33329952975467872066838161)
            ·
              refine ⟨24997464731600904050128621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33329952975467872066838161 24997464731600904050128621)
              ·
                refine ⟨9374049274350339018798233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24997464731600904050128621 9374049274350339018798233)
                ·
                  refine ⟨7030536955762754264098675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9374049274350339018798233 7030536955762754264098675)
                  ·
                    refine ⟨10545805433644131396148013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7030536955762754264098675 10545805433644131396148013)
                    ·
                      refine ⟨3954677037616549273555505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10545805433644131396148013 3954677037616549273555505)
                      ·
                        rfl

theorem cell23_7701706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_7701706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701706 prefixEnd_7701706 := by exact prefixLift 7701706
  have htrace : WordTrace (prefixWord ++ tailWord_7701706) baseStart_7701706 baseEnd_7701706 := by
    simpa [prefixWord, tailWord_7701706, baseEnd_7701706] using wordTrace_append hprefix tailTrace_7701706
  have hstable : (prefixWord ++ tailWord_7701706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701706).length < 2 ^ (prefixWord ++ tailWord_7701706).sum := by decide
  have hdescent : baseEnd_7701706 < baseStart_7701706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701732 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_7701732 : Nat := 118140960795 + 7701732 * 2 ^ 59
def prefixEnd_7701732 : Nat := 4983230072969 + 3 ^ 40 * 7701732 * 2
def baseEnd_7701732 : Nat := 3954690388113566171830385

theorem tailTrace_7701732 : CollatzResearch.WordTrace tailWord_7701732 prefixEnd_7701732 3954690388113566171830385 := by
  unfold tailWord_7701732
  simp only [CollatzResearch.WordTrace]
  refine ⟨140452621666973894975129725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187270162222631859966839633 140452621666973894975129725)
  ·
    refine ⟨52669733125115210615673647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140452621666973894975129725 52669733125115210615673647)
    ·
      refine ⟨79004599687672815923510471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52669733125115210615673647 79004599687672815923510471)
      ·
        refine ⟨118506899531509223885265707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79004599687672815923510471 118506899531509223885265707)
        ·
          refine ⟨177760349297263835827898561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118506899531509223885265707 177760349297263835827898561)
          ·
            refine ⟨133320261972947876870923921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177760349297263835827898561 133320261972947876870923921)
            ·
              refine ⟨99990196479710907653192941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133320261972947876870923921 99990196479710907653192941)
              ·
                refine ⟨37496323679891590369947353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99990196479710907653192941 37496323679891590369947353)
                ·
                  refine ⟨28122242759918692777460515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37496323679891590369947353 28122242759918692777460515)
                  ·
                    refine ⟨42183364139878039166190773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28122242759918692777460515 42183364139878039166190773)
                    ·
                      refine ⟨3954690388113566171830385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42183364139878039166190773 3954690388113566171830385)
                      ·
                        rfl

theorem cell23_7701732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_7701732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701732 prefixEnd_7701732 := by exact prefixLift 7701732
  have htrace : WordTrace (prefixWord ++ tailWord_7701732) baseStart_7701732 baseEnd_7701732 := by
    simpa [prefixWord, tailWord_7701732, baseEnd_7701732] using wordTrace_append hprefix tailTrace_7701732
  have hstable : (prefixWord ++ tailWord_7701732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701732).length < 2 ^ (prefixWord ++ tailWord_7701732).sum := by decide
  have hdescent : baseEnd_7701732 < baseStart_7701732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701733 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 1, 3, 2]
def baseStart_7701733 : Nat := 118140960795 + 7701733 * 2 ^ 59
def prefixEnd_7701733 : Nat := 4983230072969 + 3 ^ 40 * 7701733 * 2
def baseEnd_7701733 : Nat := 3954690901594220667917881

theorem tailTrace_7701733 : CollatzResearch.WordTrace tailWord_7701733 prefixEnd_7701733 3954690901594220667917881 := by
  unfold tailWord_7701733
  simp only [CollatzResearch.WordTrace]
  refine ⟨280905279806944167121045853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187270186537962778080697235 280905279806944167121045853)
  ·
    refine ⟨105339479927604062670392195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280905279806944167121045853 105339479927604062670392195)
    ·
      refine ⟨158009219891406094005588293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105339479927604062670392195 158009219891406094005588293)
      ·
        refine ⟨29626728729638642626047805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158009219891406094005588293 29626728729638642626047805)
        ·
          refine ⟨11110023273614490984767927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29626728729638642626047805 11110023273614490984767927)
          ·
            refine ⟨16665034910421736477151891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110023273614490984767927 16665034910421736477151891)
            ·
              refine ⟨24997552365632604715727837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16665034910421736477151891 24997552365632604715727837)
              ·
                refine ⟨9374082137112226768397939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24997552365632604715727837 9374082137112226768397939)
                ·
                  refine ⟨14061123205668340152596909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9374082137112226768397939 14061123205668340152596909)
                  ·
                    refine ⟨5272921202125627557223841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14061123205668340152596909 5272921202125627557223841)
                    ·
                      refine ⟨3954690901594220667917881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272921202125627557223841 3954690901594220667917881)
                      ·
                        rfl

theorem cell23_7701733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_7701733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701733 prefixEnd_7701733 := by exact prefixLift 7701733
  have htrace : WordTrace (prefixWord ++ tailWord_7701733) baseStart_7701733 baseEnd_7701733 := by
    simpa [prefixWord, tailWord_7701733, baseEnd_7701733] using wordTrace_append hprefix tailTrace_7701733
  have hstable : (prefixWord ++ tailWord_7701733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701733).length < 2 ^ (prefixWord ++ tailWord_7701733).sum := by decide
  have hdescent : baseEnd_7701733 < baseStart_7701733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701786 : List Nat := [3, 1, 1, 3, 3, 1, 3, 3, 5]
def baseStart_7701786 : Nat := 118140960795 + 7701786 * 2 ^ 59
def prefixEnd_7701786 : Nat := 4983230072969 + 3 ^ 40 * 7701786 * 2
def baseEnd_7701786 : Nat := 439413124007656551172793

theorem tailTrace_7701786 : CollatzResearch.WordTrace tailWord_7701786 prefixEnd_7701786 439413124007656551172793 := by
  unfold tailWord_7701786
  simp only [CollatzResearch.WordTrace]
  refine ⟨70226803218938039293181303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187271475250501438115150141 70226803218938039293181303)
  ·
    refine ⟨105340204828407058939771955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70226803218938039293181303 105340204828407058939771955)
    ·
      refine ⟨158010307242610588409657933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105340204828407058939771955 158010307242610588409657933)
      ·
        refine ⟨59253865215978970653621725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158010307242610588409657933 59253865215978970653621725)
        ·
          refine ⟨22220199455992113995108147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59253865215978970653621725 22220199455992113995108147)
          ·
            refine ⟨33330299183988170992662221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22220199455992113995108147 33330299183988170992662221)
            ·
              refine ⟨12498862193995564122248333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33330299183988170992662221 12498862193995564122248333)
              ·
                refine ⟨4687073322748336545843125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12498862193995564122248333 4687073322748336545843125)
                ·
                  refine ⟨439413124007656551172793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4687073322748336545843125 439413124007656551172793)
                  ·
                    rfl

theorem cell23_7701786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_7701786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701786 prefixEnd_7701786 := by exact prefixLift 7701786
  have htrace : WordTrace (prefixWord ++ tailWord_7701786) baseStart_7701786 baseEnd_7701786 := by
    simpa [prefixWord, tailWord_7701786, baseEnd_7701786] using wordTrace_append hprefix tailTrace_7701786
  have hstable : (prefixWord ++ tailWord_7701786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701786).length < 2 ^ (prefixWord ++ tailWord_7701786).sum := by decide
  have hdescent : baseEnd_7701786 < baseStart_7701786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701809 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_7701809 : Nat := 118140960795 + 7701809 * 2 ^ 59
def prefixEnd_7701809 : Nat := 4983230072969 + 3 ^ 40 * 7701809 * 2
def baseEnd_7701809 : Nat := 3954729926123962370567531

theorem tailTrace_7701809 : CollatzResearch.WordTrace tailWord_7701809 prefixEnd_7701809 3954729926123962370567531 := by
  unfold tailWord_7701809
  simp only [CollatzResearch.WordTrace]
  refine ⟨280908051754668832100812481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187272034503112554733874987 280908051754668832100812481)
  ·
    refine ⟨210681038816001624075609361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280908051754668832100812481 210681038816001624075609361)
    ·
      refine ⟨158010779112001218056707021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210681038816001624075609361 158010779112001218056707021)
      ·
        refine ⟨59254042167000456771265133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158010779112001218056707021 59254042167000456771265133)
        ·
          refine ⟨22220265812625171289224425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59254042167000456771265133 22220265812625171289224425)
          ·
            refine ⟨16665199359468878466918319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22220265812625171289224425 16665199359468878466918319)
            ·
              refine ⟨24997799039203317700377479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16665199359468878466918319 24997799039203317700377479)
              ·
                refine ⟨37496698558804976550566219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24997799039203317700377479 37496698558804976550566219)
                ·
                  refine ⟨56245047838207464825849329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37496698558804976550566219 56245047838207464825849329)
                  ·
                    refine ⟨42183785878655598619386997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56245047838207464825849329 42183785878655598619386997)
                    ·
                      refine ⟨3954729926123962370567531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42183785878655598619386997 3954729926123962370567531)
                      ·
                        rfl

theorem cell23_7701809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_7701809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701809 prefixEnd_7701809 := by exact prefixLift 7701809
  have htrace : WordTrace (prefixWord ++ tailWord_7701809) baseStart_7701809 baseEnd_7701809 := by
    simpa [prefixWord, tailWord_7701809, baseEnd_7701809] using wordTrace_append hprefix tailTrace_7701809
  have hstable : (prefixWord ++ tailWord_7701809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701809).length < 2 ^ (prefixWord ++ tailWord_7701809).sum := by decide
  have hdescent : baseEnd_7701809 < baseStart_7701809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701819 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 8, 4, 2]
def baseStart_7701819 : Nat := 118140960795 + 7701819 * 2 ^ 59
def prefixEnd_7701819 : Nat := 4983230072969 + 3 ^ 40 * 7701819 * 2
def baseEnd_7701819 : Nat := 3954735060930507331442485

theorem tailTrace_7701819 : CollatzResearch.WordTrace tailWord_7701819 prefixEnd_7701819 3954735060930507331442485 := by
  unfold tailWord_7701819
  simp only [CollatzResearch.WordTrace]
  refine ⟨280908416484632603808676511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187272277656421735872451007 280908416484632603808676511)
  ·
    refine ⟨421362624726948905713014767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280908416484632603808676511 421362624726948905713014767)
    ·
      refine ⟨632043937090423358569522151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421362624726948905713014767 632043937090423358569522151)
      ·
        refine ⟨948065905635635037854283227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632043937090423358569522151 948065905635635037854283227)
        ·
          refine ⟨1422098858453452556781424841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948065905635635037854283227 1422098858453452556781424841)
          ·
            refine ⟨1066574143840089417586068631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422098858453452556781424841 1066574143840089417586068631)
            ·
              refine ⟨1599861215760134126379102947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066574143840089417586068631 1599861215760134126379102947)
              ·
                refine ⟨2399791823640201189568654421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599861215760134126379102947 2399791823640201189568654421)
                ·
                  refine ⟨28122560433283607690257669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2399791823640201189568654421 28122560433283607690257669)
                  ·
                    refine ⟨5272980081240676441923313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28122560433283607690257669 5272980081240676441923313)
                    ·
                      refine ⟨3954735060930507331442485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5272980081240676441923313 3954735060930507331442485)
                      ·
                        rfl

theorem cell23_7701819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 4, 2].length) (baseStart_7701819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701819 prefixEnd_7701819 := by exact prefixLift 7701819
  have htrace : WordTrace (prefixWord ++ tailWord_7701819) baseStart_7701819 baseEnd_7701819 := by
    simpa [prefixWord, tailWord_7701819, baseEnd_7701819] using wordTrace_append hprefix tailTrace_7701819
  have hstable : (prefixWord ++ tailWord_7701819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701819).length < 2 ^ (prefixWord ++ tailWord_7701819).sum := by decide
  have hdescent : baseEnd_7701819 < baseStart_7701819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701829 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_7701829 : Nat := 118140960795 + 7701829 * 2 ^ 59
def prefixEnd_7701829 : Nat := 4983230072969 + 3 ^ 40 * 7701829 * 2
def baseEnd_7701829 : Nat := 1318246731912350764105813

theorem tailTrace_7701829 : CollatzResearch.WordTrace tailWord_7701829 prefixEnd_7701829 1318246731912350764105813 := by
  unfold tailWord_7701829
  simp only [CollatzResearch.WordTrace]
  refine ⟨280908781214596375516540541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187272520809730917011027027 280908781214596375516540541)
  ·
    refine ⟨105340792955473640818702703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280908781214596375516540541 105340792955473640818702703)
    ·
      refine ⟨158011189433210461228054055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105340792955473640818702703 158011189433210461228054055)
      ·
        refine ⟨237016784149815691842081083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158011189433210461228054055 237016784149815691842081083)
        ·
          refine ⟨355525176224723537763121625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237016784149815691842081083 355525176224723537763121625)
          ·
            refine ⟨266643882168542653322341219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355525176224723537763121625 266643882168542653322341219)
            ·
              refine ⟨399965823252813979983511829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266643882168542653322341219 399965823252813979983511829)
              ·
                refine ⟨18748397964975655311727117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 399965823252813979983511829 18748397964975655311727117)
                ·
                  refine ⟨7030649236865870741897669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18748397964975655311727117 7030649236865870741897669)
                  ·
                    refine ⟨1318246731912350764105813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7030649236865870741897669 1318246731912350764105813)
                    ·
                      rfl

theorem cell23_7701829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_7701829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701829 prefixEnd_7701829 := by exact prefixLift 7701829
  have htrace : WordTrace (prefixWord ++ tailWord_7701829) baseStart_7701829 baseEnd_7701829 := by
    simpa [prefixWord, tailWord_7701829, baseEnd_7701829] using wordTrace_append hprefix tailTrace_7701829
  have hstable : (prefixWord ++ tailWord_7701829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701829).length < 2 ^ (prefixWord ++ tailWord_7701829).sum := by decide
  have hdescent : baseEnd_7701829 < baseStart_7701829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701832 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_7701832 : Nat := 118140960795 + 7701832 * 2 ^ 59
def prefixEnd_7701832 : Nat := 4983230072969 + 3 ^ 40 * 7701832 * 2
def baseEnd_7701832 : Nat := 3954741736179015780579925

theorem tailTrace_7701832 : CollatzResearch.WordTrace tailWord_7701832 prefixEnd_7701832 3954741736179015780579925 := by
  unfold tailWord_7701832
  simp only [CollatzResearch.WordTrace]
  refine ⟨140454445316792753514449875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187272593755723671352599833 140454445316792753514449875)
  ·
    refine ⟨210681667975189130271674813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140454445316792753514449875 210681667975189130271674813)
    ·
      refine ⟨79005625490695923851878055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210681667975189130271674813 79005625490695923851878055)
      ·
        refine ⟨118508438236043885777817083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79005625490695923851878055 118508438236043885777817083)
        ·
          refine ⟨177762657354065828666725625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118508438236043885777817083 177762657354065828666725625)
          ·
            refine ⟨133321993015549371500044219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177762657354065828666725625 133321993015549371500044219)
            ·
              refine ⟨199982989523324057250066329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133321993015549371500044219 199982989523324057250066329)
              ·
                refine ⟨149987242142493042937549747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199982989523324057250066329 149987242142493042937549747)
                ·
                  refine ⟨224980863213739564406324621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149987242142493042937549747 224980863213739564406324621)
                  ·
                    refine ⟨84367823705152336652371733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224980863213739564406324621 84367823705152336652371733)
                    ·
                      refine ⟨3954741736179015780579925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84367823705152336652371733 3954741736179015780579925)
                      ·
                        rfl

theorem cell23_7701832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_7701832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701832 prefixEnd_7701832 := by exact prefixLift 7701832
  have htrace : WordTrace (prefixWord ++ tailWord_7701832) baseStart_7701832 baseEnd_7701832 := by
    simpa [prefixWord, tailWord_7701832, baseEnd_7701832] using wordTrace_append hprefix tailTrace_7701832
  have hstable : (prefixWord ++ tailWord_7701832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701832).length < 2 ^ (prefixWord ++ tailWord_7701832).sum := by decide
  have hdescent : baseEnd_7701832 < baseStart_7701832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701836 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_7701836 : Nat := 118140960795 + 7701836 * 2 ^ 59
def prefixEnd_7701836 : Nat := 4983230072969 + 3 ^ 40 * 7701836 * 2
def baseEnd_7701836 : Nat := 3954743790101633764929907

theorem tailTrace_7701836 : CollatzResearch.WordTrace tailWord_7701836 prefixEnd_7701836 3954743790101633764929907 := by
  unfold tailWord_7701836
  simp only [CollatzResearch.WordTrace]
  refine ⟨140454518262785507856022681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187272691017047343808030241 140454518262785507856022681)
  ·
    refine ⟨105340888697089130892017011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140454518262785507856022681 105340888697089130892017011)
    ·
      refine ⟨158011333045633696338025517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105340888697089130892017011 158011333045633696338025517)
      ·
        refine ⟨59254249892112636126759569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158011333045633696338025517 59254249892112636126759569)
        ·
          refine ⟨44440687419084477095069677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59254249892112636126759569 44440687419084477095069677)
          ·
            refine ⟨16665257782156678910651129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44440687419084477095069677 16665257782156678910651129)
            ·
              refine ⟨12498943336617509182988347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16665257782156678910651129 12498943336617509182988347)
              ·
                refine ⟨18748415004926263774482521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12498943336617509182988347 18748415004926263774482521)
                ·
                  refine ⟨14061311253694697830861891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18748415004926263774482521 14061311253694697830861891)
                  ·
                    refine ⟨21091966880542046746292837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14061311253694697830861891 21091966880542046746292837)
                    ·
                      refine ⟨3954743790101633764929907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21091966880542046746292837 3954743790101633764929907)
                      ·
                        rfl

theorem cell23_7701836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_7701836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701836 prefixEnd_7701836 := by exact prefixLift 7701836
  have htrace : WordTrace (prefixWord ++ tailWord_7701836) baseStart_7701836 baseEnd_7701836 := by
    simpa [prefixWord, tailWord_7701836, baseEnd_7701836] using wordTrace_append hprefix tailTrace_7701836
  have hstable : (prefixWord ++ tailWord_7701836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701836).length < 2 ^ (prefixWord ++ tailWord_7701836).sum := by decide
  have hdescent : baseEnd_7701836 < baseStart_7701836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701856 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 3]
def baseStart_7701856 : Nat := 118140960795 + 7701856 * 2 ^ 59
def prefixEnd_7701856 : Nat := 4983230072969 + 3 ^ 40 * 7701856 * 2
def baseEnd_7701856 : Nat := 3954754059714723686679815

theorem tailTrace_7701856 : CollatzResearch.WordTrace tailWord_7701856 prefixEnd_7701856 3954754059714723686679815 := by
  unfold tailWord_7701856
  simp only [CollatzResearch.WordTrace]
  refine ⟨140454882992749279563886711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187273177323665706085182281 140454882992749279563886711)
  ·
    refine ⟨210682324489123919345830067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140454882992749279563886711 210682324489123919345830067)
    ·
      refine ⟨316023486733685879018745101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210682324489123919345830067 316023486733685879018745101)
      ·
        refine ⟨118508807525132204632029413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316023486733685879018745101 118508807525132204632029413)
        ·
          refine ⟨22220401410962288368505515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118508807525132204632029413 22220401410962288368505515)
          ·
            refine ⟨33330602116443432552758273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22220401410962288368505515 33330602116443432552758273)
            ·
              refine ⟨24997951587332574414568705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33330602116443432552758273 24997951587332574414568705)
              ·
                refine ⟨18748463690499430810926529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24997951587332574414568705 18748463690499430810926529)
                ·
                  refine ⟨14061347767874573108194897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18748463690499430810926529 14061347767874573108194897)
                  ·
                    refine ⟨10546010825905929831146173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14061347767874573108194897 10546010825905929831146173)
                    ·
                      refine ⟨3954754059714723686679815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10546010825905929831146173 3954754059714723686679815)
                      ·
                        rfl

theorem cell23_7701856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_7701856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701856 prefixEnd_7701856 := by exact prefixLift 7701856
  have htrace : WordTrace (prefixWord ++ tailWord_7701856) baseStart_7701856 baseEnd_7701856 := by
    simpa [prefixWord, tailWord_7701856, baseEnd_7701856] using wordTrace_append hprefix tailTrace_7701856
  have hstable : (prefixWord ++ tailWord_7701856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701856).length < 2 ^ (prefixWord ++ tailWord_7701856).sum := by decide
  have hdescent : baseEnd_7701856 < baseStart_7701856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701859 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 6]
def baseStart_7701859 : Nat := 118140960795 + 7701859 * 2 ^ 59
def prefixEnd_7701859 : Nat := 4983230072969 + 3 ^ 40 * 7701859 * 2
def baseEnd_7701859 : Nat := 439417288906298574993589

theorem tailTrace_7701859 : CollatzResearch.WordTrace tailWord_7701859 prefixEnd_7701859 439417288906298574993589 := by
  unfold tailWord_7701859
  simp only [CollatzResearch.WordTrace]
  refine ⟨280909875404487690640132631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187273250269658460426755087 280909875404487690640132631)
  ·
    refine ⟨421364813106731535960198947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280909875404487690640132631 421364813106731535960198947)
    ·
      refine ⟨632047219660097303940298421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421364813106731535960198947 632047219660097303940298421)
      ·
        refine ⟨59254426843134122244402977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 632047219660097303940298421 59254426843134122244402977)
        ·
          refine ⟨44440820132350591683302233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59254426843134122244402977 44440820132350591683302233)
          ·
            refine ⟨33330615099262943762476675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44440820132350591683302233 33330615099262943762476675)
            ·
              refine ⟨49995922648894415643715013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33330615099262943762476675 49995922648894415643715013)
              ·
                refine ⟨9374235496667702933196565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49995922648894415643715013 9374235496667702933196565)
                ·
                  refine ⟨439417288906298574993589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9374235496667702933196565 439417288906298574993589)
                  ·
                    rfl

theorem cell23_7701859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 6].length) (baseStart_7701859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701859 prefixEnd_7701859 := by exact prefixLift 7701859
  have htrace : WordTrace (prefixWord ++ tailWord_7701859) baseStart_7701859 baseEnd_7701859 := by
    simpa [prefixWord, tailWord_7701859, baseEnd_7701859] using wordTrace_append hprefix tailTrace_7701859
  have hstable : (prefixWord ++ tailWord_7701859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701859).length < 2 ^ (prefixWord ++ tailWord_7701859).sum := by decide
  have hdescent : baseEnd_7701859 < baseStart_7701859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701870 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7701870 : Nat := 118140960795 + 7701870 * 2 ^ 59
def prefixEnd_7701870 : Nat := 4983230072969 + 3 ^ 40 * 7701870 * 2
def baseEnd_7701870 : Nat := 3954761248443886631904751

theorem tailTrace_7701870 : CollatzResearch.WordTrace tailWord_7701870 prefixEnd_7701870 3954761248443886631904751 := by
  unfold tailWord_7701870
  simp only [CollatzResearch.WordTrace]
  refine ⟨35113784575930979939847883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187273517738298559679188709 35113784575930979939847883)
  ·
    refine ⟨52670676863896469909771825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35113784575930979939847883 52670676863896469909771825)
    ·
      refine ⟨39503007647922352432328869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52670676863896469909771825 39503007647922352432328869)
      ·
        refine ⟨7406813933985441081061663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39503007647922352432328869 7406813933985441081061663)
        ·
          refine ⟨11110220900978161621592495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7406813933985441081061663 11110220900978161621592495)
          ·
            refine ⟨16665331351467242432388743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110220900978161621592495 16665331351467242432388743)
            ·
              refine ⟨24997997027200863648583115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16665331351467242432388743 24997997027200863648583115)
              ·
                refine ⟨37496995540801295472874673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24997997027200863648583115 37496995540801295472874673)
                ·
                  refine ⟨28122746655600971604656005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37496995540801295472874673 28122746655600971604656005)
                  ·
                    refine ⟨5273014997925182175873001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28122746655600971604656005 5273014997925182175873001)
                    ·
                      refine ⟨3954761248443886631904751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273014997925182175873001 3954761248443886631904751)
                      ·
                        rfl

theorem cell23_7701870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7701870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701870 prefixEnd_7701870 := by exact prefixLift 7701870
  have htrace : WordTrace (prefixWord ++ tailWord_7701870) baseStart_7701870 baseEnd_7701870 := by
    simpa [prefixWord, tailWord_7701870, baseEnd_7701870] using wordTrace_append hprefix tailTrace_7701870
  have hstable : (prefixWord ++ tailWord_7701870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701870).length < 2 ^ (prefixWord ++ tailWord_7701870).sum := by decide
  have hdescent : baseEnd_7701870 < baseStart_7701870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701890 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7701890 : Nat := 118140960795 + 7701890 * 2 ^ 59
def prefixEnd_7701890 : Nat := 4983230072969 + 3 ^ 40 * 7701890 * 2
def baseEnd_7701890 : Nat := 3954771518056976553654659

theorem tailTrace_7701890 : CollatzResearch.WordTrace tailWord_7701890 prefixEnd_7701890 3954771518056976553654659 := by
  unfold tailWord_7701890
  simp only [CollatzResearch.WordTrace]
  refine ⟨70227751516843845733627781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187274004044916921956340749 70227751516843845733627781)
  ·
    refine ⟨13167703409408221075055209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70227751516843845733627781 13167703409408221075055209)
    ·
      refine ⟨9875777557056165806291407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13167703409408221075055209 9875777557056165806291407)
      ·
        refine ⟨14813666335584248709437111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9875777557056165806291407 14813666335584248709437111)
        ·
          refine ⟨22220499503376373064155667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14813666335584248709437111 22220499503376373064155667)
          ·
            refine ⟨33330749255064559596233501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22220499503376373064155667 33330749255064559596233501)
            ·
              refine ⟨12499030970649209848587563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33330749255064559596233501 12499030970649209848587563)
              ·
                refine ⟨18748546455973814772881345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12499030970649209848587563 18748546455973814772881345)
                ·
                  refine ⟨14061409841980361079661009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18748546455973814772881345 14061409841980361079661009)
                  ·
                    refine ⟨10546057381485270809745757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14061409841980361079661009 10546057381485270809745757)
                    ·
                      refine ⟨3954771518056976553654659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10546057381485270809745757 3954771518056976553654659)
                      ·
                        rfl

theorem cell23_7701890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7701890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701890 prefixEnd_7701890 := by exact prefixLift 7701890
  have htrace : WordTrace (prefixWord ++ tailWord_7701890) baseStart_7701890 baseEnd_7701890 := by
    simpa [prefixWord, tailWord_7701890, baseEnd_7701890] using wordTrace_append hprefix tailTrace_7701890
  have hstable : (prefixWord ++ tailWord_7701890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701890).length < 2 ^ (prefixWord ++ tailWord_7701890).sum := by decide
  have hdescent : baseEnd_7701890 < baseStart_7701890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701943 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 3, 2, 2]
def baseStart_7701943 : Nat := 118140960795 + 7701943 * 2 ^ 59
def prefixEnd_7701943 : Nat := 4983230072969 + 3 ^ 40 * 7701943 * 2
def baseEnd_7701943 : Nat := 3954798732531664846291915

theorem tailTrace_7701943 : CollatzResearch.WordTrace tailWord_7701943 prefixEnd_7701943 3954798732531664846291915 := by
  unfold tailWord_7701943
  simp only [CollatzResearch.WordTrace]
  refine ⟨280912939136183372986190483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187275292757455581990793655 280912939136183372986190483)
  ·
    refine ⟨421369408704275059479285725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280912939136183372986190483 421369408704275059479285725)
    ·
      refine ⟨158013528264103147304732147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421369408704275059479285725 158013528264103147304732147)
      ·
        refine ⟨237020292396154720957098221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158013528264103147304732147 237020292396154720957098221)
        ·
          refine ⟨88882609648558020358911833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237020292396154720957098221 88882609648558020358911833)
          ·
            refine ⟨66661957236418515269183875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88882609648558020358911833 66661957236418515269183875)
            ·
              refine ⟨99992935854627772903775813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66661957236418515269183875 99992935854627772903775813)
              ·
                refine ⟨18748675472742707419457965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99992935854627772903775813 18748675472742707419457965)
                ·
                  refine ⟨7030753302278515282296737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18748675472742707419457965 7030753302278515282296737)
                  ·
                    refine ⟨5273064976708886461722553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7030753302278515282296737 5273064976708886461722553)
                    ·
                      refine ⟨3954798732531664846291915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273064976708886461722553 3954798732531664846291915)
                      ·
                        rfl

theorem cell23_7701943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_7701943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701943 prefixEnd_7701943 := by exact prefixLift 7701943
  have htrace : WordTrace (prefixWord ++ tailWord_7701943) baseStart_7701943 baseEnd_7701943 := by
    simpa [prefixWord, tailWord_7701943, baseEnd_7701943] using wordTrace_append hprefix tailTrace_7701943
  have hstable : (prefixWord ++ tailWord_7701943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701943).length < 2 ^ (prefixWord ++ tailWord_7701943).sum := by decide
  have hdescent : baseEnd_7701943 < baseStart_7701943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701949 : List Nat := [1, 4, 1, 2, 2, 1, 3, 9]
def baseStart_7701949 : Nat := 118140960795 + 7701949 * 2 ^ 59
def prefixEnd_7701949 : Nat := 4983230072969 + 3 ^ 40 * 7701949 * 2
def baseEnd_7701949 : Nat := 146474141237614511956181

theorem tailTrace_7701949 : CollatzResearch.WordTrace tailWord_7701949 prefixEnd_7701949 146474141237614511956181 := by
  unfold tailWord_7701949
  simp only [CollatzResearch.WordTrace]
  refine ⟨280913157974161636010908901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187275438649441090673939267 280913157974161636010908901)
  ·
    refine ⟨52671217120155306752045419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280913157974161636010908901 52671217120155306752045419)
    ·
      refine ⟨79006825680232960128068129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52671217120155306752045419 79006825680232960128068129)
      ·
        refine ⟨59255119260174720096051097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79006825680232960128068129 59255119260174720096051097)
        ·
          refine ⟨44441339445131040072038323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59255119260174720096051097 44441339445131040072038323)
          ·
            refine ⟨66662009167696560108057485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44441339445131040072038323 66662009167696560108057485)
            ·
              refine ⟨24998253437886210040521557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66662009167696560108057485 24998253437886210040521557)
              ·
                refine ⟨146474141237614511956181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24998253437886210040521557 146474141237614511956181)
                ·
                  rfl

theorem cell23_7701949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 9].length) (baseStart_7701949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701949 prefixEnd_7701949 := by exact prefixLift 7701949
  have htrace : WordTrace (prefixWord ++ tailWord_7701949) baseStart_7701949 baseEnd_7701949 := by
    simpa [prefixWord, tailWord_7701949, baseEnd_7701949] using wordTrace_append hprefix tailTrace_7701949
  have hstable : (prefixWord ++ tailWord_7701949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701949).length < 2 ^ (prefixWord ++ tailWord_7701949).sum := by decide
  have hdescent : baseEnd_7701949 < baseStart_7701949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7701997 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_7701997 : Nat := 118140960795 + 7701997 * 2 ^ 59
def prefixEnd_7701997 : Nat := 4983230072969 + 3 ^ 40 * 7701997 * 2
def baseEnd_7701997 : Nat := 3954826460487007635016667

theorem tailTrace_7701997 : CollatzResearch.WordTrace tailWord_7701997 prefixEnd_7701997 3954826460487007635016667 := by
  unfold tailWord_7701997
  simp only [CollatzResearch.WordTrace]
  refine ⟨280914908677987740208656245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187276605785325160139104163 280914908677987740208656245)
  ·
    refine ⟨26335772688561350644561523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280914908677987740208656245 26335772688561350644561523)
    ·
      refine ⟨39503659032842025966842285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26335772688561350644561523 39503659032842025966842285)
      ·
        refine ⟨14813872137315759737565857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39503659032842025966842285 14813872137315759737565857)
        ·
          refine ⟨11110404102986819803174393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14813872137315759737565857 11110404102986819803174393)
          ·
            refine ⟨8332803077240114852380795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11110404102986819803174393 8332803077240114852380795)
            ·
              refine ⟨12499204615860172278571193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8332803077240114852380795 12499204615860172278571193)
              ·
                refine ⟨9374403461895129208928395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12499204615860172278571193 9374403461895129208928395)
                ·
                  refine ⟨14061605192842693813392593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9374403461895129208928395 14061605192842693813392593)
                  ·
                    refine ⟨10546203894632020360044445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14061605192842693813392593 10546203894632020360044445)
                    ·
                      refine ⟨3954826460487007635016667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10546203894632020360044445 3954826460487007635016667)
                      ·
                        rfl

theorem cell23_7701997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_7701997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7701997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7701997 prefixEnd_7701997 := by exact prefixLift 7701997
  have htrace : WordTrace (prefixWord ++ tailWord_7701997) baseStart_7701997 baseEnd_7701997 := by
    simpa [prefixWord, tailWord_7701997, baseEnd_7701997] using wordTrace_append hprefix tailTrace_7701997
  have hstable : (prefixWord ++ tailWord_7701997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7701997).length < 2 ^ (prefixWord ++ tailWord_7701997).sum := by decide
  have hdescent : baseEnd_7701997 < baseStart_7701997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7701997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702003 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 1, 3, 2]
def baseStart_7702003 : Nat := 118140960795 + 7702003 * 2 ^ 59
def prefixEnd_7702003 : Nat := 4983230072969 + 3 ^ 40 * 7702003 * 2
def baseEnd_7702003 : Nat := 3954829541370934611541639

theorem tailTrace_7702003 : CollatzResearch.WordTrace tailWord_7702003 prefixEnd_7702003 3954829541370934611541639 := by
  unfold tailWord_7702003
  simp only [CollatzResearch.WordTrace]
  refine ⟨280915127515966003233374663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187276751677310668822249775 280915127515966003233374663)
  ·
    refine ⟨421372691273949004850061995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280915127515966003233374663 421372691273949004850061995)
    ·
      refine ⟨632059036910923507275092993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421372691273949004850061995 632059036910923507275092993)
      ·
        refine ⟨474044277683192630456319745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632059036910923507275092993 474044277683192630456319745)
        ·
          refine ⟨355533208262394472842239809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474044277683192630456319745 355533208262394472842239809)
          ·
            refine ⟨266649906196795854631679857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355533208262394472842239809 266649906196795854631679857)
            ·
              refine ⟨199987429647596890973759893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266649906196795854631679857 199987429647596890973759893)
              ·
                refine ⟨9374410764731104264394995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199987429647596890973759893 9374410764731104264394995)
                ·
                  refine ⟨14061616147096656396592493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9374410764731104264394995 14061616147096656396592493)
                  ·
                    refine ⟨5273106055161246148722185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14061616147096656396592493 5273106055161246148722185)
                    ·
                      refine ⟨3954829541370934611541639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273106055161246148722185 3954829541370934611541639)
                      ·
                        rfl

theorem cell23_7702003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 3, 2].length) (baseStart_7702003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702003 prefixEnd_7702003 := by exact prefixLift 7702003
  have htrace : WordTrace (prefixWord ++ tailWord_7702003) baseStart_7702003 baseEnd_7702003 := by
    simpa [prefixWord, tailWord_7702003, baseEnd_7702003] using wordTrace_append hprefix tailTrace_7702003
  have hstable : (prefixWord ++ tailWord_7702003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702003).length < 2 ^ (prefixWord ++ tailWord_7702003).sum := by decide
  have hdescent : baseEnd_7702003 < baseStart_7702003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702009 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 4, 6]
def baseStart_7702009 : Nat := 118140960795 + 7702009 * 2 ^ 59
def prefixEnd_7702009 : Nat := 4983230072969 + 3 ^ 40 * 7702009 * 2
def baseEnd_7702009 : Nat := 1318277540751620529355537

theorem tailTrace_7702009 : CollatzResearch.WordTrace tailWord_7702009 prefixEnd_7702009 1318277540751620529355537 := by
  unfold tailWord_7702009
  simp only [CollatzResearch.WordTrace]
  refine ⟨280915346353944266258093081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187276897569296177505395387 280915346353944266258093081)
  ·
    refine ⟨210686509765458199693569811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280915346353944266258093081 210686509765458199693569811)
    ·
      refine ⟨316029764648187299540354717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210686509765458199693569811 316029764648187299540354717)
      ·
        refine ⟨118511161743070237327633019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316029764648187299540354717 118511161743070237327633019)
        ·
          refine ⟨177766742614605355991449529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118511161743070237327633019 177766742614605355991449529)
          ·
            refine ⟨133325056960954016993587147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177766742614605355991449529 133325056960954016993587147)
            ·
              refine ⟨199987585441431025490380721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133325056960954016993587147 199987585441431025490380721)
              ·
                refine ⟨149990689081073269117785541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199987585441431025490380721 149990689081073269117785541)
                ·
                  refine ⟨28123254202701237959584789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149990689081073269117785541 28123254202701237959584789)
                  ·
                    refine ⟨1318277540751620529355537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28123254202701237959584789 1318277540751620529355537)
                    ·
                      rfl

theorem cell23_7702009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_7702009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702009 prefixEnd_7702009 := by exact prefixLift 7702009
  have htrace : WordTrace (prefixWord ++ tailWord_7702009) baseStart_7702009 baseEnd_7702009 := by
    simpa [prefixWord, tailWord_7702009, baseEnd_7702009] using wordTrace_append hprefix tailTrace_7702009
  have hstable : (prefixWord ++ tailWord_7702009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702009).length < 2 ^ (prefixWord ++ tailWord_7702009).sum := by decide
  have hdescent : baseEnd_7702009 < baseStart_7702009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702014 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7702014 : Nat := 118140960795 + 7702014 * 2 ^ 59
def prefixEnd_7702014 : Nat := 4983230072969 + 3 ^ 40 * 7702014 * 2
def baseEnd_7702014 : Nat := 3954835189658134068504089

theorem tailTrace_7702014 : CollatzResearch.WordTrace tailWord_7702014 prefixEnd_7702014 3954835189658134068504089 := by
  unfold tailWord_7702014
  simp only [CollatzResearch.WordTrace]
  refine ⟨35114441089865769014003137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187277019145950768074683397 35114441089865769014003137)
  ·
    refine ⟨26335830817399326760502353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35114441089865769014003137 26335830817399326760502353)
    ·
      refine ⟨19751873113049495070376765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26335830817399326760502353 19751873113049495070376765)
      ·
        refine ⟨7406952417393560651391287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19751873113049495070376765 7406952417393560651391287)
        ·
          refine ⟨11110428626090340977086931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7406952417393560651391287 11110428626090340977086931)
          ·
            refine ⟨16665642939135511465630397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110428626090340977086931 16665642939135511465630397)
            ·
              refine ⟨6249616102175816799611399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16665642939135511465630397 6249616102175816799611399)
              ·
                refine ⟨9374424153263725199417099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6249616102175816799611399 9374424153263725199417099)
                ·
                  refine ⟨14061636229895587799125649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9374424153263725199417099 14061636229895587799125649)
                  ·
                    refine ⟨10546227172421690849344237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14061636229895587799125649 10546227172421690849344237)
                    ·
                      refine ⟨3954835189658134068504089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10546227172421690849344237 3954835189658134068504089)
                      ·
                        rfl

theorem cell23_7702014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7702014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702014 prefixEnd_7702014 := by exact prefixLift 7702014
  have htrace : WordTrace (prefixWord ++ tailWord_7702014) baseStart_7702014 baseEnd_7702014 := by
    simpa [prefixWord, tailWord_7702014, baseEnd_7702014] using wordTrace_append hprefix tailTrace_7702014
  have hstable : (prefixWord ++ tailWord_7702014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702014).length < 2 ^ (prefixWord ++ tailWord_7702014).sum := by decide
  have hdescent : baseEnd_7702014 < baseStart_7702014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702019 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 5]
def baseStart_7702019 : Nat := 118140960795 + 7702019 * 2 ^ 59
def prefixEnd_7702019 : Nat := 4983230072969 + 3 ^ 40 * 7702019 * 2
def baseEnd_7702019 : Nat := 3954837757061406548941565

theorem tailTrace_7702019 : CollatzResearch.WordTrace tailWord_7702019 prefixEnd_7702019 3954837757061406548941565 := by
  unfold tailWord_7702019
  simp only [CollatzResearch.WordTrace]
  refine ⟨280915711083908037965957111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187277140722605358643971407 280915711083908037965957111)
  ·
    refine ⟨421373566625862056948935667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280915711083908037965957111 421373566625862056948935667)
    ·
      refine ⟨632060349938793085423403501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421373566625862056948935667 632060349938793085423403501)
      ·
        refine ⟨237022631227047407033776313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 632060349938793085423403501 237022631227047407033776313)
        ·
          refine ⟨177766973420285555275332235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237022631227047407033776313 177766973420285555275332235)
          ·
            refine ⟨266650460130428332912998353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177766973420285555275332235 266650460130428332912998353)
            ·
              refine ⟨199987845097821249684748765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266650460130428332912998353 199987845097821249684748765)
              ·
                refine ⟨74995441911682968631780787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199987845097821249684748765 74995441911682968631780787)
                ·
                  refine ⟨112493162867524452947671181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74995441911682968631780787 112493162867524452947671181)
                  ·
                    refine ⟨42184936075321669855376693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112493162867524452947671181 42184936075321669855376693)
                    ·
                      refine ⟨3954837757061406548941565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42184936075321669855376693 3954837757061406548941565)
                      ·
                        rfl

theorem cell23_7702019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_7702019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702019 prefixEnd_7702019 := by exact prefixLift 7702019
  have htrace : WordTrace (prefixWord ++ tailWord_7702019) baseStart_7702019 baseEnd_7702019 := by
    simpa [prefixWord, tailWord_7702019, baseEnd_7702019] using wordTrace_append hprefix tailTrace_7702019
  have hstable : (prefixWord ++ tailWord_7702019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702019).length < 2 ^ (prefixWord ++ tailWord_7702019).sum := by decide
  have hdescent : baseEnd_7702019 < baseStart_7702019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702066 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_7702066 : Nat := 118140960795 + 7702066 * 2 ^ 59
def prefixEnd_7702066 : Nat := 4983230072969 + 3 ^ 40 * 7702066 * 2
def baseEnd_7702066 : Nat := 3954861890652167865053849

theorem tailTrace_7702066 : CollatzResearch.WordTrace tailWord_7702066 prefixEnd_7702066 3954861890652167865053849 := by
  unfold tailWord_7702066
  simp only [CollatzResearch.WordTrace]
  refine ⟨70229356328684441248229513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187278283543158509995278701 70229356328684441248229513)
  ·
    refine ⟨52672017246513330936172135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70229356328684441248229513 52672017246513330936172135)
    ·
      refine ⟨79008025869769996404258203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52672017246513330936172135 79008025869769996404258203)
      ·
        refine ⟨118512038804654994606387305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79008025869769996404258203 118512038804654994606387305)
        ·
          refine ⟨88884029103491245954790479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118512038804654994606387305 88884029103491245954790479)
          ·
            refine ⟨133326043655236868932185719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88884029103491245954790479 133326043655236868932185719)
            ·
              refine ⟨199989065482855303398278579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133326043655236868932185719 199989065482855303398278579)
              ·
                refine ⟨299983598224282955097417869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199989065482855303398278579 299983598224282955097417869)
                ·
                  refine ⟨112493849334106108161531701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299983598224282955097417869 112493849334106108161531701)
                  ·
                    refine ⟨10546298375072447640143597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112493849334106108161531701 10546298375072447640143597)
                    ·
                      refine ⟨3954861890652167865053849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10546298375072447640143597 3954861890652167865053849)
                      ·
                        rfl

theorem cell23_7702066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_7702066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702066 prefixEnd_7702066 := by exact prefixLift 7702066
  have htrace : WordTrace (prefixWord ++ tailWord_7702066) baseStart_7702066 baseEnd_7702066 := by
    simpa [prefixWord, tailWord_7702066, baseEnd_7702066] using wordTrace_append hprefix tailTrace_7702066
  have hstable : (prefixWord ++ tailWord_7702066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702066).length < 2 ^ (prefixWord ++ tailWord_7702066).sum := by decide
  have hdescent : baseEnd_7702066 < baseStart_7702066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702073 : List Nat := [1, 2, 1, 5, 1, 2, 1, 5, 5]
def baseStart_7702073 : Nat := 118140960795 + 7702073 * 2 ^ 59
def prefixEnd_7702073 : Nat := 4983230072969 + 3 ^ 40 * 7702073 * 2
def baseEnd_7702073 : Nat := 439429498335194370851813

theorem tailTrace_7702073 : CollatzResearch.WordTrace tailWord_7702073 prefixEnd_7702073 439429498335194370851813 := by
  unfold tailWord_7702073
  simp only [CollatzResearch.WordTrace]
  refine ⟨280917680625712405188422873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187278453750474936792281915 280917680625712405188422873)
  ·
    refine ⟨210688260469284303891317155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280917680625712405188422873 210688260469284303891317155)
    ·
      refine ⟨316032390703926455836975733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210688260469284303891317155 316032390703926455836975733)
      ·
        refine ⟨29628036628493105234716475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316032390703926455836975733 29628036628493105234716475)
        ·
          refine ⟨44442054942739657852074713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29628036628493105234716475 44442054942739657852074713)
          ·
            refine ⟨33331541207054743389056035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44442054942739657852074713 33331541207054743389056035)
            ·
              refine ⟨49997311810582115083584053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33331541207054743389056035 49997311810582115083584053)
              ·
                refine ⟨4687247982242073289086005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49997311810582115083584053 4687247982242073289086005)
                ·
                  refine ⟨439429498335194370851813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4687247982242073289086005 439429498335194370851813)
                  ·
                    rfl

theorem cell23_7702073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 5].length) (baseStart_7702073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702073 prefixEnd_7702073 := by exact prefixLift 7702073
  have htrace : WordTrace (prefixWord ++ tailWord_7702073) baseStart_7702073 baseEnd_7702073 := by
    simpa [prefixWord, tailWord_7702073, baseEnd_7702073] using wordTrace_append hprefix tailTrace_7702073
  have hstable : (prefixWord ++ tailWord_7702073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702073).length < 2 ^ (prefixWord ++ tailWord_7702073).sum := by decide
  have hdescent : baseEnd_7702073 < baseStart_7702073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702207 : List Nat := [1, 1, 2, 2, 2, 3, 3, 4, 1, 1, 3]
def baseStart_7702207 : Nat := 118140960795 + 7702207 * 2 ^ 59
def prefixEnd_7702207 : Nat := 4983230072969 + 3 ^ 40 * 7702207 * 2
def baseEnd_7702207 : Nat := 3954934291424451813390701

theorem tailTrace_7702207 : CollatzResearch.WordTrace tailWord_7702207 prefixEnd_7702207 3954934291424451813390701 := by
  unfold tailWord_7702207
  simp only [CollatzResearch.WordTrace]
  refine ⟨280922568007226946073800875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187281712004817964049200583 280922568007226946073800875)
  ·
    refine ⟨421383852010840419110701313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280922568007226946073800875 421383852010840419110701313)
    ·
      refine ⟨316037889008130314333025985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421383852010840419110701313 316037889008130314333025985)
      ·
        refine ⟨237028416756097735749769489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316037889008130314333025985 237028416756097735749769489)
        ·
          refine ⟨177771312567073301812327117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237028416756097735749769489 177771312567073301812327117)
          ·
            refine ⟨66664242212652488179622669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177771312567073301812327117 66664242212652488179622669)
            ·
              refine ⟨24999090829744683067358501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66664242212652488179622669 24999090829744683067358501)
              ·
                refine ⟨4687329530577128075129719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24999090829744683067358501 4687329530577128075129719)
                ·
                  refine ⟨7030994295865692112694579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687329530577128075129719 7030994295865692112694579)
                  ·
                    refine ⟨10546491443798538169041869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7030994295865692112694579 10546491443798538169041869)
                    ·
                      refine ⟨3954934291424451813390701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10546491443798538169041869 3954934291424451813390701)
                      ·
                        rfl

theorem cell23_7702207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_7702207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702207 prefixEnd_7702207 := by exact prefixLift 7702207
  have htrace : WordTrace (prefixWord ++ tailWord_7702207) baseStart_7702207 baseEnd_7702207 := by
    simpa [prefixWord, tailWord_7702207, baseEnd_7702207] using wordTrace_append hprefix tailTrace_7702207
  have hstable : (prefixWord ++ tailWord_7702207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702207).length < 2 ^ (prefixWord ++ tailWord_7702207).sum := by decide
  have hdescent : baseEnd_7702207 < baseStart_7702207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702253 : List Nat := [1, 5, 1, 2, 1, 3, 10]
def baseStart_7702253 : Nat := 118140960795 + 7702253 * 2 ^ 59
def prefixEnd_7702253 : Nat := 4983230072969 + 3 ^ 40 * 7702253 * 2
def baseEnd_7702253 : Nat := 48826640883142699177969

theorem tailTrace_7702253 : CollatzResearch.WordTrace tailWord_7702253 prefixEnd_7702253 48826640883142699177969 := by
  unfold tailWord_7702253
  simp only [CollatzResearch.WordTrace]
  refine ⟨280924245765060295929975413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187282830510040197286650275 280924245765060295929975413)
  ·
    refine ⟨26336648040474402743435195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280924245765060295929975413 26336648040474402743435195)
    ·
      refine ⟨39504972060711604115152793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26336648040474402743435195 39504972060711604115152793)
      ·
        refine ⟨29628729045533703086364595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39504972060711604115152793 29628729045533703086364595)
        ·
          refine ⟨44443093568300554629546893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29628729045533703086364595 44443093568300554629546893)
          ·
            refine ⟨16666160088112707986080085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44443093568300554629546893 16666160088112707986080085)
            ·
              refine ⟨48826640883142699177969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16666160088112707986080085 48826640883142699177969)
              ·
                rfl

theorem cell23_7702253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 10].length) (baseStart_7702253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702253 prefixEnd_7702253 := by exact prefixLift 7702253
  have htrace : WordTrace (prefixWord ++ tailWord_7702253) baseStart_7702253 baseEnd_7702253 := by
    simpa [prefixWord, tailWord_7702253, baseEnd_7702253] using wordTrace_append hprefix tailTrace_7702253
  have hstable : (prefixWord ++ tailWord_7702253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702253).length < 2 ^ (prefixWord ++ tailWord_7702253).sum := by decide
  have hdescent : baseEnd_7702253 < baseStart_7702253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702257 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 2, 4]
def baseStart_7702257 : Nat := 118140960795 + 7702257 * 2 ^ 59
def prefixEnd_7702257 : Nat := 4983230072969 + 3 ^ 40 * 7702257 * 2
def baseEnd_7702257 : Nat := 1318319988485725539255157

theorem tailTrace_7702257 : CollatzResearch.WordTrace tailWord_7702257 prefixEnd_7702257 1318319988485725539255157 := by
  unfold tailWord_7702257
  simp only [CollatzResearch.WordTrace]
  refine ⟨280924391657045804613121025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187282927771363869742080683 280924391657045804613121025)
  ·
    refine ⟨210693293742784353459840769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280924391657045804613121025 210693293742784353459840769)
    ·
      refine ⟨158019970307088265094880577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210693293742784353459840769 158019970307088265094880577)
      ·
        refine ⟨118514977730316198821160433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158019970307088265094880577 118514977730316198821160433)
        ·
          refine ⟨88886233297737149115870325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118514977730316198821160433 88886233297737149115870325)
          ·
            refine ⟨8333084371662857729612843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88886233297737149115870325 8333084371662857729612843)
            ·
              refine ⟨12499626557494286594419265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8333084371662857729612843 12499626557494286594419265)
              ·
                refine ⟨9374719918120714945814449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12499626557494286594419265 9374719918120714945814449)
                ·
                  refine ⟨7031039938590536209360837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9374719918120714945814449 7031039938590536209360837)
                  ·
                    refine ⟨1318319988485725539255157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7031039938590536209360837 1318319988485725539255157)
                    ·
                      rfl

theorem cell23_7702257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_7702257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702257 prefixEnd_7702257 := by exact prefixLift 7702257
  have htrace : WordTrace (prefixWord ++ tailWord_7702257) baseStart_7702257 baseEnd_7702257 := by
    simpa [prefixWord, tailWord_7702257, baseEnd_7702257] using wordTrace_append hprefix tailTrace_7702257
  have hstable : (prefixWord ++ tailWord_7702257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702257).length < 2 ^ (prefixWord ++ tailWord_7702257).sum := by decide
  have hdescent : baseEnd_7702257 < baseStart_7702257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702263 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_7702263 : Nat := 118140960795 + 7702263 * 2 ^ 59
def prefixEnd_7702263 : Nat := 4983230072969 + 3 ^ 40 * 7702263 * 2
def baseEnd_7702263 : Nat := 3954963046341103594290443

theorem tailTrace_7702263 : CollatzResearch.WordTrace tailWord_7702263 prefixEnd_7702263 3954963046341103594290443 := by
  unfold tailWord_7702263
  simp only [CollatzResearch.WordTrace]
  refine ⟨280924610495024067637839443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187283073663349378425226295 280924610495024067637839443)
  ·
    refine ⟨421386915742536101456759165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280924610495024067637839443 421386915742536101456759165)
    ·
      refine ⟨158020093403451038046284687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421386915742536101456759165 158020093403451038046284687)
      ·
        refine ⟨237030140105176557069427031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158020093403451038046284687 237030140105176557069427031)
        ·
          refine ⟨355545210157764835604140547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237030140105176557069427031 355545210157764835604140547)
          ·
            refine ⟨533317815236647253406210821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355545210157764835604140547 533317815236647253406210821)
            ·
              refine ⟨99997090356871360013664529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 533317815236647253406210821 99997090356871360013664529)
              ·
                refine ⟨74997817767653520010248397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99997090356871360013664529 74997817767653520010248397)
                ·
                  refine ⟨28124181662870070003843149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74997817767653520010248397 28124181662870070003843149)
                  ·
                    refine ⟨10546568123576276251441181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28124181662870070003843149 10546568123576276251441181)
                    ·
                      refine ⟨3954963046341103594290443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10546568123576276251441181 3954963046341103594290443)
                      ·
                        rfl

theorem cell23_7702263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_7702263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702263 prefixEnd_7702263 := by exact prefixLift 7702263
  have htrace : WordTrace (prefixWord ++ tailWord_7702263) baseStart_7702263 baseEnd_7702263 := by
    simpa [prefixWord, tailWord_7702263, baseEnd_7702263] using wordTrace_append hprefix tailTrace_7702263
  have hstable : (prefixWord ++ tailWord_7702263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702263).length < 2 ^ (prefixWord ++ tailWord_7702263).sum := by decide
  have hdescent : baseEnd_7702263 < baseStart_7702263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702274 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_7702274 : Nat := 118140960795 + 7702274 * 2 ^ 59
def prefixEnd_7702274 : Nat := 4983230072969 + 3 ^ 40 * 7702274 * 2
def baseEnd_7702274 : Nat := 1318322898209434350417631

theorem tailTrace_7702274 : CollatzResearch.WordTrace tailWord_7702274 prefixEnd_7702274 1318322898209434350417631 := by
  unfold tailWord_7702274
  simp only [CollatzResearch.WordTrace]
  refine ⟨70231252924496054129122469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187283341131989477677659917 70231252924496054129122469)
  ·
    refine ⟨13168359923343010149210463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70231252924496054129122469 13168359923343010149210463)
    ·
      refine ⟨19752539885014515223815695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13168359923343010149210463 19752539885014515223815695)
      ·
        refine ⟨29628809827521772835723543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19752539885014515223815695 29628809827521772835723543)
        ·
          refine ⟨44443214741282659253585315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29628809827521772835723543 44443214741282659253585315)
          ·
            refine ⟨66664822111923988880377973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44443214741282659253585315 66664822111923988880377973)
            ·
              refine ⟨6249827072992873957535435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66664822111923988880377973 6249827072992873957535435)
              ·
                refine ⟨9374740609489310936303153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6249827072992873957535435 9374740609489310936303153)
                ·
                  refine ⟨7031055457116983202227365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9374740609489310936303153 7031055457116983202227365)
                  ·
                    refine ⟨1318322898209434350417631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7031055457116983202227365 1318322898209434350417631)
                    ·
                      rfl

theorem cell23_7702274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_7702274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702274 prefixEnd_7702274 := by exact prefixLift 7702274
  have htrace : WordTrace (prefixWord ++ tailWord_7702274) baseStart_7702274 baseEnd_7702274 := by
    simpa [prefixWord, tailWord_7702274, baseEnd_7702274] using wordTrace_append hprefix tailTrace_7702274
  have hstable : (prefixWord ++ tailWord_7702274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702274).length < 2 ^ (prefixWord ++ tailWord_7702274).sum := by decide
  have hdescent : baseEnd_7702274 < baseStart_7702274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702292 : List Nat := [2, 4, 4, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7702292 : Nat := 118140960795 + 7702292 * 2 ^ 59
def prefixEnd_7702292 : Nat := 4983230072969 + 3 ^ 40 * 7702292 * 2
def baseEnd_7702292 : Nat := 3954977937280083980827811

theorem tailTrace_7702292 : CollatzResearch.WordTrace tailWord_7702292 prefixEnd_7702292 3954977937280083980827811 := by
  unfold tailWord_7702292
  simp only [CollatzResearch.WordTrace]
  refine ⟨140462834105959502795322565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187283778807946003727096753 140462834105959502795322565)
  ·
    refine ⟨26336781394867406774122981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140462834105959502795322565 26336781394867406774122981)
    ·
      refine ⟨4938146511537638770148059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26336781394867406774122981 4938146511537638770148059)
      ·
        refine ⟨7407219767306458155222089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938146511537638770148059 7407219767306458155222089)
        ·
          refine ⟨5555414825479843616416567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7407219767306458155222089 5555414825479843616416567)
          ·
            refine ⟨8333122238219765424624851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555414825479843616416567 8333122238219765424624851)
            ·
              refine ⟨12499683357329648136937277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8333122238219765424624851 12499683357329648136937277)
              ·
                refine ⟨4687381258998618051351479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12499683357329648136937277 4687381258998618051351479)
                ·
                  refine ⟨7031071888497927077027219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687381258998618051351479 7031071888497927077027219)
                  ·
                    refine ⟨10546607832746890615540829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7031071888497927077027219 10546607832746890615540829)
                    ·
                      refine ⟨3954977937280083980827811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10546607832746890615540829 3954977937280083980827811)
                      ·
                        rfl

theorem cell23_7702292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7702292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702292 prefixEnd_7702292 := by exact prefixLift 7702292
  have htrace : WordTrace (prefixWord ++ tailWord_7702292) baseStart_7702292 baseEnd_7702292 := by
    simpa [prefixWord, tailWord_7702292, baseEnd_7702292] using wordTrace_append hprefix tailTrace_7702292
  have hstable : (prefixWord ++ tailWord_7702292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702292).length < 2 ^ (prefixWord ++ tailWord_7702292).sum := by decide
  have hdescent : baseEnd_7702292 < baseStart_7702292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702293 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_7702293 : Nat := 118140960795 + 7702293 * 2 ^ 59
def prefixEnd_7702293 : Nat := 4983230072969 + 3 ^ 40 * 7702293 * 2
def baseEnd_7702293 : Nat := 3954978450760738476915305

theorem tailTrace_7702293 : CollatzResearch.WordTrace tailWord_7702293 prefixEnd_7702293 3954978450760738476915305 := by
  unfold tailWord_7702293
  simp only [CollatzResearch.WordTrace]
  refine ⟨280925704684915382761431533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187283803123276921840954355 280925704684915382761431533)
  ·
    refine ⟨105347139256843268535536825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280925704684915382761431533 105347139256843268535536825)
    ·
      refine ⟨79010354442632451401652619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105347139256843268535536825 79010354442632451401652619)
      ·
        refine ⟨118515531663948677102478929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79010354442632451401652619 118515531663948677102478929)
        ·
          refine ⟨88886648747961507826859197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118515531663948677102478929 88886648747961507826859197)
          ·
            refine ⟨33332493280485565435072199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88886648747961507826859197 33332493280485565435072199)
            ·
              refine ⟨49998739920728348152608299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33332493280485565435072199 49998739920728348152608299)
              ·
                refine ⟨74998109881092522228912449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49998739920728348152608299 74998109881092522228912449)
                ·
                  refine ⟨56248582410819391671684337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74998109881092522228912449 56248582410819391671684337)
                  ·
                    refine ⟨42186436808114543753763253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56248582410819391671684337 42186436808114543753763253)
                    ·
                      refine ⟨3954978450760738476915305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42186436808114543753763253 3954978450760738476915305)
                      ·
                        rfl

theorem cell23_7702293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_7702293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702293 prefixEnd_7702293 := by exact prefixLift 7702293
  have htrace : WordTrace (prefixWord ++ tailWord_7702293) baseStart_7702293 baseEnd_7702293 := by
    simpa [prefixWord, tailWord_7702293, baseEnd_7702293] using wordTrace_append hprefix tailTrace_7702293
  have hstable : (prefixWord ++ tailWord_7702293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702293).length < 2 ^ (prefixWord ++ tailWord_7702293).sum := by decide
  have hdescent : baseEnd_7702293 < baseStart_7702293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702307 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 1, 3, 2]
def baseStart_7702307 : Nat := 118140960795 + 7702307 * 2 ^ 59
def prefixEnd_7702307 : Nat := 4983230072969 + 3 ^ 40 * 7702307 * 2
def baseEnd_7702307 : Nat := 3954985639489901422140241

theorem tailTrace_7702307 : CollatzResearch.WordTrace tailWord_7702307 prefixEnd_7702307 3954985639489901422140241 := by
  unfold tailWord_7702307
  simp only [CollatzResearch.WordTrace]
  refine ⟨280926215306864663152441175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187284143537909775434960783 280926215306864663152441175)
  ·
    refine ⟨421389322960296994728661763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280926215306864663152441175 421389322960296994728661763)
    ·
      refine ⟨632083984440445492092992645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421389322960296994728661763 632083984440445492092992645)
      ·
        refine ⟨118515747082583529767436121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 632083984440445492092992645 118515747082583529767436121)
        ·
          refine ⟨88886810311937647325577091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118515747082583529767436121 88886810311937647325577091)
          ·
            refine ⟨133330215467906470988365637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88886810311937647325577091 133330215467906470988365637)
            ·
              refine ⟨24999415400232463310318557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133330215467906470988365637 24999415400232463310318557)
              ·
                refine ⟨9374780775087173741369459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24999415400232463310318557 9374780775087173741369459)
                ·
                  refine ⟨14062171162630760612054189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9374780775087173741369459 14062171162630760612054189)
                  ·
                    refine ⟨5273314185986535229520321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14062171162630760612054189 5273314185986535229520321)
                    ·
                      refine ⟨3954985639489901422140241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273314185986535229520321 3954985639489901422140241)
                      ·
                        rfl

theorem cell23_7702307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_7702307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702307 prefixEnd_7702307 := by exact prefixLift 7702307
  have htrace : WordTrace (prefixWord ++ tailWord_7702307) baseStart_7702307 baseEnd_7702307 := by
    simpa [prefixWord, tailWord_7702307, baseEnd_7702307] using wordTrace_append hprefix tailTrace_7702307
  have hstable : (prefixWord ++ tailWord_7702307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702307).length < 2 ^ (prefixWord ++ tailWord_7702307).sum := by decide
  have hdescent : baseEnd_7702307 < baseStart_7702307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702343 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 7]
def baseStart_7702343 : Nat := 118140960795 + 7702343 * 2 ^ 59
def prefixEnd_7702343 : Nat := 4983230072969 + 3 ^ 40 * 7702343 * 2
def baseEnd_7702343 : Nat := 439444902754829253476675

theorem tailTrace_7702343 : CollatzResearch.WordTrace tailWord_7702343 prefixEnd_7702343 439444902754829253476675 := by
  unfold tailWord_7702343
  simp only [CollatzResearch.WordTrace]
  refine ⟨280927528334734241300751683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187285018889822827533834455 280927528334734241300751683)
  ·
    refine ⟨421391292502101361951127525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280927528334734241300751683 421391292502101361951127525)
    ·
      refine ⟨79010867344144005365836411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421391292502101361951127525 79010867344144005365836411)
      ·
        refine ⟨118516301016216008048754617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79010867344144005365836411 118516301016216008048754617)
        ·
          refine ⟨88887225762162006036565963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118516301016216008048754617 88887225762162006036565963)
          ·
            refine ⟨133330838643243009054848945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88887225762162006036565963 133330838643243009054848945)
            ·
              refine ⟨99998128982432256791136709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133330838643243009054848945 99998128982432256791136709)
              ·
                refine ⟨18749649184206048148338133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99998128982432256791136709 18749649184206048148338133)
                ·
                  refine ⟨439444902754829253476675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18749649184206048148338133 439444902754829253476675)
                  ·
                    rfl

theorem cell23_7702343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 7].length) (baseStart_7702343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702343 prefixEnd_7702343 := by exact prefixLift 7702343
  have htrace : WordTrace (prefixWord ++ tailWord_7702343) baseStart_7702343 baseEnd_7702343 := by
    simpa [prefixWord, tailWord_7702343, baseEnd_7702343] using wordTrace_append hprefix tailTrace_7702343
  have hstable : (prefixWord ++ tailWord_7702343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702343).length < 2 ^ (prefixWord ++ tailWord_7702343).sum := by decide
  have hdescent : baseEnd_7702343 < baseStart_7702343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702371 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 2, 2, 2]
def baseStart_7702371 : Nat := 118140960795 + 7702371 * 2 ^ 59
def prefixEnd_7702371 : Nat := 4983230072969 + 3 ^ 40 * 7702371 * 2
def baseEnd_7702371 : Nat := 3955018502251789171739947

theorem tailTrace_7702371 : CollatzResearch.WordTrace tailWord_7702371 prefixEnd_7702371 3955018502251789171739947 := by
  unfold tailWord_7702371
  simp only [CollatzResearch.WordTrace]
  refine ⟨280928549578632802082770967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187285699719088534721847311 280928549578632802082770967)
  ·
    refine ⟨421392824367949203124156451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280928549578632802082770967 421392824367949203124156451)
    ·
      refine ⟨632089236551923804686234677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421392824367949203124156451 632089236551923804686234677)
      ·
        refine ⟨59258365926742856689334501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 632089236551923804686234677 59258365926742856689334501)
        ·
          refine ⟨11110943611264285629250219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59258365926742856689334501 11110943611264285629250219)
          ·
            refine ⟨16666415416896428443875329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110943611264285629250219 16666415416896428443875329)
            ·
              refine ⟨12499811562672321332906497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16666415416896428443875329 12499811562672321332906497)
              ·
                refine ⟨9374858672004240999679873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12499811562672321332906497 9374858672004240999679873)
                ·
                  refine ⟨7031144004003180749759905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9374858672004240999679873 7031144004003180749759905)
                  ·
                    refine ⟨5273358003002385562319929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7031144004003180749759905 5273358003002385562319929)
                    ·
                      refine ⟨3955018502251789171739947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273358003002385562319929 3955018502251789171739947)
                      ·
                        rfl

theorem cell23_7702371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_7702371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702371 prefixEnd_7702371 := by exact prefixLift 7702371
  have htrace : WordTrace (prefixWord ++ tailWord_7702371) baseStart_7702371 baseEnd_7702371 := by
    simpa [prefixWord, tailWord_7702371, baseEnd_7702371] using wordTrace_append hprefix tailTrace_7702371
  have hstable : (prefixWord ++ tailWord_7702371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702371).length < 2 ^ (prefixWord ++ tailWord_7702371).sum := by decide
  have hdescent : baseEnd_7702371 < baseStart_7702371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702373 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_7702373 : Nat := 118140960795 + 7702373 * 2 ^ 59
def prefixEnd_7702373 : Nat := 4983230072969 + 3 ^ 40 * 7702373 * 2
def baseEnd_7702373 : Nat := 1318339843071032721304979

theorem tailTrace_7702373 : CollatzResearch.WordTrace tailWord_7702373 prefixEnd_7702373 1318339843071032721304979 := by
  unfold tailWord_7702373
  simp only [CollatzResearch.WordTrace]
  refine ⟨280928622524625556424343773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187285748349750370949562515 280928622524625556424343773)
  ·
    refine ⟨105348233446734583659128915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280928622524625556424343773 105348233446734583659128915)
    ·
      refine ⟨158022350170101875488693373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105348233446734583659128915 158022350170101875488693373)
      ·
        refine ⟨59258381313788203308260015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158022350170101875488693373 59258381313788203308260015)
        ·
          refine ⟨88887571970682304962390023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59258381313788203308260015 88887571970682304962390023)
          ·
            refine ⟨133331357956023457443585035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88887571970682304962390023 133331357956023457443585035)
            ·
              refine ⟨199997036934035186165377553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133331357956023457443585035 199997036934035186165377553)
              ·
                refine ⟨149997777700526389624033165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199997036934035186165377553 149997777700526389624033165)
                ·
                  refine ⟨56249166637697396109012437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149997777700526389624033165 56249166637697396109012437)
                  ·
                    refine ⟨1318339843071032721304979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56249166637697396109012437 1318339843071032721304979)
                    ·
                      rfl

theorem cell23_7702373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_7702373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702373 prefixEnd_7702373 := by exact prefixLift 7702373
  have htrace : WordTrace (prefixWord ++ tailWord_7702373) baseStart_7702373 baseEnd_7702373 := by
    simpa [prefixWord, tailWord_7702373, baseEnd_7702373] using wordTrace_append hprefix tailTrace_7702373
  have hstable : (prefixWord ++ tailWord_7702373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702373).length < 2 ^ (prefixWord ++ tailWord_7702373).sum := by decide
  have hdescent : baseEnd_7702373 < baseStart_7702373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702422 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7702422 : Nat := 118140960795 + 7702422 * 2 ^ 59
def prefixEnd_7702422 : Nat := 4983230072969 + 3 ^ 40 * 7702422 * 2
def baseEnd_7702422 : Nat := 3955044689765168472202213

theorem tailTrace_7702422 : CollatzResearch.WordTrace tailWord_7702422 prefixEnd_7702422 3955044689765168472202213 := by
  unfold tailWord_7702422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558150606340502362054845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187286939800965358528585013 17558150606340502362054845)
  ·
    refine ⟨6584306477377688385770567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17558150606340502362054845 6584306477377688385770567)
    ·
      refine ⟨9876459716066532578655851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6584306477377688385770567 9876459716066532578655851)
      ·
        refine ⟨14814689574099798867983777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9876459716066532578655851 14814689574099798867983777)
        ·
          refine ⟨11111017180574849150987833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14814689574099798867983777 11111017180574849150987833)
          ·
            refine ⟨8333262885431136863240875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11111017180574849150987833 8333262885431136863240875)
            ·
              refine ⟨12499894328146705294861313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8333262885431136863240875 12499894328146705294861313)
              ·
                refine ⟨9374920746110028971145985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12499894328146705294861313 9374920746110028971145985)
                ·
                  refine ⟨7031190559582521728359489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9374920746110028971145985 7031190559582521728359489)
                  ·
                    refine ⟨5273392919686891296269617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7031190559582521728359489 5273392919686891296269617)
                    ·
                      refine ⟨3955044689765168472202213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273392919686891296269617 3955044689765168472202213)
                      ·
                        rfl

theorem cell23_7702422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7702422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702422 prefixEnd_7702422 := by exact prefixLift 7702422
  have htrace : WordTrace (prefixWord ++ tailWord_7702422) baseStart_7702422 baseEnd_7702422 := by
    simpa [prefixWord, tailWord_7702422, baseEnd_7702422] using wordTrace_append hprefix tailTrace_7702422
  have hstable : (prefixWord ++ tailWord_7702422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702422).length < 2 ^ (prefixWord ++ tailWord_7702422).sum := by decide
  have hdescent : baseEnd_7702422 < baseStart_7702422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702450 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 6]
def baseStart_7702450 : Nat := 118140960795 + 7702450 * 2 ^ 59
def prefixEnd_7702450 : Nat := 4983230072969 + 3 ^ 40 * 7702450 * 2
def baseEnd_7702450 : Nat := 439451007469277151405787

theorem tailTrace_7702450 : CollatzResearch.WordTrace tailWord_7702450 prefixEnd_7702450 439451007469277151405787 := by
  unfold tailWord_7702450
  simp only [CollatzResearch.WordTrace]
  refine ⟨70232857736336649643724201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187287620630231065716597869 70232857736336649643724201)
  ·
    refine ⟨52674643302252487232793151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70232857736336649643724201 52674643302252487232793151)
    ·
      refine ⟨79011964953378730849189727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52674643302252487232793151 79011964953378730849189727)
      ·
        refine ⟨118517947430068096273784591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79011964953378730849189727 118517947430068096273784591)
        ·
          refine ⟨177776921145102144410676887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118517947430068096273784591 177776921145102144410676887)
          ·
            refine ⟨266665381717653216616015331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177776921145102144410676887 266665381717653216616015331)
            ·
              refine ⟨399998072576479824924022997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266665381717653216616015331 399998072576479824924022997)
              ·
                refine ⟨9374954826011245896656789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 399998072576479824924022997 9374954826011245896656789)
                ·
                  refine ⟨439451007469277151405787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9374954826011245896656789 439451007469277151405787)
                  ·
                    rfl

theorem cell23_7702450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_7702450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702450 prefixEnd_7702450 := by exact prefixLift 7702450
  have htrace : WordTrace (prefixWord ++ tailWord_7702450) baseStart_7702450 baseEnd_7702450 := by
    simpa [prefixWord, tailWord_7702450, baseEnd_7702450] using wordTrace_append hprefix tailTrace_7702450
  have hstable : (prefixWord ++ tailWord_7702450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702450).length < 2 ^ (prefixWord ++ tailWord_7702450).sum := by decide
  have hdescent : baseEnd_7702450 < baseStart_7702450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702520 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_7702520 : Nat := 118140960795 + 7702520 * 2 ^ 59
def prefixEnd_7702520 : Nat := 4983230072969 + 3 ^ 40 * 7702520 * 2
def baseEnd_7702520 : Nat := 3955095010869309088776761

theorem tailTrace_7702520 : CollatzResearch.WordTrace tailWord_7702520 prefixEnd_7702520 3955095010869309088776761 := by
  unfold tailWord_7702520
  simp only [CollatzResearch.WordTrace]
  refine ⟨140466992027546500264972507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187289322703395333686630009 140466992027546500264972507)
  ·
    refine ⟨210700488041319750397458761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140466992027546500264972507 210700488041319750397458761)
    ·
      refine ⟨158025366030989812798094071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210700488041319750397458761 158025366030989812798094071)
      ·
        refine ⟨237038049046484719197141107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158025366030989812798094071 237038049046484719197141107)
        ·
          refine ⟨355557073569727078795711661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237038049046484719197141107 355557073569727078795711661)
          ·
            refine ⟨133333902588647654548391873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355557073569727078795711661 133333902588647654548391873)
            ·
              refine ⟨100000426941485740911293905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133333902588647654548391873 100000426941485740911293905)
              ·
                refine ⟨75000320206114305683470429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100000426941485740911293905 75000320206114305683470429)
                ·
                  refine ⟨28125120077292864631301411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75000320206114305683470429 28125120077292864631301411)
                  ·
                    refine ⟨42187680115939296946952117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28125120077292864631301411 42187680115939296946952117)
                    ·
                      refine ⟨3955095010869309088776761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42187680115939296946952117 3955095010869309088776761)
                      ·
                        rfl

theorem cell23_7702520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_7702520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702520 prefixEnd_7702520 := by exact prefixLift 7702520
  have htrace : WordTrace (prefixWord ++ tailWord_7702520) baseStart_7702520 baseEnd_7702520 := by
    simpa [prefixWord, tailWord_7702520, baseEnd_7702520] using wordTrace_append hprefix tailTrace_7702520
  have hstable : (prefixWord ++ tailWord_7702520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702520).length < 2 ^ (prefixWord ++ tailWord_7702520).sum := by decide
  have hdescent : baseEnd_7702520 < baseStart_7702520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702557 : List Nat := [1, 4, 2, 2, 2, 1, 3, 8]
def baseStart_7702557 : Nat := 118140960795 + 7702557 * 2 ^ 59
def prefixEnd_7702557 : Nat := 4983230072969 + 3 ^ 40 * 7702557 * 2
def baseEnd_7702557 : Nat := 146485704061241683111633

theorem tailTrace_7702557 : CollatzResearch.WordTrace tailWord_7702557 prefixEnd_7702557 146485704061241683111633 := by
  unfold tailWord_7702557
  simp only [CollatzResearch.WordTrace]
  refine ⟨280935333555958955849041925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187290222370639303899361283 280935333555958955849041925)
  ·
    refine ⟨52675375041742304221695361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280935333555958955849041925 52675375041742304221695361)
    ·
      refine ⟨39506531281306728166271521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52675375041742304221695361 39506531281306728166271521)
      ·
        refine ⟨29629898460980046124703641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39506531281306728166271521 29629898460980046124703641)
        ·
          refine ⟨22222423845735034593527731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29629898460980046124703641 22222423845735034593527731)
          ·
            refine ⟨33333635768602551890291597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22222423845735034593527731 33333635768602551890291597)
            ·
              refine ⟨12500113413225956958859349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33333635768602551890291597 12500113413225956958859349)
              ·
                refine ⟨146485704061241683111633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12500113413225956958859349 146485704061241683111633)
                ·
                  rfl

theorem cell23_7702557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 8].length) (baseStart_7702557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702557 prefixEnd_7702557 := by exact prefixLift 7702557
  have htrace : WordTrace (prefixWord ++ tailWord_7702557) baseStart_7702557 baseEnd_7702557 := by
    simpa [prefixWord, tailWord_7702557, baseEnd_7702557] using wordTrace_append hprefix tailTrace_7702557
  have hstable : (prefixWord ++ tailWord_7702557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702557).length < 2 ^ (prefixWord ++ tailWord_7702557).sum := by decide
  have hdescent : baseEnd_7702557 < baseStart_7702557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702574 : List Nat := [4, 1, 3, 1, 1, 3, 3, 7]
def baseStart_7702574 : Nat := 118140960795 + 7702574 * 2 ^ 59
def prefixEnd_7702574 : Nat := 4983230072969 + 3 ^ 40 * 7702574 * 2
def baseEnd_7702574 : Nat := 146486027363875995463019

theorem tailTrace_7702574 : CollatzResearch.WordTrace tailWord_7702574 prefixEnd_7702574 146486027363875995463019 := by
  unfold tailWord_7702574
  simp only [CollatzResearch.WordTrace]
  refine ⟨35116994199612170969051347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187290635731264911834940517 35116994199612170969051347)
  ·
    refine ⟨52675491299418256453577021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35116994199612170969051347 52675491299418256453577021)
    ·
      refine ⟨19753309237281846170091383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52675491299418256453577021 19753309237281846170091383)
      ·
        refine ⟨29629963855922769255137075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19753309237281846170091383 29629963855922769255137075)
        ·
          refine ⟨44444945783884153882705613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29629963855922769255137075 44444945783884153882705613)
          ·
            refine ⟨16666854668956557706014605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44444945783884153882705613 16666854668956557706014605)
            ·
              refine ⟨6250070500858709139755477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16666854668956557706014605 6250070500858709139755477)
              ·
                refine ⟨146486027363875995463019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6250070500858709139755477 146486027363875995463019)
                ·
                  rfl

theorem cell23_7702574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_7702574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702574 prefixEnd_7702574 := by exact prefixLift 7702574
  have htrace : WordTrace (prefixWord ++ tailWord_7702574) baseStart_7702574 baseEnd_7702574 := by
    simpa [prefixWord, tailWord_7702574, baseEnd_7702574] using wordTrace_append hprefix tailTrace_7702574
  have hstable : (prefixWord ++ tailWord_7702574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702574).length < 2 ^ (prefixWord ++ tailWord_7702574).sum := by decide
  have hdescent : baseEnd_7702574 < baseStart_7702574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702585 : List Nat := [1, 2, 1, 5, 3, 1, 2, 3, 1, 2, 2]
def baseStart_7702585 : Nat := 118140960795 + 7702585 * 2 ^ 59
def prefixEnd_7702585 : Nat := 4983230072969 + 3 ^ 40 * 7702585 * 2
def baseEnd_7702585 : Nat := 3955128387111851334463963

theorem tailTrace_7702585 : CollatzResearch.WordTrace tailWord_7702585 prefixEnd_7702585 3955128387111851334463963 := by
  unfold tailWord_7702585
  simp only [CollatzResearch.WordTrace]
  refine ⟨280936354799857516631061209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187290903199905011087374139 280936354799857516631061209)
  ·
    refine ⟨210702266099893137473295907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280936354799857516631061209 210702266099893137473295907)
    ·
      refine ⟨316053399149839706209943861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210702266099893137473295907 316053399149839706209943861)
      ·
        refine ⟨29630006170297472457182237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316053399149839706209943861 29630006170297472457182237)
        ·
          refine ⟨11111252313861552171443339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29630006170297472457182237 11111252313861552171443339)
          ·
            refine ⟨16666878470792328257165009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11111252313861552171443339 16666878470792328257165009)
            ·
              refine ⟨12500158853094246192873757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16666878470792328257165009 12500158853094246192873757)
              ·
                refine ⟨4687559569910342322327659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12500158853094246192873757 4687559569910342322327659)
                ·
                  refine ⟨7031339354865513483491489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687559569910342322327659 7031339354865513483491489)
                  ·
                    refine ⟨5273504516149135112618617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7031339354865513483491489 5273504516149135112618617)
                    ·
                      refine ⟨3955128387111851334463963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273504516149135112618617 3955128387111851334463963)
                      ·
                        rfl

theorem cell23_7702585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_7702585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702585 prefixEnd_7702585 := by exact prefixLift 7702585
  have htrace : WordTrace (prefixWord ++ tailWord_7702585) baseStart_7702585 baseEnd_7702585 := by
    simpa [prefixWord, tailWord_7702585, baseEnd_7702585] using wordTrace_append hprefix tailTrace_7702585
  have hstable : (prefixWord ++ tailWord_7702585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702585).length < 2 ^ (prefixWord ++ tailWord_7702585).sum := by decide
  have hdescent : baseEnd_7702585 < baseStart_7702585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702627 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 3]
def baseStart_7702627 : Nat := 118140960795 + 7702627 * 2 ^ 59
def prefixEnd_7702627 : Nat := 4983230072969 + 3 ^ 40 * 7702627 * 2
def baseEnd_7702627 : Nat := 3955149953299340170138769

theorem tailTrace_7702627 : CollatzResearch.WordTrace tailWord_7702627 prefixEnd_7702627 3955149953299340170138769 := by
  unfold tailWord_7702627
  simp only [CollatzResearch.WordTrace]
  refine ⟨280937886665705357804090135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187291924443803571869393423 280937886665705357804090135)
  ·
    refine ⟨421406829998558036706135203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280937886665705357804090135 421406829998558036706135203)
    ·
      refine ⟨632110244997837055059202805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421406829998558036706135203 632110244997837055059202805)
      ·
        refine ⟨59260335468547223911800263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 632110244997837055059202805 59260335468547223911800263)
        ·
          refine ⟨88890503202820835867700395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59260335468547223911800263 88890503202820835867700395)
          ·
            refine ⟨133335754804231253801550593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88890503202820835867700395 133335754804231253801550593)
            ·
              refine ⟨100001816103173440351162945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133335754804231253801550593 100001816103173440351162945)
              ·
                refine ⟨75001362077380080263372209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100001816103173440351162945 75001362077380080263372209)
                ·
                  refine ⟨56251021558035060197529157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75001362077380080263372209 56251021558035060197529157)
                  ·
                    refine ⟨10547066542131573787036717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56251021558035060197529157 10547066542131573787036717)
                    ·
                      refine ⟨3955149953299340170138769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10547066542131573787036717 3955149953299340170138769)
                      ·
                        rfl

theorem cell23_7702627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_7702627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702627 prefixEnd_7702627 := by exact prefixLift 7702627
  have htrace : WordTrace (prefixWord ++ tailWord_7702627) baseStart_7702627 baseEnd_7702627 := by
    simpa [prefixWord, tailWord_7702627, baseEnd_7702627] using wordTrace_append hprefix tailTrace_7702627
  have hstable : (prefixWord ++ tailWord_7702627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702627).length < 2 ^ (prefixWord ++ tailWord_7702627).sum := by decide
  have hdescent : baseEnd_7702627 < baseStart_7702627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702664 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 7]
def baseStart_7702664 : Nat := 118140960795 + 7702664 * 2 ^ 59
def prefixEnd_7702664 : Nat := 4983230072969 + 3 ^ 40 * 7702664 * 2
def baseEnd_7702664 : Nat := 439463216898172947264011

theorem tailTrace_7702664 : CollatzResearch.WordTrace tailWord_7702664 prefixEnd_7702664 439463216898172947264011 := by
  unfold tailWord_7702664
  simp only [CollatzResearch.WordTrace]
  refine ⟨140469618083285656561593523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187292824111047542082124697 140469618083285656561593523)
  ·
    refine ⟨210704427124928484842390285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140469618083285656561593523 210704427124928484842390285)
    ·
      refine ⟨79014160171848181815896357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210704427124928484842390285 79014160171848181815896357)
      ·
        refine ⟨14815155032221534090480567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79014160171848181815896357 14815155032221534090480567)
        ·
          refine ⟨22222732548332301135720851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14815155032221534090480567 22222732548332301135720851)
          ·
            refine ⟨33334098822498451703581277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22222732548332301135720851 33334098822498451703581277)
            ·
              refine ⟨12500287058436919388842979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33334098822498451703581277 12500287058436919388842979)
              ·
                refine ⟨18750430587655379083264469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12500287058436919388842979 18750430587655379083264469)
                ·
                  refine ⟨439463216898172947264011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18750430587655379083264469 439463216898172947264011)
                  ·
                    rfl

theorem cell23_7702664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 7].length) (baseStart_7702664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702664 prefixEnd_7702664 := by exact prefixLift 7702664
  have htrace : WordTrace (prefixWord ++ tailWord_7702664) baseStart_7702664 baseEnd_7702664 := by
    simpa [prefixWord, tailWord_7702664, baseEnd_7702664] using wordTrace_append hprefix tailTrace_7702664
  have hstable : (prefixWord ++ tailWord_7702664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702664).length < 2 ^ (prefixWord ++ tailWord_7702664).sum := by decide
  have hdescent : baseEnd_7702664 < baseStart_7702664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702674 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_7702674 : Nat := 118140960795 + 7702674 * 2 ^ 59
def prefixEnd_7702674 : Nat := 4983230072969 + 3 ^ 40 * 7702674 * 2
def baseEnd_7702674 : Nat := 3955174086890101486251053

theorem tailTrace_7702674 : CollatzResearch.WordTrace tailWord_7702674 prefixEnd_7702674 3955174086890101486251053 := by
  unfold tailWord_7702674
  simp only [CollatzResearch.WordTrace]
  refine ⟨70234900224133771207762769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187293067264356723220700717 70234900224133771207762769)
  ·
    refine ⟨52676175168100328405822077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70234900224133771207762769 52676175168100328405822077)
    ·
      refine ⟨19753565688037623152183279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52676175168100328405822077 19753565688037623152183279)
      ·
        refine ⟨29630348532056434728274919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19753565688037623152183279 29630348532056434728274919)
        ·
          refine ⟨44445522798084652092412379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29630348532056434728274919 44445522798084652092412379)
          ·
            refine ⟨66668284197126978138618569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44445522798084652092412379 66668284197126978138618569)
            ·
              refine ⟨50001213147845233603963927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66668284197126978138618569 50001213147845233603963927)
              ·
                refine ⟨75001819721767850405945891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50001213147845233603963927 75001819721767850405945891)
                ·
                  refine ⟨112502729582651775608918837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75001819721767850405945891 112502729582651775608918837)
                  ·
                    refine ⟨10547130898373603963336141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112502729582651775608918837 10547130898373603963336141)
                    ·
                      refine ⟨3955174086890101486251053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10547130898373603963336141 3955174086890101486251053)
                      ·
                        rfl

theorem cell23_7702674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_7702674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702674 prefixEnd_7702674 := by exact prefixLift 7702674
  have htrace : WordTrace (prefixWord ++ tailWord_7702674) baseStart_7702674 baseEnd_7702674 := by
    simpa [prefixWord, tailWord_7702674, baseEnd_7702674] using wordTrace_append hprefix tailTrace_7702674
  have hstable : (prefixWord ++ tailWord_7702674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702674).length < 2 ^ (prefixWord ++ tailWord_7702674).sum := by decide
  have hdescent : baseEnd_7702674 < baseStart_7702674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702677 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_7702677 : Nat := 118140960795 + 7702677 * 2 ^ 59
def prefixEnd_7702677 : Nat := 4983230072969 + 3 ^ 40 * 7702677 * 2
def baseEnd_7702677 : Nat := 1318391875777354991504513

theorem tailTrace_7702677 : CollatzResearch.WordTrace tailWord_7702677 prefixEnd_7702677 1318391875777354991504513 := by
  unfold tailWord_7702677
  simp only [CollatzResearch.WordTrace]
  refine ⟨280939710315524216343410285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187293140210349477562273523 280939710315524216343410285)
  ·
    refine ⟨105352391368321581128778857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280939710315524216343410285 105352391368321581128778857)
    ·
      refine ⟨79014293526241185846584143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105352391368321581128778857 79014293526241185846584143)
      ·
        refine ⟨118521440289361778769876215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79014293526241185846584143 118521440289361778769876215)
        ·
          refine ⟨177782160434042668154814323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118521440289361778769876215 177782160434042668154814323)
          ·
            refine ⟨266673240651064002232221485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177782160434042668154814323 266673240651064002232221485)
            ·
              refine ⟨100002465244149000837083057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266673240651064002232221485 100002465244149000837083057)
              ·
                refine ⟨75001848933111750627812293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100002465244149000837083057 75001848933111750627812293)
                ·
                  refine ⟨14062846674958453242714805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75001848933111750627812293 14062846674958453242714805)
                  ·
                    refine ⟨1318391875777354991504513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14062846674958453242714805 1318391875777354991504513)
                    ·
                      rfl

theorem cell23_7702677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_7702677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702677 prefixEnd_7702677 := by exact prefixLift 7702677
  have htrace : WordTrace (prefixWord ++ tailWord_7702677) baseStart_7702677 baseEnd_7702677 := by
    simpa [prefixWord, tailWord_7702677, baseEnd_7702677] using wordTrace_append hprefix tailTrace_7702677
  have hstable : (prefixWord ++ tailWord_7702677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702677).length < 2 ^ (prefixWord ++ tailWord_7702677).sum := by decide
  have hdescent : baseEnd_7702677 < baseStart_7702677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702714 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_7702714 : Nat := 118140960795 + 7702714 * 2 ^ 59
def prefixEnd_7702714 : Nat := 4983230072969 + 3 ^ 40 * 7702714 * 2
def baseEnd_7702714 : Nat := 3955194626116281329750869

theorem tailTrace_7702714 : CollatzResearch.WordTrace tailWord_7702714 prefixEnd_7702714 3955194626116281329750869 := by
  unfold tailWord_7702714
  simp only [CollatzResearch.WordTrace]
  refine ⟨70235264954097542915626799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187294039877593447775004797 70235264954097542915626799)
  ·
    refine ⟨105352897431146314373440199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70235264954097542915626799 105352897431146314373440199)
    ·
      refine ⟨158029346146719471560160299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105352897431146314373440199 158029346146719471560160299)
      ·
        refine ⟨237044019220079207340240449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158029346146719471560160299 237044019220079207340240449)
        ·
          refine ⟨177783014415059405505180337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237044019220079207340240449 177783014415059405505180337)
          ·
            refine ⟨133337260811294554128885253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177783014415059405505180337 133337260811294554128885253)
            ·
              refine ⟨25000736402117728899165985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133337260811294554128885253 25000736402117728899165985)
              ·
                refine ⟨18750552301588296674374489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25000736402117728899165985 18750552301588296674374489)
                ·
                  refine ⟨14062914226191222505780867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18750552301588296674374489 14062914226191222505780867)
                  ·
                    refine ⟨21094371339286833758671301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14062914226191222505780867 21094371339286833758671301)
                    ·
                      refine ⟨3955194626116281329750869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21094371339286833758671301 3955194626116281329750869)
                      ·
                        rfl

theorem cell23_7702714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_7702714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702714 prefixEnd_7702714 := by exact prefixLift 7702714
  have htrace : WordTrace (prefixWord ++ tailWord_7702714) baseStart_7702714 baseEnd_7702714 := by
    simpa [prefixWord, tailWord_7702714, baseEnd_7702714] using wordTrace_append hprefix tailTrace_7702714
  have hstable : (prefixWord ++ tailWord_7702714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702714).length < 2 ^ (prefixWord ++ tailWord_7702714).sum := by decide
  have hdescent : baseEnd_7702714 < baseStart_7702714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702717 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7702717 : Nat := 118140960795 + 7702717 * 2 ^ 59
def prefixEnd_7702717 : Nat := 4983230072969 + 3 ^ 40 * 7702717 * 2
def baseEnd_7702717 : Nat := 3955196166558244818013355

theorem tailTrace_7702717 : CollatzResearch.WordTrace tailWord_7702717 prefixEnd_7702717 3955196166558244818013355 := by
  unfold tailWord_7702717
  simp only [CollatzResearch.WordTrace]
  refine ⟨280941169235379303174866405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187294112823586202116577603 280941169235379303174866405)
  ·
    refine ⟨52676469231633619345287451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280941169235379303174866405 52676469231633619345287451)
    ·
      refine ⟨79014703847450429017931177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52676469231633619345287451 79014703847450429017931177)
      ·
        refine ⟨59261027885587821763448383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79014703847450429017931177 59261027885587821763448383)
        ·
          refine ⟨88891541828381732645172575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59261027885587821763448383 88891541828381732645172575)
          ·
            refine ⟨133337312742572598967758863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88891541828381732645172575 133337312742572598967758863)
            ·
              refine ⟨200005969113858898451638295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133337312742572598967758863 200005969113858898451638295)
              ·
                refine ⟨300008953670788347677457443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200005969113858898451638295 300008953670788347677457443)
                ·
                  refine ⟨450013430506182521516186165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300008953670788347677457443 450013430506182521516186165)
                  ·
                    refine ⟨42188759109954611392142453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 450013430506182521516186165 42188759109954611392142453)
                    ·
                      refine ⟨3955196166558244818013355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42188759109954611392142453 3955196166558244818013355)
                      ·
                        rfl

theorem cell23_7702717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7702717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702717 prefixEnd_7702717 := by exact prefixLift 7702717
  have htrace : WordTrace (prefixWord ++ tailWord_7702717) baseStart_7702717 baseEnd_7702717 := by
    simpa [prefixWord, tailWord_7702717, baseEnd_7702717] using wordTrace_append hprefix tailTrace_7702717
  have hstable : (prefixWord ++ tailWord_7702717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702717).length < 2 ^ (prefixWord ++ tailWord_7702717).sum := by decide
  have hdescent : baseEnd_7702717 < baseStart_7702717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702727 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_7702727 : Nat := 118140960795 + 7702727 * 2 ^ 59
def prefixEnd_7702727 : Nat := 4983230072969 + 3 ^ 40 * 7702727 * 2
def baseEnd_7702727 : Nat := 3955201301364789778888309

theorem tailTrace_7702727 : CollatzResearch.WordTrace tailWord_7702727 prefixEnd_7702727 3955201301364789778888309 := by
  unfold tailWord_7702727
  simp only [CollatzResearch.WordTrace]
  refine ⟨280941533965343074882730435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187294355976895383255153623 280941533965343074882730435)
  ·
    refine ⟨421412300948014612324095653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280941533965343074882730435 421412300948014612324095653)
    ·
      refine ⟨79014806427752739810767935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421412300948014612324095653 79014806427752739810767935)
      ·
        refine ⟨118522209641629109716151903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79014806427752739810767935 118522209641629109716151903)
        ·
          refine ⟨177783314462443664574227855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118522209641629109716151903 177783314462443664574227855)
          ·
            refine ⟨266674971693665496861341783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177783314462443664574227855 266674971693665496861341783)
            ·
              refine ⟨400012457540498245292012675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266674971693665496861341783 400012457540498245292012675)
              ·
                refine ⟨600018686310747367938019013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400012457540498245292012675 600018686310747367938019013)
                ·
                  refine ⟨112503503683265131488378565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600018686310747367938019013 112503503683265131488378565)
                  ·
                    refine ⟨21094406940612212154070981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112503503683265131488378565 21094406940612212154070981)
                    ·
                      refine ⟨3955201301364789778888309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21094406940612212154070981 3955201301364789778888309)
                      ·
                        rfl

theorem cell23_7702727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_7702727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702727 prefixEnd_7702727 := by exact prefixLift 7702727
  have htrace : WordTrace (prefixWord ++ tailWord_7702727) baseStart_7702727 baseEnd_7702727 := by
    simpa [prefixWord, tailWord_7702727, baseEnd_7702727] using wordTrace_append hprefix tailTrace_7702727
  have hstable : (prefixWord ++ tailWord_7702727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702727).length < 2 ^ (prefixWord ++ tailWord_7702727).sum := by decide
  have hdescent : baseEnd_7702727 < baseStart_7702727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702748 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7702748 : Nat := 118140960795 + 7702748 * 2 ^ 59
def prefixEnd_7702748 : Nat := 4983230072969 + 3 ^ 40 * 7702748 * 2
def baseEnd_7702748 : Nat := 3955212084458534196725713

theorem tailTrace_7702748 : CollatzResearch.WordTrace tailWord_7702748 prefixEnd_7702748 3955212084458534196725713 := by
  unfold tailWord_7702748
  simp only [CollatzResearch.WordTrace]
  refine ⟨140471149949133497734622449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187294866598844663646163265 140471149949133497734622449)
  ·
    refine ⟨105353362461850123300966837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140471149949133497734622449 105353362461850123300966837)
    ·
      refine ⟨9876877730798449059465641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105353362461850123300966837 9876877730798449059465641)
      ·
        refine ⟨7407658298098836794599231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9876877730798449059465641 7407658298098836794599231)
        ·
          refine ⟨11111487447148255191898847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7407658298098836794599231 11111487447148255191898847)
          ·
            refine ⟨16667231170722382787848271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11111487447148255191898847 16667231170722382787848271)
            ·
              refine ⟨25000846756083574181772407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16667231170722382787848271 25000846756083574181772407)
              ·
                refine ⟨37501270134125361272658611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25000846756083574181772407 37501270134125361272658611)
                ·
                  refine ⟨56251905201188041908987917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37501270134125361272658611 56251905201188041908987917)
                  ·
                    refine ⟨21094464450445515715870469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56251905201188041908987917 21094464450445515715870469)
                    ·
                      refine ⟨3955212084458534196725713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21094464450445515715870469 3955212084458534196725713)
                      ·
                        rfl

theorem cell23_7702748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7702748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702748 prefixEnd_7702748 := by exact prefixLift 7702748
  have htrace : WordTrace (prefixWord ++ tailWord_7702748) baseStart_7702748 baseEnd_7702748 := by
    simpa [prefixWord, tailWord_7702748, baseEnd_7702748] using wordTrace_append hprefix tailTrace_7702748
  have hstable : (prefixWord ++ tailWord_7702748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702748).length < 2 ^ (prefixWord ++ tailWord_7702748).sum := by decide
  have hdescent : baseEnd_7702748 < baseStart_7702748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702774 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_7702774 : Nat := 118140960795 + 7702774 * 2 ^ 59
def prefixEnd_7702774 : Nat := 4983230072969 + 3 ^ 40 * 7702774 * 2
def baseEnd_7702774 : Nat := 3955225434955551095000593

theorem tailTrace_7702774 : CollatzResearch.WordTrace tailWord_7702774 prefixEnd_7702774 3955225434955551095000593 := by
  unfold tailWord_7702774
  simp only [CollatzResearch.WordTrace]
  refine ⟨17558953012260800119355711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187295498797448534606460917 17558953012260800119355711)
  ·
    refine ⟨26338429518391200179033567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17558953012260800119355711 26338429518391200179033567)
    ·
      refine ⟨39507644277586800268550351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26338429518391200179033567 39507644277586800268550351)
      ·
        refine ⟨59261466416380200402825527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39507644277586800268550351 59261466416380200402825527)
        ·
          refine ⟨88892199624570300604238291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59261466416380200402825527 88892199624570300604238291)
          ·
            refine ⟨133338299436855450906357437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88892199624570300604238291 133338299436855450906357437)
            ·
              refine ⟨50001862288820794089884039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133338299436855450906357437 50001862288820794089884039)
              ·
                refine ⟨75002793433231191134826059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50001862288820794089884039 75002793433231191134826059)
                ·
                  refine ⟨112504190149846786702239089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75002793433231191134826059 112504190149846786702239089)
                  ·
                    refine ⟨84378142612385090026679317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112504190149846786702239089 84378142612385090026679317)
                    ·
                      refine ⟨3955225434955551095000593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84378142612385090026679317 3955225434955551095000593)
                      ·
                        rfl

theorem cell23_7702774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_7702774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702774 prefixEnd_7702774 := by exact prefixLift 7702774
  have htrace : WordTrace (prefixWord ++ tailWord_7702774) baseStart_7702774 baseEnd_7702774 := by
    simpa [prefixWord, tailWord_7702774, baseEnd_7702774] using wordTrace_append hprefix tailTrace_7702774
  have hstable : (prefixWord ++ tailWord_7702774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702774).length < 2 ^ (prefixWord ++ tailWord_7702774).sum := by decide
  have hdescent : baseEnd_7702774 < baseStart_7702774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702777 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_7702777 : Nat := 118140960795 + 7702777 * 2 ^ 59
def prefixEnd_7702777 : Nat := 4983230072969 + 3 ^ 40 * 7702777 * 2
def baseEnd_7702777 : Nat := 3955226975397514583263079

theorem tailTrace_7702777 : CollatzResearch.WordTrace tailWord_7702777 prefixEnd_7702777 3955226975397514583263079 := by
  unfold tailWord_7702777
  simp only [CollatzResearch.WordTrace]
  refine ⟨280943357615161933422050585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187295571743441288948033723 280943357615161933422050585)
  ·
    refine ⟨210707518211371450066537939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280943357615161933422050585 210707518211371450066537939)
    ·
      refine ⟨316061277317057175099806909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210707518211371450066537939 316061277317057175099806909)
      ·
        refine ⟨118522978993896440662427591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316061277317057175099806909 118522978993896440662427591)
        ·
          refine ⟨177784468490844660993641387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118522978993896440662427591 177784468490844660993641387)
          ·
            refine ⟨266676702736266991490462081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177784468490844660993641387 266676702736266991490462081)
            ·
              refine ⟨200007527052200243617846561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266676702736266991490462081 200007527052200243617846561)
              ·
                refine ⟨150005645289150182713384921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200007527052200243617846561 150005645289150182713384921)
                ·
                  refine ⟨112504233966862637035038691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150005645289150182713384921 112504233966862637035038691)
                  ·
                    refine ⟨168756350950293955552558037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112504233966862637035038691 168756350950293955552558037)
                    ·
                      refine ⟨3955226975397514583263079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168756350950293955552558037 3955226975397514583263079)
                      ·
                        rfl

theorem cell23_7702777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_7702777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702777 prefixEnd_7702777 := by exact prefixLift 7702777
  have htrace : WordTrace (prefixWord ++ tailWord_7702777) baseStart_7702777 baseEnd_7702777 := by
    simpa [prefixWord, tailWord_7702777, baseEnd_7702777] using wordTrace_append hprefix tailTrace_7702777
  have hstable : (prefixWord ++ tailWord_7702777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702777).length < 2 ^ (prefixWord ++ tailWord_7702777).sum := by decide
  have hdescent : baseEnd_7702777 < baseStart_7702777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702788 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 6]
def baseStart_7702788 : Nat := 118140960795 + 7702788 * 2 ^ 59
def prefixEnd_7702788 : Nat := 4983230072969 + 3 ^ 40 * 7702788 * 2
def baseEnd_7702788 : Nat := 439470291520523782247281

theorem tailTrace_7702788 : CollatzResearch.WordTrace tailWord_7702788 prefixEnd_7702788 439470291520523782247281 := by
  unfold tailWord_7702788
  simp only [CollatzResearch.WordTrace]
  refine ⟨140471879409061041150350509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187295839212081388200467345 140471879409061041150350509)
  ·
    refine ⟨52676954778397890431381441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140471879409061041150350509 52676954778397890431381441)
    ·
      refine ⟨39507716083798417823536081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52676954778397890431381441 39507716083798417823536081)
      ·
        refine ⟨29630787062848813367652061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39507716083798417823536081 29630787062848813367652061)
        ·
          refine ⟨11111545148568305012869523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29630787062848813367652061 11111545148568305012869523)
          ·
            refine ⟨16667317722852457519304285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11111545148568305012869523 16667317722852457519304285)
            ·
              refine ⟨6250244146069671569739107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16667317722852457519304285 6250244146069671569739107)
              ·
                refine ⟨9375366219104507354608661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6250244146069671569739107 9375366219104507354608661)
                ·
                  refine ⟨439470291520523782247281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9375366219104507354608661 439470291520523782247281)
                  ·
                    rfl

theorem cell23_7702788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_7702788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702788 prefixEnd_7702788 := by exact prefixLift 7702788
  have htrace : WordTrace (prefixWord ++ tailWord_7702788) baseStart_7702788 baseEnd_7702788 := by
    simpa [prefixWord, tailWord_7702788, baseEnd_7702788] using wordTrace_append hprefix tailTrace_7702788
  have hstable : (prefixWord ++ tailWord_7702788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702788).length < 2 ^ (prefixWord ++ tailWord_7702788).sum := by decide
  have hdescent : baseEnd_7702788 < baseStart_7702788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702801 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 1, 5]
def baseStart_7702801 : Nat := 118140960795 + 7702801 * 2 ^ 59
def prefixEnd_7702801 : Nat := 4983230072969 + 3 ^ 40 * 7702801 * 2
def baseEnd_7702801 : Nat := 1318413099644407496454323

theorem tailTrace_7702801 : CollatzResearch.WordTrace tailWord_7702801 prefixEnd_7702801 1318413099644407496454323 := by
  unfold tailWord_7702801
  simp only [CollatzResearch.WordTrace]
  refine ⟨280944232967074985520924257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187296155311383323680616171 280944232967074985520924257)
  ·
    refine ⟨210708174725306239140693193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280944232967074985520924257 210708174725306239140693193)
    ·
      refine ⟨158031131043979679355519895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210708174725306239140693193 158031131043979679355519895)
      ·
        refine ⟨237046696565969519033279843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158031131043979679355519895 237046696565969519033279843)
        ·
          refine ⟨355570044848954278549919765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237046696565969519033279843 355570044848954278549919765)
          ·
            refine ⟨16667345852294731807027489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 355570044848954278549919765 16667345852294731807027489)
            ·
              refine ⟨12500509389221048855270617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16667345852294731807027489 12500509389221048855270617)
              ·
                refine ⟨9375382041915786641452963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12500509389221048855270617 9375382041915786641452963)
                ·
                  refine ⟨14063073062873679962179445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375382041915786641452963 14063073062873679962179445)
                  ·
                    refine ⟨1318413099644407496454323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14063073062873679962179445 1318413099644407496454323)
                    ·
                      rfl

theorem cell23_7702801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_7702801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702801 prefixEnd_7702801 := by exact prefixLift 7702801
  have htrace : WordTrace (prefixWord ++ tailWord_7702801) baseStart_7702801 baseEnd_7702801 := by
    simpa [prefixWord, tailWord_7702801, baseEnd_7702801] using wordTrace_append hprefix tailTrace_7702801
  have hstable : (prefixWord ++ tailWord_7702801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702801).length < 2 ^ (prefixWord ++ tailWord_7702801).sum := by decide
  have hdescent : baseEnd_7702801 < baseStart_7702801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702815 : List Nat := [1, 1, 2, 4, 3, 1, 3, 3, 1, 1, 3]
def baseStart_7702815 : Nat := 118140960795 + 7702815 * 2 ^ 59
def prefixEnd_7702815 : Nat := 4983230072969 + 3 ^ 40 * 7702815 * 2
def baseEnd_7702815 : Nat := 3955246487662385434587905

theorem tailTrace_7702815 : CollatzResearch.WordTrace tailWord_7702815 prefixEnd_7702815 3955246487662385434587905 := by
  unfold tailWord_7702815
  simp only [CollatzResearch.WordTrace]
  refine ⟨280944743589024265911933899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187296495726016177274622599 280944743589024265911933899)
  ·
    refine ⟨421417115383536398867900849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280944743589024265911933899 421417115383536398867900849)
    ·
      refine ⟨316062836537652299150925637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421417115383536398867900849 316062836537652299150925637)
      ·
        refine ⟨59261781850809806090798557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316062836537652299150925637 59261781850809806090798557)
        ·
          refine ⟨22223168194053677284049459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59261781850809806090798557 22223168194053677284049459)
          ·
            refine ⟨33334752291080515926074189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22223168194053677284049459 33334752291080515926074189)
            ·
              refine ⟨12500532109155193472277821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33334752291080515926074189 12500532109155193472277821)
              ·
                refine ⟨4687699540933197552104183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12500532109155193472277821 4687699540933197552104183)
                ·
                  refine ⟨7031549311399796328156275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687699540933197552104183 7031549311399796328156275)
                  ·
                    refine ⟨10547323967099694492234413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7031549311399796328156275 10547323967099694492234413)
                    ·
                      refine ⟨3955246487662385434587905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10547323967099694492234413 3955246487662385434587905)
                      ·
                        rfl

theorem cell23_7702815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_7702815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702815 prefixEnd_7702815 := by exact prefixLift 7702815
  have htrace : WordTrace (prefixWord ++ tailWord_7702815) baseStart_7702815 baseEnd_7702815 := by
    simpa [prefixWord, tailWord_7702815, baseEnd_7702815] using wordTrace_append hprefix tailTrace_7702815
  have hstable : (prefixWord ++ tailWord_7702815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702815).length < 2 ^ (prefixWord ++ tailWord_7702815).sum := by decide
  have hdescent : baseEnd_7702815 < baseStart_7702815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702841 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7702841 : Nat := 118140960795 + 7702841 * 2 ^ 59
def prefixEnd_7702841 : Nat := 4983230072969 + 3 ^ 40 * 7702841 * 2
def baseEnd_7702841 : Nat := 3955259838159402332862785

theorem tailTrace_7702841 : CollatzResearch.WordTrace tailWord_7702841 prefixEnd_7702841 3955259838159402332862785 := by
  unfold tailWord_7702841
  simp only [CollatzResearch.WordTrace]
  refine ⟨280945691886930072352380377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187297127924620048234920251 280945691886930072352380377)
  ·
    refine ⟨210709268915197554264285283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280945691886930072352380377 210709268915197554264285283)
    ·
      refine ⟨316063903372796331396427925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210709268915197554264285283 316063903372796331396427925)
      ·
        refine ⟨14815495470599828034207559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 316063903372796331396427925 14815495470599828034207559)
        ·
          refine ⟨22223243205899742051311339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14815495470599828034207559 22223243205899742051311339)
          ·
            refine ⟨33334864808849613076967009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22223243205899742051311339 33334864808849613076967009)
            ·
              refine ⟨25001148606637209807725257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33334864808849613076967009 25001148606637209807725257)
              ·
                refine ⟨18750861454977907355793943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25001148606637209807725257 18750861454977907355793943)
                ·
                  refine ⟨28126292182466861033690915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18750861454977907355793943 28126292182466861033690915)
                  ·
                    refine ⟨42189438273700291550536373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28126292182466861033690915 42189438273700291550536373)
                    ·
                      refine ⟨3955259838159402332862785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42189438273700291550536373 3955259838159402332862785)
                      ·
                        rfl

theorem cell23_7702841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7702841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702841 prefixEnd_7702841 := by exact prefixLift 7702841
  have htrace : WordTrace (prefixWord ++ tailWord_7702841) baseStart_7702841 baseEnd_7702841 := by
    simpa [prefixWord, tailWord_7702841, baseEnd_7702841] using wordTrace_append hprefix tailTrace_7702841
  have hstable : (prefixWord ++ tailWord_7702841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702841).length < 2 ^ (prefixWord ++ tailWord_7702841).sum := by decide
  have hdescent : baseEnd_7702841 < baseStart_7702841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702844 : List Nat := [2, 2, 2, 2, 1, 2, 4, 8]
def baseStart_7702844 : Nat := 118140960795 + 7702844 * 2 ^ 59
def prefixEnd_7702844 : Nat := 4983230072969 + 3 ^ 40 * 7702844 * 2
def baseEnd_7702844 : Nat := 146491162170420956337973

theorem tailTrace_7702844 : CollatzResearch.WordTrace tailWord_7702844 prefixEnd_7702844 146491162170420956337973 := by
  unfold tailWord_7702844
  simp only [CollatzResearch.WordTrace]
  refine ⟨140472900652959601932369793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187297200870612802576493057 140472900652959601932369793)
  ·
    refine ⟨105354675489719701449277345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140472900652959601932369793 105354675489719701449277345)
    ·
      refine ⟨79016006617289776086958009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105354675489719701449277345 79016006617289776086958009)
      ·
        refine ⟨59262004962967332065218507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79016006617289776086958009 59262004962967332065218507)
        ·
          refine ⟨88893007444450998097827761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59262004962967332065218507 88893007444450998097827761)
          ·
            refine ⟨66669755583338248573370821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88893007444450998097827761 66669755583338248573370821)
            ·
              refine ⟨12500579171875921607507029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66669755583338248573370821 12500579171875921607507029)
              ·
                refine ⟨146491162170420956337973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12500579171875921607507029 146491162170420956337973)
                ·
                  rfl

theorem cell23_7702844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 8].length) (baseStart_7702844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702844 prefixEnd_7702844 := by exact prefixLift 7702844
  have htrace : WordTrace (prefixWord ++ tailWord_7702844) baseStart_7702844 baseEnd_7702844 := by
    simpa [prefixWord, tailWord_7702844, baseEnd_7702844] using wordTrace_append hprefix tailTrace_7702844
  have hstable : (prefixWord ++ tailWord_7702844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702844).length < 2 ^ (prefixWord ++ tailWord_7702844).sum := by decide
  have hdescent : baseEnd_7702844 < baseStart_7702844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702852 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_7702852 : Nat := 118140960795 + 7702852 * 2 ^ 59
def prefixEnd_7702852 : Nat := 4983230072969 + 3 ^ 40 * 7702852 * 2
def baseEnd_7702852 : Nat := 1318421828815533929941745

theorem tailTrace_7702852 : CollatzResearch.WordTrace tailWord_7702852 prefixEnd_7702852 1318421828815533929941745 := by
  unfold tailWord_7702852
  simp only [CollatzResearch.WordTrace]
  refine ⟨140473046544945110615515405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187297395393260147487353873 140473046544945110615515405)
  ·
    refine ⟨52677392454354416480818277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140473046544945110615515405 52677392454354416480818277)
    ·
      refine ⟨9877011085191453090153427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52677392454354416480818277 9877011085191453090153427)
      ·
        refine ⟨14815516627787179635230141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9877011085191453090153427 14815516627787179635230141)
        ·
          refine ⟨5555818735420192363211303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14815516627787179635230141 5555818735420192363211303)
          ·
            refine ⟨8333728103130288544816955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5555818735420192363211303 8333728103130288544816955)
            ·
              refine ⟨12500592154695432817225433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8333728103130288544816955 12500592154695432817225433)
              ·
                refine ⟨9375444116021574612919075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12500592154695432817225433 9375444116021574612919075)
                ·
                  refine ⟨14063166174032361919378613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375444116021574612919075 14063166174032361919378613)
                  ·
                    refine ⟨1318421828815533929941745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14063166174032361919378613 1318421828815533929941745)
                    ·
                      rfl

theorem cell23_7702852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_7702852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702852 prefixEnd_7702852 := by exact prefixLift 7702852
  have htrace : WordTrace (prefixWord ++ tailWord_7702852) baseStart_7702852 baseEnd_7702852 := by
    simpa [prefixWord, tailWord_7702852, baseEnd_7702852] using wordTrace_append hprefix tailTrace_7702852
  have hstable : (prefixWord ++ tailWord_7702852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702852).length < 2 ^ (prefixWord ++ tailWord_7702852).sum := by decide
  have hdescent : baseEnd_7702852 < baseStart_7702852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702871 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_7702871 : Nat := 118140960795 + 7702871 * 2 ^ 59
def prefixEnd_7702871 : Nat := 4983230072969 + 3 ^ 40 * 7702871 * 2
def baseEnd_7702871 : Nat := 3955275242579037215487647

theorem tailTrace_7702871 : CollatzResearch.WordTrace tailWord_7702871 prefixEnd_7702871 3955275242579037215487647 := by
  unfold tailWord_7702871
  simp only [CollatzResearch.WordTrace]
  refine ⟨280946786076821387475972467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187297857384547591650648311 280946786076821387475972467)
  ·
    refine ⟨421420179115232081213958701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280946786076821387475972467 421420179115232081213958701)
    ·
      refine ⟨158032567168212030455234513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421420179115232081213958701 158032567168212030455234513)
      ·
        refine ⟨118524425376159022841425885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158032567168212030455234513 118524425376159022841425885)
        ·
          refine ⟨44446659516059633565534707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118524425376159022841425885 44446659516059633565534707)
          ·
            refine ⟨66669989274089450348302061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44446659516059633565534707 66669989274089450348302061)
            ·
              refine ⟨25001245977783543880613273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66669989274089450348302061 25001245977783543880613273)
              ·
                refine ⟨18750934483337657910459955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25001245977783543880613273 18750934483337657910459955)
                ·
                  refine ⟨28126401725006486865689933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18750934483337657910459955 28126401725006486865689933)
                  ·
                    refine ⟨10547400646877432574633725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28126401725006486865689933 10547400646877432574633725)
                    ·
                      refine ⟨3955275242579037215487647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10547400646877432574633725 3955275242579037215487647)
                      ·
                        rfl

theorem cell23_7702871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_7702871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702871 prefixEnd_7702871 := by exact prefixLift 7702871
  have htrace : WordTrace (prefixWord ++ tailWord_7702871) baseStart_7702871 baseEnd_7702871 := by
    simpa [prefixWord, tailWord_7702871, baseEnd_7702871] using wordTrace_append hprefix tailTrace_7702871
  have hstable : (prefixWord ++ tailWord_7702871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702871).length < 2 ^ (prefixWord ++ tailWord_7702871).sum := by decide
  have hdescent : baseEnd_7702871 < baseStart_7702871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702898 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_7702898 : Nat := 118140960795 + 7702898 * 2 ^ 59
def prefixEnd_7702898 : Nat := 4983230072969 + 3 ^ 40 * 7702898 * 2
def baseEnd_7702898 : Nat := 3955289106556708609850023

theorem tailTrace_7702898 : CollatzResearch.WordTrace tailWord_7702898 prefixEnd_7702898 3955289106556708609850023 := by
  unfold tailWord_7702898
  simp only [CollatzResearch.WordTrace]
  refine ⟨70236942711930892771801337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187298513898482380724803565 70236942711930892771801337)
  ·
    refine ⟨52677707033948169578851003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70236942711930892771801337 52677707033948169578851003)
    ·
      refine ⟨79016560550922254368276505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52677707033948169578851003 79016560550922254368276505)
      ·
        refine ⟨59262420413191690776207379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79016560550922254368276505 59262420413191690776207379)
        ·
          refine ⟨88893630619787536164311069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59262420413191690776207379 88893630619787536164311069)
          ·
            refine ⟨33335111482420326061616651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88893630619787536164311069 33335111482420326061616651)
            ·
              refine ⟨50002667223630489092424977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33335111482420326061616651 50002667223630489092424977)
              ·
                refine ⟨37502000417722866819318733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50002667223630489092424977 37502000417722866819318733)
                ·
                  refine ⟨14063250156646075057244525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37502000417722866819318733 14063250156646075057244525)
                  ·
                    refine ⟨5273718808742278146466697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14063250156646075057244525 5273718808742278146466697)
                    ·
                      refine ⟨3955289106556708609850023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273718808742278146466697 3955289106556708609850023)
                      ·
                        rfl

theorem cell23_7702898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_7702898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702898 prefixEnd_7702898 := by exact prefixLift 7702898
  have htrace : WordTrace (prefixWord ++ tailWord_7702898) baseStart_7702898 baseEnd_7702898 := by
    simpa [prefixWord, tailWord_7702898, baseEnd_7702898] using wordTrace_append hprefix tailTrace_7702898
  have hstable : (prefixWord ++ tailWord_7702898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702898).length < 2 ^ (prefixWord ++ tailWord_7702898).sum := by decide
  have hdescent : baseEnd_7702898 < baseStart_7702898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702911 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 5, 4, 2]
def baseStart_7702911 : Nat := 118140960795 + 7702911 * 2 ^ 59
def prefixEnd_7702911 : Nat := 4983230072969 + 3 ^ 40 * 7702911 * 2
def baseEnd_7702911 : Nat := 3955295781805217058987463

theorem tailTrace_7702911 : CollatzResearch.WordTrace tailWord_7702911 prefixEnd_7702911 3955295781805217058987463 := by
  unfold tailWord_7702911
  simp only [CollatzResearch.WordTrace]
  refine ⟨280948244996676474307428587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187298829997784316204952391 280948244996676474307428587)
  ·
    refine ⟨421422367495014711461142881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280948244996676474307428587 421422367495014711461142881)
    ·
      refine ⟨316066775621261033595857161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421422367495014711461142881 316066775621261033595857161)
      ·
        refine ⟨237050081715945775196892871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316066775621261033595857161 237050081715945775196892871)
        ·
          refine ⟨355575122573918662795339307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237050081715945775196892871 355575122573918662795339307)
          ·
            refine ⟨533362683860877994193008961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355575122573918662795339307 533362683860877994193008961)
            ·
              refine ⟨400022012895658495644756721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533362683860877994193008961 400022012895658495644756721)
              ·
                refine ⟨300016509671743871733567541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400022012895658495644756721 300016509671743871733567541)
                ·
                  refine ⟨28126547781725987975021957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300016509671743871733567541 28126547781725987975021957)
                  ·
                    refine ⟨5273727709073622745316617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28126547781725987975021957 5273727709073622745316617)
                    ·
                      refine ⟨3955295781805217058987463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273727709073622745316617 3955295781805217058987463)
                      ·
                        rfl

theorem cell23_7702911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_7702911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702911 prefixEnd_7702911 := by exact prefixLift 7702911
  have htrace : WordTrace (prefixWord ++ tailWord_7702911) baseStart_7702911 baseEnd_7702911 := by
    simpa [prefixWord, tailWord_7702911, baseEnd_7702911] using wordTrace_append hprefix tailTrace_7702911
  have hstable : (prefixWord ++ tailWord_7702911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702911).length < 2 ^ (prefixWord ++ tailWord_7702911).sum := by decide
  have hdescent : baseEnd_7702911 < baseStart_7702911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702932 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_7702932 : Nat := 118140960795 + 7702932 * 2 ^ 59
def prefixEnd_7702932 : Nat := 4983230072969 + 3 ^ 40 * 7702932 * 2
def baseEnd_7702932 : Nat := 3955306564898961476824867

theorem tailTrace_7702932 : CollatzResearch.WordTrace tailWord_7702932 prefixEnd_7702932 3955306564898961476824867 := by
  unfold tailWord_7702932
  simp only [CollatzResearch.WordTrace]
  refine ⟨140474505464800197446971525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187299340619733596595962033 140474505464800197446971525)
  ·
    refine ⟨26338969774650037021307161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140474505464800197446971525 26338969774650037021307161)
    ·
      refine ⟨19754227330987527765980371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26338969774650037021307161 19754227330987527765980371)
      ·
        refine ⟨29631340996481291648970557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19754227330987527765980371 29631340996481291648970557)
        ·
          refine ⟨11111752873680484368363959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29631340996481291648970557 11111752873680484368363959)
          ·
            refine ⟨16667629310520726552545939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11111752873680484368363959 16667629310520726552545939)
            ·
              refine ⟨25001443965781089828818909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16667629310520726552545939 25001443965781089828818909)
              ·
                refine ⟨9375541487167908685807091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25001443965781089828818909 9375541487167908685807091)
                ·
                  refine ⟨14063312230751863028710637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375541487167908685807091 14063312230751863028710637)
                  ·
                    refine ⟨5273742086531948635766489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14063312230751863028710637 5273742086531948635766489)
                    ·
                      refine ⟨3955306564898961476824867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273742086531948635766489 3955306564898961476824867)
                      ·
                        rfl

theorem cell23_7702932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_7702932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702932 prefixEnd_7702932 := by exact prefixLift 7702932
  have htrace : WordTrace (prefixWord ++ tailWord_7702932) baseStart_7702932 baseEnd_7702932 := by
    simpa [prefixWord, tailWord_7702932, baseEnd_7702932] using wordTrace_append hprefix tailTrace_7702932
  have hstable : (prefixWord ++ tailWord_7702932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702932).length < 2 ^ (prefixWord ++ tailWord_7702932).sum := by decide
  have hdescent : baseEnd_7702932 < baseStart_7702932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702951 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 7]
def baseStart_7702951 : Nat := 118140960795 + 7702951 * 2 ^ 59
def prefixEnd_7702951 : Nat := 4983230072969 + 3 ^ 40 * 7702951 * 2
def baseEnd_7702951 : Nat := 439479591225710766943031

theorem tailTrace_7702951 : CollatzResearch.WordTrace tailWord_7702951 prefixEnd_7702951 439479591225710766943031 := by
  unfold tailWord_7702951
  simp only [CollatzResearch.WordTrace]
  refine ⟨280949703916531561138884707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187299802611021040759256471 280949703916531561138884707)
  ·
    refine ⟨421424555874797341708327061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280949703916531561138884707 421424555874797341708327061)
    ·
      refine ⟨19754276056631125392577831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 421424555874797341708327061 19754276056631125392577831)
      ·
        refine ⟨29631414084946688088866747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19754276056631125392577831 29631414084946688088866747)
        ·
          refine ⟨44447121127420032133300121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29631414084946688088866747 44447121127420032133300121)
          ·
            refine ⟨33335340845565024099975091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44447121127420032133300121 33335340845565024099975091)
            ·
              refine ⟨50003011268347536149962637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33335340845565024099975091 50003011268347536149962637)
              ·
                refine ⟨18751129225630326056235989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50003011268347536149962637 18751129225630326056235989)
                ·
                  refine ⟨439479591225710766943031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18751129225630326056235989 439479591225710766943031)
                  ·
                    rfl

theorem cell23_7702951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 7].length) (baseStart_7702951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702951 prefixEnd_7702951 := by exact prefixLift 7702951
  have htrace : WordTrace (prefixWord ++ tailWord_7702951) baseStart_7702951 baseEnd_7702951 := by
    simpa [prefixWord, tailWord_7702951, baseEnd_7702951] using wordTrace_append hprefix tailTrace_7702951
  have hstable : (prefixWord ++ tailWord_7702951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702951).length < 2 ^ (prefixWord ++ tailWord_7702951).sum := by decide
  have hdescent : baseEnd_7702951 < baseStart_7702951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7702962 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_7702962 : Nat := 118140960795 + 7702962 * 2 ^ 59
def prefixEnd_7702962 : Nat := 4983230072969 + 3 ^ 40 * 7702962 * 2
def baseEnd_7702962 : Nat := 3955321969318596359449729

theorem tailTrace_7702962 : CollatzResearch.WordTrace tailWord_7702962 prefixEnd_7702962 3955321969318596359449729 := by
  unfold tailWord_7702962
  simp only [CollatzResearch.WordTrace]
  refine ⟨70237526279872927504383785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187300070079661140011690093 70237526279872927504383785)
  ·
    refine ⟨52678144709904695628287839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70237526279872927504383785 52678144709904695628287839)
    ·
      refine ⟨79017217064857043442431759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52678144709904695628287839 79017217064857043442431759)
      ·
        refine ⟨118525825597285565163647639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79017217064857043442431759 118525825597285565163647639)
        ·
          refine ⟨177788738395928347745471459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118525825597285565163647639 177788738395928347745471459)
          ·
            refine ⟨266683107593892521618207189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177788738395928347745471459 266683107593892521618207189)
            ·
              refine ⟨6250385334231855975426731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 266683107593892521618207189 6250385334231855975426731)
              ·
                refine ⟨9375578001347783963140097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6250385334231855975426731 9375578001347783963140097)
                ·
                  refine ⟨7031683501010837972355073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9375578001347783963140097 7031683501010837972355073)
                  ·
                    refine ⟨5273762625758128479266305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7031683501010837972355073 5273762625758128479266305)
                    ·
                      refine ⟨3955321969318596359449729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273762625758128479266305 3955321969318596359449729)
                      ·
                        rfl

theorem cell23_7702962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_7702962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7702962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7702962 prefixEnd_7702962 := by exact prefixLift 7702962
  have htrace : WordTrace (prefixWord ++ tailWord_7702962) baseStart_7702962 baseEnd_7702962 := by
    simpa [prefixWord, tailWord_7702962, baseEnd_7702962] using wordTrace_append hprefix tailTrace_7702962
  have hstable : (prefixWord ++ tailWord_7702962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7702962).length < 2 ^ (prefixWord ++ tailWord_7702962).sum := by decide
  have hdescent : baseEnd_7702962 < baseStart_7702962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7702962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703061 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_7703061 : Nat := 118140960795 + 7703061 * 2 ^ 59
def prefixEnd_7703061 : Nat := 4983230072969 + 3 ^ 40 * 7703061 * 2
def baseEnd_7703061 : Nat := 3955372803903391472111773

theorem tailTrace_7703061 : CollatzResearch.WordTrace tailWord_7703061 prefixEnd_7703061 3955372803903391472111773 := by
  unfold tailWord_7703061
  simp only [CollatzResearch.WordTrace]
  refine ⟨280953715946133049925389037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187302477297422033283592691 280953715946133049925389037)
  ·
    refine ⟨105357643479799893722020889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280953715946133049925389037 105357643479799893722020889)
    ·
      refine ⟨79018232609849920291515667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105357643479799893722020889 79018232609849920291515667)
      ·
        refine ⟨118527348914774880437273501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79018232609849920291515667 118527348914774880437273501)
        ·
          refine ⟨44447755843040580163977563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118527348914774880437273501 44447755843040580163977563)
          ·
            refine ⟨66671633764560870245966345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44447755843040580163977563 66671633764560870245966345)
            ·
              refine ⟨50003725323420652684474759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66671633764560870245966345 50003725323420652684474759)
              ·
                refine ⟨75005587985130979026712139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50003725323420652684474759 75005587985130979026712139)
                ·
                  refine ⟨112508381977696468540068209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75005587985130979026712139 112508381977696468540068209)
                  ·
                    refine ⟨84381286483272351405051157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112508381977696468540068209 84381286483272351405051157)
                    ·
                      refine ⟨3955372803903391472111773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84381286483272351405051157 3955372803903391472111773)
                      ·
                        rfl

theorem cell23_7703061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_7703061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703061 prefixEnd_7703061 := by exact prefixLift 7703061
  have htrace : WordTrace (prefixWord ++ tailWord_7703061) baseStart_7703061 baseEnd_7703061 := by
    simpa [prefixWord, tailWord_7703061, baseEnd_7703061] using wordTrace_append hprefix tailTrace_7703061
  have hstable : (prefixWord ++ tailWord_7703061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703061).length < 2 ^ (prefixWord ++ tailWord_7703061).sum := by decide
  have hdescent : baseEnd_7703061 < baseStart_7703061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703105 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 1, 5]
def baseStart_7703105 : Nat := 118140960795 + 7703105 * 2 ^ 59
def prefixEnd_7703105 : Nat := 4983230072969 + 3 ^ 40 * 7703105 * 2
def baseEnd_7703105 : Nat := 1318465132350729766653857

theorem tailTrace_7703105 : CollatzResearch.WordTrace tailWord_7703105 prefixEnd_7703105 1318465132350729766653857 := by
  unfold tailWord_7703105
  simp only [CollatzResearch.WordTrace]
  refine ⟨280955320757973645439990769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187303547171982430293327179 280955320757973645439990769)
  ·
    refine ⟨210716490568480234079993077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280955320757973645439990769 210716490568480234079993077)
    ·
      refine ⟨19754670990795021944999351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210716490568480234079993077 19754670990795021944999351)
      ·
        refine ⟨29632006486192532917499027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19754670990795021944999351 29632006486192532917499027)
        ·
          refine ⟨44448009729288799376248541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29632006486192532917499027 44448009729288799376248541)
          ·
            refine ⟨16668003648483299766093203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44448009729288799376248541 16668003648483299766093203)
            ·
              refine ⟨25002005472724949649139805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16668003648483299766093203 25002005472724949649139805)
              ·
                refine ⟨9375752052271856118427427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25002005472724949649139805 9375752052271856118427427)
                ·
                  refine ⟨14063628078407784177641141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375752052271856118427427 14063628078407784177641141)
                  ·
                    refine ⟨1318465132350729766653857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14063628078407784177641141 1318465132350729766653857)
                    ·
                      rfl

theorem cell23_7703105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_7703105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703105 prefixEnd_7703105 := by exact prefixLift 7703105
  have htrace : WordTrace (prefixWord ++ tailWord_7703105) baseStart_7703105 baseEnd_7703105 := by
    simpa [prefixWord, tailWord_7703105, baseEnd_7703105] using wordTrace_append hprefix tailTrace_7703105
  have hstable : (prefixWord ++ tailWord_7703105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703105).length < 2 ^ (prefixWord ++ tailWord_7703105).sum := by decide
  have hdescent : baseEnd_7703105 < baseStart_7703105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703128 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_7703128 : Nat := 118140960795 + 7703128 * 2 ^ 59
def prefixEnd_7703128 : Nat := 4983230072969 + 3 ^ 40 * 7703128 * 2
def baseEnd_7703128 : Nat := 3955407207107242709973965

theorem tailTrace_7703128 : CollatzResearch.WordTrace tailWord_7703128 prefixEnd_7703128 3955407207107242709973965 := by
  unfold tailWord_7703128
  simp only [CollatzResearch.WordTrace]
  refine ⟨140478079818445160184039019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187304106424593546912052025 140478079818445160184039019)
  ·
    refine ⟨210717119727667740276058529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140478079818445160184039019 210717119727667740276058529)
    ·
      refine ⟨158037839795750805207043897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210717119727667740276058529 158037839795750805207043897)
      ·
        refine ⟨118528379846813103905282923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158037839795750805207043897 118528379846813103905282923)
        ·
          refine ⟨177792569770219655857924385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118528379846813103905282923 177792569770219655857924385)
          ·
            refine ⟨133344427327664741893443289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177792569770219655857924385 133344427327664741893443289)
            ·
              refine ⟨100008320495748556420082467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133344427327664741893443289 100008320495748556420082467)
              ·
                refine ⟨150012480743622834630123701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100008320495748556420082467 150012480743622834630123701)
                ·
                  refine ⟨14063670069714640746574097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150012480743622834630123701 14063670069714640746574097)
                  ·
                    refine ⟨10547752552285980559930573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14063670069714640746574097 10547752552285980559930573)
                    ·
                      refine ⟨3955407207107242709973965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10547752552285980559930573 3955407207107242709973965)
                      ·
                        rfl

theorem cell23_7703128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_7703128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703128 prefixEnd_7703128 := by exact prefixLift 7703128
  have htrace : WordTrace (prefixWord ++ tailWord_7703128) baseStart_7703128 baseEnd_7703128 := by
    simpa [prefixWord, tailWord_7703128, baseEnd_7703128] using wordTrace_append hprefix tailTrace_7703128
  have hstable : (prefixWord ++ tailWord_7703128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703128).length < 2 ^ (prefixWord ++ tailWord_7703128).sum := by decide
  have hdescent : baseEnd_7703128 < baseStart_7703128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703148 : List Nat := [2, 2, 1, 1, 3, 1, 6, 7]
def baseStart_7703148 : Nat := 118140960795 + 7703148 * 2 ^ 59
def prefixEnd_7703148 : Nat := 4983230072969 + 3 ^ 40 * 7703148 * 2
def baseEnd_7703148 : Nat := 146496943582234541915699

theorem tailTrace_7703148 : CollatzResearch.WordTrace tailWord_7703148 prefixEnd_7703148 146496943582234541915699 := by
  unfold tailWord_7703148
  simp only [CollatzResearch.WordTrace]
  refine ⟨140478444548408931891903049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187304592731211909189204065 140478444548408931891903049)
  ·
    refine ⟨105358833411306698918927287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140478444548408931891903049 105358833411306698918927287)
    ·
      refine ⟨158038250116960048378390931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105358833411306698918927287 158038250116960048378390931)
      ·
        refine ⟨237057375175440072567586397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158038250116960048378390931 237057375175440072567586397)
        ·
          refine ⟨88896515690790027212844899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237057375175440072567586397 88896515690790027212844899)
          ·
            refine ⟨133344773536185040819267349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88896515690790027212844899 133344773536185040819267349)
            ·
              refine ⟨6250536259508673788403157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133344773536185040819267349 6250536259508673788403157)
              ·
                refine ⟨146496943582234541915699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6250536259508673788403157 146496943582234541915699)
                ·
                  rfl

theorem cell23_7703148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 7].length) (baseStart_7703148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703148 prefixEnd_7703148 := by exact prefixLift 7703148
  have htrace : WordTrace (prefixWord ++ tailWord_7703148) baseStart_7703148 baseEnd_7703148 := by
    simpa [prefixWord, tailWord_7703148, baseEnd_7703148] using wordTrace_append hprefix tailTrace_7703148
  have hstable : (prefixWord ++ tailWord_7703148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703148).length < 2 ^ (prefixWord ++ tailWord_7703148).sum := by decide
  have hdescent : baseEnd_7703148 < baseStart_7703148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703159 : List Nat := [1, 1, 3, 1, 1, 3, 5, 3, 1, 2, 2]
def baseStart_7703159 : Nat := 118140960795 + 7703159 * 2 ^ 59
def prefixEnd_7703159 : Nat := 4983230072969 + 3 ^ 40 * 7703159 * 2
def baseEnd_7703159 : Nat := 3955423125007532088686323

theorem tailTrace_7703159 : CollatzResearch.WordTrace tailWord_7703159 prefixEnd_7703159 3955423125007532088686323 := by
  unfold tailWord_7703159
  simp only [CollatzResearch.WordTrace]
  refine ⟨280957290299778012662456531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187304860199852008441637687 280957290299778012662456531)
  ·
    refine ⟨421435935449667018993684797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280957290299778012662456531 421435935449667018993684797)
    ·
      refine ⟨158038475793625132122631799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421435935449667018993684797 158038475793625132122631799)
      ·
        refine ⟨237057713690437698183947699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158038475793625132122631799 237057713690437698183947699)
        ·
          refine ⟨355586570535656547275921549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237057713690437698183947699 355586570535656547275921549)
          ·
            refine ⟨133344963950871205228470581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355586570535656547275921549 133344963950871205228470581)
            ·
              refine ⟨12501090370394175490169117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133344963950871205228470581 12501090370394175490169117)
              ·
                refine ⟨4687908888897815808813419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12501090370394175490169117 4687908888897815808813419)
                ·
                  refine ⟨7031863333346723713220129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4687908888897815808813419 7031863333346723713220129)
                  ·
                    refine ⟨5273897500010042784915097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7031863333346723713220129 5273897500010042784915097)
                    ·
                      refine ⟨3955423125007532088686323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273897500010042784915097 3955423125007532088686323)
                      ·
                        rfl

theorem cell23_7703159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_7703159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703159 prefixEnd_7703159 := by exact prefixLift 7703159
  have htrace : WordTrace (prefixWord ++ tailWord_7703159) baseStart_7703159 baseEnd_7703159 := by
    simpa [prefixWord, tailWord_7703159, baseEnd_7703159] using wordTrace_append hprefix tailTrace_7703159
  have hstable : (prefixWord ++ tailWord_7703159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703159).length < 2 ^ (prefixWord ++ tailWord_7703159).sum := by decide
  have hdescent : baseEnd_7703159 < baseStart_7703159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703165 : List Nat := [1, 4, 1, 1, 6, 1, 9]
def baseStart_7703165 : Nat := 118140960795 + 7703165 * 2 ^ 59
def prefixEnd_7703165 : Nat := 4983230072969 + 3 ^ 40 * 7703165 * 2
def baseEnd_7703165 : Nat := 48832422294956284755695

theorem tailTrace_7703165 : CollatzResearch.WordTrace tailWord_7703165 prefixEnd_7703165 48832422294956284755695 := by
  unfold tailWord_7703165
  simp only [CollatzResearch.WordTrace]
  refine ⟨280957509137756275687174949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187305006091837517124783299 280957509137756275687174949)
  ·
    refine ⟨52679532963329301691345303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280957509137756275687174949 52679532963329301691345303)
    ·
      refine ⟨79019299444993952537017955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52679532963329301691345303 79019299444993952537017955)
      ·
        refine ⟨118528949167490928805526933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79019299444993952537017955 118528949167490928805526933)
        ·
          refine ⟨5556044492226137287759075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118528949167490928805526933 5556044492226137287759075)
          ·
            refine ⟨8334066738339205931638613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556044492226137287759075 8334066738339205931638613)
            ·
              refine ⟨48832422294956284755695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8334066738339205931638613 48832422294956284755695)
              ·
                rfl

theorem cell23_7703165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 9].length) (baseStart_7703165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703165 prefixEnd_7703165 := by exact prefixLift 7703165
  have htrace : WordTrace (prefixWord ++ tailWord_7703165) baseStart_7703165 baseEnd_7703165 := by
    simpa [prefixWord, tailWord_7703165, baseEnd_7703165] using wordTrace_append hprefix tailTrace_7703165
  have hstable : (prefixWord ++ tailWord_7703165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703165).length < 2 ^ (prefixWord ++ tailWord_7703165).sum := by decide
  have hdescent : baseEnd_7703165 < baseStart_7703165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703170 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7703170 : Nat := 118140960795 + 7703170 * 2 ^ 59
def prefixEnd_7703170 : Nat := 4983230072969 + 3 ^ 40 * 7703170 * 2
def baseEnd_7703170 : Nat := 3955428773294731545648773

theorem tailTrace_7703170 : CollatzResearch.WordTrace tailWord_7703170 prefixEnd_7703170 3955428773294731545648773 := by
  unfold tailWord_7703170
  simp only [CollatzResearch.WordTrace]
  refine ⟨70239422875684540385276741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187305127668492107694071309 70239422875684540385276741)
  ·
    refine ⟨13169891789190851322239389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70239422875684540385276741 13169891789190851322239389)
    ·
      refine ⟨4938709420946569245839771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13169891789190851322239389 4938709420946569245839771)
      ·
        refine ⟨7408064131419853868759657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938709420946569245839771 7408064131419853868759657)
        ·
          refine ⟨5556048098564890401569743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7408064131419853868759657 5556048098564890401569743)
          ·
            refine ⟨8334072147847335602354615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556048098564890401569743 8334072147847335602354615)
            ·
              refine ⟨12501108221771003403531923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8334072147847335602354615 12501108221771003403531923)
              ·
                refine ⟨18751662332656505105297885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12501108221771003403531923 18751662332656505105297885)
                ·
                  refine ⟨7031873374746189414486707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18751662332656505105297885 7031873374746189414486707)
                  ·
                    refine ⟨10547810062119284121730061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7031873374746189414486707 10547810062119284121730061)
                    ·
                      refine ⟨3955428773294731545648773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10547810062119284121730061 3955428773294731545648773)
                      ·
                        rfl

theorem cell23_7703170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7703170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703170 prefixEnd_7703170 := by exact prefixLift 7703170
  have htrace : WordTrace (prefixWord ++ tailWord_7703170) baseStart_7703170 baseEnd_7703170 := by
    simpa [prefixWord, tailWord_7703170, baseEnd_7703170] using wordTrace_append hprefix tailTrace_7703170
  have hstable : (prefixWord ++ tailWord_7703170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703170).length < 2 ^ (prefixWord ++ tailWord_7703170).sum := by decide
  have hdescent : baseEnd_7703170 < baseStart_7703170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703175 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_7703175 : Nat := 118140960795 + 7703175 * 2 ^ 59
def prefixEnd_7703175 : Nat := 4983230072969 + 3 ^ 40 * 7703175 * 2
def baseEnd_7703175 : Nat := 3955431340698004026086249

theorem tailTrace_7703175 : CollatzResearch.WordTrace tailWord_7703175 prefixEnd_7703175 3955431340698004026086249 := by
  unfold tailWord_7703175
  simp only [CollatzResearch.WordTrace]
  refine ⟨280957873867720047395038979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187305249245146698263359319 280957873867720047395038979)
  ·
    refine ⟨421436810801580071092558469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280957873867720047395038979 421436810801580071092558469)
    ·
      refine ⟨79019402025296263329854713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421436810801580071092558469 79019402025296263329854713)
      ·
        refine ⟨59264551518972197497391035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79019402025296263329854713 59264551518972197497391035)
        ·
          refine ⟨88896827278458296246086553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59264551518972197497391035 88896827278458296246086553)
          ·
            refine ⟨66672620458843722184564915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88896827278458296246086553 66672620458843722184564915)
            ·
              refine ⟨100008930688265583276847373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66672620458843722184564915 100008930688265583276847373)
              ·
                refine ⟨37503349008099593728817765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100008930688265583276847373 37503349008099593728817765)
                ·
                  refine ⟨7031877939018673824153331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37503349008099593728817765 7031877939018673824153331)
                  ·
                    refine ⟨10547816908528010736229997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7031877939018673824153331 10547816908528010736229997)
                    ·
                      refine ⟨3955431340698004026086249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10547816908528010736229997 3955431340698004026086249)
                      ·
                        rfl

theorem cell23_7703175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_7703175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703175 prefixEnd_7703175 := by exact prefixLift 7703175
  have htrace : WordTrace (prefixWord ++ tailWord_7703175) baseStart_7703175 baseEnd_7703175 := by
    simpa [prefixWord, tailWord_7703175, baseEnd_7703175] using wordTrace_append hprefix tailTrace_7703175
  have hstable : (prefixWord ++ tailWord_7703175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703175).length < 2 ^ (prefixWord ++ tailWord_7703175).sum := by decide
  have hdescent : baseEnd_7703175 < baseStart_7703175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703192 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_7703192 : Nat := 118140960795 + 7703192 * 2 ^ 59
def prefixEnd_7703192 : Nat := 4983230072969 + 3 ^ 40 * 7703192 * 2
def baseEnd_7703192 : Nat := 3955440069869130459573671

theorem tailTrace_7703192 : CollatzResearch.WordTrace tailWord_7703192 prefixEnd_7703192 3955440069869130459573671 := by
  unfold tailWord_7703192
  simp only [CollatzResearch.WordTrace]
  refine ⟨140479246954329229649203915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187305662605772306198938553 140479246954329229649203915)
  ·
    refine ⟨210718870431493844473805873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140479246954329229649203915 210718870431493844473805873)
    ·
      refine ⟨158039152823620383355354405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210718870431493844473805873 158039152823620383355354405)
      ·
        refine ⟨29632341154428821879128951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158039152823620383355354405 29632341154428821879128951)
        ·
          refine ⟨44448511731643232818693427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29632341154428821879128951 44448511731643232818693427)
          ·
            refine ⟨66672767597464849228040141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44448511731643232818693427 66672767597464849228040141)
            ·
              refine ⟨25002287849049318460515053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66672767597464849228040141 25002287849049318460515053)
              ·
                refine ⟨9375857943393494422693145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25002287849049318460515053 9375857943393494422693145)
                ·
                  refine ⟨7031893457545120817019859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9375857943393494422693145 7031893457545120817019859)
                  ·
                    refine ⟨10547840186317681225529789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7031893457545120817019859 10547840186317681225529789)
                    ·
                      refine ⟨3955440069869130459573671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10547840186317681225529789 3955440069869130459573671)
                      ·
                        rfl

theorem cell23_7703192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_7703192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703192 prefixEnd_7703192 := by exact prefixLift 7703192
  have htrace : WordTrace (prefixWord ++ tailWord_7703192) baseStart_7703192 baseEnd_7703192 := by
    simpa [prefixWord, tailWord_7703192, baseEnd_7703192] using wordTrace_append hprefix tailTrace_7703192
  have hstable : (prefixWord ++ tailWord_7703192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703192).length < 2 ^ (prefixWord ++ tailWord_7703192).sum := by decide
  have hdescent : baseEnd_7703192 < baseStart_7703192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703215 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 3, 4, 2]
def baseStart_7703215 : Nat := 118140960795 + 7703215 * 2 ^ 59
def prefixEnd_7703215 : Nat := 4983230072969 + 3 ^ 40 * 7703215 * 2
def baseEnd_7703215 : Nat := 3955451879924183869586065

theorem tailTrace_7703215 : CollatzResearch.WordTrace tailWord_7703215 prefixEnd_7703215 3955451879924183869586065 := by
  unfold tailWord_7703215
  simp only [CollatzResearch.WordTrace]
  refine ⟨280959332787575134226495099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187306221858383422817663399 280959332787575134226495099)
  ·
    refine ⟨421438999181362701339742649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280959332787575134226495099 421438999181362701339742649)
    ·
      refine ⟨316079249386022026004806987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421438999181362701339742649 316079249386022026004806987)
      ·
        refine ⟨474118874079033039007210481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316079249386022026004806987 474118874079033039007210481)
        ·
          refine ⟨355589155559274779255407861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474118874079033039007210481 355589155559274779255407861)
          ·
            refine ⟨33336483333682010555194487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355589155559274779255407861 33336483333682010555194487)
            ·
              refine ⟨50004725000523015832791731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33336483333682010555194487 50004725000523015832791731)
              ·
                refine ⟨75007087500784523749187597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50004725000523015832791731 75007087500784523749187597)
                ·
                  refine ⟨28127657812794196405945349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75007087500784523749187597 28127657812794196405945349)
                  ·
                    refine ⟨5273935839898911826114753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28127657812794196405945349 5273935839898911826114753)
                    ·
                      refine ⟨3955451879924183869586065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273935839898911826114753 3955451879924183869586065)
                      ·
                        rfl

theorem cell23_7703215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 4, 2].length) (baseStart_7703215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703215 prefixEnd_7703215 := by exact prefixLift 7703215
  have htrace : WordTrace (prefixWord ++ tailWord_7703215) baseStart_7703215 baseEnd_7703215 := by
    simpa [prefixWord, tailWord_7703215, baseEnd_7703215] using wordTrace_append hprefix tailTrace_7703215
  have hstable : (prefixWord ++ tailWord_7703215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703215).length < 2 ^ (prefixWord ++ tailWord_7703215).sum := by decide
  have hdescent : baseEnd_7703215 < baseStart_7703215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703219 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 1, 3, 2]
def baseStart_7703219 : Nat := 118140960795 + 7703219 * 2 ^ 59
def prefixEnd_7703219 : Nat := 4983230072969 + 3 ^ 40 * 7703219 * 2
def baseEnd_7703219 : Nat := 3955453933846801853936047

theorem tailTrace_7703219 : CollatzResearch.WordTrace tailWord_7703219 prefixEnd_7703219 3955453933846801853936047 := by
  unfold tailWord_7703219
  simp only [CollatzResearch.WordTrace]
  refine ⟨280959478679560642909640711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187306319119707095273093807 280959478679560642909640711)
  ·
    refine ⟨421439218019340964364461067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280959478679560642909640711 421439218019340964364461067)
    ·
      refine ⟨632158827029011446546691601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421439218019340964364461067 632158827029011446546691601)
      ·
        refine ⟨474119120271758584910018701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632158827029011446546691601 474119120271758584910018701)
        ·
          refine ⟨177794670101909469341257013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474119120271758584910018701 177794670101909469341257013)
          ·
            refine ⟨16668250322054012750742845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177794670101909469341257013 16668250322054012750742845)
            ·
              refine ⟨6250593870770254781528567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16668250322054012750742845 6250593870770254781528567)
              ·
                refine ⟨9375890806155382172292851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6250593870770254781528567 9375890806155382172292851)
                ·
                  refine ⟨14063836209233073258439277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9375890806155382172292851 14063836209233073258439277)
                  ·
                    refine ⟨5273938578462402471914729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14063836209233073258439277 5273938578462402471914729)
                    ·
                      refine ⟨3955453933846801853936047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5273938578462402471914729 3955453933846801853936047)
                      ·
                        rfl

theorem cell23_7703219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 3, 2].length) (baseStart_7703219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703219 prefixEnd_7703219 := by exact prefixLift 7703219
  have htrace : WordTrace (prefixWord ++ tailWord_7703219) baseStart_7703219 baseEnd_7703219 := by
    simpa [prefixWord, tailWord_7703219, baseEnd_7703219] using wordTrace_append hprefix tailTrace_7703219
  have hstable : (prefixWord ++ tailWord_7703219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703219).length < 2 ^ (prefixWord ++ tailWord_7703219).sum := by decide
  have hdescent : baseEnd_7703219 < baseStart_7703219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703315 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 3, 4]
def baseStart_7703315 : Nat := 118140960795 + 7703315 * 2 ^ 59
def prefixEnd_7703315 : Nat := 4983230072969 + 3 ^ 40 * 7703315 * 2
def baseEnd_7703315 : Nat := 1318501075996544492778535

theorem tailTrace_7703315 : CollatzResearch.WordTrace tailWord_7703315 prefixEnd_7703315 1318501075996544492778535 := by
  unfold tailWord_7703315
  simp only [CollatzResearch.WordTrace]
  refine ⟨280962980087212851305135399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187308653391475234203423599 280962980087212851305135399)
  ·
    refine ⟨421444470130819276957703099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280962980087212851305135399 421444470130819276957703099)
    ·
      refine ⟨632166705196228915436554649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421444470130819276957703099 632166705196228915436554649)
      ·
        refine ⟨474125028897171686577415987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632166705196228915436554649 474125028897171686577415987)
        ·
          refine ⟨711187543345757529866123981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474125028897171686577415987 711187543345757529866123981)
          ·
            refine ⟨266695328754659073699796493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 711187543345757529866123981 266695328754659073699796493)
            ·
              refine ⟨100010748282997152637423685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266695328754659073699796493 100010748282997152637423685)
              ·
                refine ⟨18752015303061966119516941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100010748282997152637423685 18752015303061966119516941)
                ·
                  refine ⟨7032005738648237294818853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18752015303061966119516941 7032005738648237294818853)
                  ·
                    refine ⟨1318501075996544492778535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7032005738648237294818853 1318501075996544492778535)
                    ·
                      rfl

theorem cell23_7703315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 4].length) (baseStart_7703315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703315 prefixEnd_7703315 := by exact prefixLift 7703315
  have htrace : WordTrace (prefixWord ++ tailWord_7703315) baseStart_7703315 baseEnd_7703315 := by
    simpa [prefixWord, tailWord_7703315, baseEnd_7703315] using wordTrace_append hprefix tailTrace_7703315
  have hstable : (prefixWord ++ tailWord_7703315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703315).length < 2 ^ (prefixWord ++ tailWord_7703315).sum := by decide
  have hdescent : baseEnd_7703315 < baseStart_7703315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703345 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 6]
def baseStart_7703345 : Nat := 118140960795 + 7703345 * 2 ^ 59
def prefixEnd_7703345 : Nat := 4983230072969 + 3 ^ 40 * 7703345 * 2
def baseEnd_7703345 : Nat := 439502070267696484551163

theorem tailTrace_7703345 : CollatzResearch.WordTrace tailWord_7703345 prefixEnd_7703345 439502070267696484551163 := by
  unfold tailWord_7703345
  simp only [CollatzResearch.WordTrace]
  refine ⟨280964074277104166428727489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187309382851402777619151659 280964074277104166428727489)
  ·
    refine ⟨210723055707828124821545617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280964074277104166428727489 210723055707828124821545617)
    ·
      refine ⟨158042291780871093616159213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210723055707828124821545617 158042291780871093616159213)
      ·
        refine ⟨59265859417826660106059705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158042291780871093616159213 59265859417826660106059705)
        ·
          refine ⟨44449394563369995079544779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59265859417826660106059705 44449394563369995079544779)
          ·
            refine ⟨66674091845054992619317169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44449394563369995079544779 66674091845054992619317169)
            ·
              refine ⟨50005568883791244464487877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66674091845054992619317169 50005568883791244464487877)
              ·
                refine ⟨9376044165710858337091477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50005568883791244464487877 9376044165710858337091477)
                ·
                  refine ⟨439502070267696484551163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9376044165710858337091477 439502070267696484551163)
                  ·
                    rfl

theorem cell23_7703345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 6].length) (baseStart_7703345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703345 prefixEnd_7703345 := by exact prefixLift 7703345
  have htrace : WordTrace (prefixWord ++ tailWord_7703345) baseStart_7703345 baseEnd_7703345 := by
    simpa [prefixWord, tailWord_7703345, baseEnd_7703345] using wordTrace_append hprefix tailTrace_7703345
  have hstable : (prefixWord ++ tailWord_7703345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703345).length < 2 ^ (prefixWord ++ tailWord_7703345).sum := by decide
  have hdescent : baseEnd_7703345 < baseStart_7703345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703349 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_7703349 : Nat := 118140960795 + 7703349 * 2 ^ 59
def prefixEnd_7703349 : Nat := 4983230072969 + 3 ^ 40 * 7703349 * 2
def baseEnd_7703349 : Nat := 1318506895443962115103483

theorem tailTrace_7703349 : CollatzResearch.WordTrace tailWord_7703349 prefixEnd_7703349 1318506895443962115103483 := by
  unfold tailWord_7703349
  simp only [CollatzResearch.WordTrace]
  refine ⟨280964220169089675111873101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187309480112726450074582067 280964220169089675111873101)
  ·
    refine ⟨105361582563408628166952413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280964220169089675111873101 105361582563408628166952413)
    ·
      refine ⟨39510593461278235562607155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105361582563408628166952413 39510593461278235562607155)
      ·
        refine ⟨59265890191917353343910733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39510593461278235562607155 59265890191917353343910733)
        ·
          refine ⟨22224708821969007503966525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59265890191917353343910733 22224708821969007503966525)
          ·
            refine ⟨8334265808238377813987447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22224708821969007503966525 8334265808238377813987447)
            ·
              refine ⟨12501398712357566720981171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8334265808238377813987447 12501398712357566720981171)
              ·
                refine ⟨18752098068536350081471757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12501398712357566720981171 18752098068536350081471757)
                ·
                  refine ⟨7032036775701131280551909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18752098068536350081471757 7032036775701131280551909)
                  ·
                    refine ⟨1318506895443962115103483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7032036775701131280551909 1318506895443962115103483)
                    ·
                      rfl

theorem cell23_7703349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_7703349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703349 prefixEnd_7703349 := by exact prefixLift 7703349
  have htrace : WordTrace (prefixWord ++ tailWord_7703349) baseStart_7703349 baseEnd_7703349 := by
    simpa [prefixWord, tailWord_7703349, baseEnd_7703349] using wordTrace_append hprefix tailTrace_7703349
  have hstable : (prefixWord ++ tailWord_7703349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703349).length < 2 ^ (prefixWord ++ tailWord_7703349).sum := by decide
  have hdescent : baseEnd_7703349 < baseStart_7703349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703399 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_7703399 : Nat := 118140960795 + 7703399 * 2 ^ 59
def prefixEnd_7703399 : Nat := 4983230072969 + 3 ^ 40 * 7703399 * 2
def baseEnd_7703399 : Nat := 3955546360364611149685219

theorem tailTrace_7703399 : CollatzResearch.WordTrace tailWord_7703399 prefixEnd_7703399 3955546360364611149685219 := by
  unfold tailWord_7703399
  simp only [CollatzResearch.WordTrace]
  refine ⟨280966043818908533651193251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187310695879272355767462167 280966043818908533651193251)
  ·
    refine ⟨421449065728362800476789877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280966043818908533651193251 421449065728362800476789877)
    ·
      refine ⟨39510849912034012544699051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 421449065728362800476789877 39510849912034012544699051)
      ·
        refine ⟨59266274868051018817048577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39510849912034012544699051 59266274868051018817048577)
        ·
          refine ⟨44449706151038264112786433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59266274868051018817048577 44449706151038264112786433)
          ·
            refine ⟨33337279613278698084589825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44449706151038264112786433 33337279613278698084589825)
            ·
              refine ⟨25002959709959023563442369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33337279613278698084589825 25002959709959023563442369)
              ·
                refine ⟨18752219782469267672581777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25002959709959023563442369 18752219782469267672581777)
                ·
                  refine ⟨14064164836851950754436333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18752219782469267672581777 14064164836851950754436333)
                  ·
                    refine ⟨5274061813819481532913625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14064164836851950754436333 5274061813819481532913625)
                    ·
                      refine ⟨3955546360364611149685219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274061813819481532913625 3955546360364611149685219)
                      ·
                        rfl

theorem cell23_7703399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_7703399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703399 prefixEnd_7703399 := by exact prefixLift 7703399
  have htrace : WordTrace (prefixWord ++ tailWord_7703399) baseStart_7703399 baseEnd_7703399 := by
    simpa [prefixWord, tailWord_7703399, baseEnd_7703399] using wordTrace_append hprefix tailTrace_7703399
  have hstable : (prefixWord ++ tailWord_7703399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703399).length < 2 ^ (prefixWord ++ tailWord_7703399).sum := by decide
  have hdescent : baseEnd_7703399 < baseStart_7703399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703405 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_7703405 : Nat := 118140960795 + 7703405 * 2 ^ 59
def prefixEnd_7703405 : Nat := 4983230072969 + 3 ^ 40 * 7703405 * 2
def baseEnd_7703405 : Nat := 1318516480416179375403397

theorem tailTrace_7703405 : CollatzResearch.WordTrace tailWord_7703405 prefixEnd_7703405 1318516480416179375403397 := by
  unfold tailWord_7703405
  simp only [CollatzResearch.WordTrace]
  refine ⟨280966262656886796675911669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187310841771257864450607779 280966262656886796675911669)
  ·
    refine ⟨26340587124083137188366719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280966262656886796675911669 26340587124083137188366719)
    ·
      refine ⟨39510880686124705782550079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26340587124083137188366719 39510880686124705782550079)
      ·
        refine ⟨59266321029187058673825119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39510880686124705782550079 59266321029187058673825119)
        ·
          refine ⟨88899481543780588010737679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59266321029187058673825119 88899481543780588010737679)
          ·
            refine ⟨133349222315670882016106519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88899481543780588010737679 133349222315670882016106519)
            ·
              refine ⟨200023833473506323024159779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133349222315670882016106519 200023833473506323024159779)
              ·
                refine ⟨300035750210259484536239669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200023833473506323024159779 300035750210259484536239669)
                ·
                  refine ⟨28128351582211826675272469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300035750210259484536239669 28128351582211826675272469)
                  ·
                    refine ⟨1318516480416179375403397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28128351582211826675272469 1318516480416179375403397)
                    ·
                      rfl

theorem cell23_7703405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_7703405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703405 prefixEnd_7703405 := by exact prefixLift 7703405
  have htrace : WordTrace (prefixWord ++ tailWord_7703405) baseStart_7703405 baseEnd_7703405 := by
    simpa [prefixWord, tailWord_7703405, baseEnd_7703405] using wordTrace_append hprefix tailTrace_7703405
  have hstable : (prefixWord ++ tailWord_7703405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703405).length < 2 ^ (prefixWord ++ tailWord_7703405).sum := by decide
  have hdescent : baseEnd_7703405 < baseStart_7703405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703415 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_7703415 : Nat := 118140960795 + 7703415 * 2 ^ 59
def prefixEnd_7703415 : Nat := 4983230072969 + 3 ^ 40 * 7703415 * 2
def baseEnd_7703415 : Nat := 3955554576055083087085145

theorem tailTrace_7703415 : CollatzResearch.WordTrace tailWord_7703415 prefixEnd_7703415 3955554576055083087085145 := by
  unfold tailWord_7703415
  simp only [CollatzResearch.WordTrace]
  refine ⟨280966627386850568383775699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187311084924567045589183799 280966627386850568383775699)
  ·
    refine ⟨421449941080275852575663549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280966627386850568383775699 421449941080275852575663549)
    ·
      refine ⟨158043727905103444715873831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421449941080275852575663549 158043727905103444715873831)
      ·
        refine ⟨237065591857655167073810747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158043727905103444715873831 237065591857655167073810747)
        ·
          refine ⟨355598387786482750610716121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237065591857655167073810747 355598387786482750610716121)
          ·
            refine ⟨266698790839862062958037091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355598387786482750610716121 266698790839862062958037091)
            ·
              refine ⟨400048186259793094437055637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266698790839862062958037091 400048186259793094437055637)
              ·
                refine ⟨18752258730927801301736983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 400048186259793094437055637 18752258730927801301736983)
                ·
                  refine ⟨28128388096391701952605475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18752258730927801301736983 28128388096391701952605475)
                  ·
                    refine ⟨42192582144587552928908213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28128388096391701952605475 42192582144587552928908213)
                    ·
                      refine ⟨3955554576055083087085145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42192582144587552928908213 3955554576055083087085145)
                      ·
                        rfl

theorem cell23_7703415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_7703415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703415 prefixEnd_7703415 := by exact prefixLift 7703415
  have htrace : WordTrace (prefixWord ++ tailWord_7703415) baseStart_7703415 baseEnd_7703415 := by
    simpa [prefixWord, tailWord_7703415, baseEnd_7703415] using wordTrace_append hprefix tailTrace_7703415
  have hstable : (prefixWord ++ tailWord_7703415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703415).length < 2 ^ (prefixWord ++ tailWord_7703415).sum := by decide
  have hdescent : baseEnd_7703415 < baseStart_7703415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703429 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 5, 2, 2]
def baseStart_7703429 : Nat := 118140960795 + 7703429 * 2 ^ 59
def prefixEnd_7703429 : Nat := 4983230072969 + 3 ^ 40 * 7703429 * 2
def baseEnd_7703429 : Nat := 3955561764784246032310081

theorem tailTrace_7703429 : CollatzResearch.WordTrace tailWord_7703429 prefixEnd_7703429 3955561764784246032310081 := by
  unfold tailWord_7703429
  simp only [CollatzResearch.WordTrace]
  refine ⟨280967138008799848774785341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187311425339199899183190227 280967138008799848774785341)
  ·
    refine ⟨105362676753299943290544503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280967138008799848774785341 105362676753299943290544503)
    ·
      refine ⟨158044015129949914935816755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105362676753299943290544503 158044015129949914935816755)
      ·
        refine ⟨237066022694924872403725133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158044015129949914935816755 237066022694924872403725133)
        ·
          refine ⟨88899758510596827151396925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237066022694924872403725133 88899758510596827151396925)
          ·
            refine ⟨33337409441473810181773847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88899758510596827151396925 33337409441473810181773847)
            ·
              refine ⟨50006114162210715272660771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33337409441473810181773847 50006114162210715272660771)
              ·
                refine ⟨75009171243316072908991157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50006114162210715272660771 75009171243316072908991157)
                ·
                  refine ⟨7032109804060881835217921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75009171243316072908991157 7032109804060881835217921)
                  ·
                    refine ⟨5274082353045661376413441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7032109804060881835217921 5274082353045661376413441)
                    ·
                      refine ⟨3955561764784246032310081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274082353045661376413441 3955561764784246032310081)
                      ·
                        rfl

theorem cell23_7703429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_7703429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703429 prefixEnd_7703429 := by exact prefixLift 7703429
  have htrace : WordTrace (prefixWord ++ tailWord_7703429) baseStart_7703429 baseEnd_7703429 := by
    simpa [prefixWord, tailWord_7703429, baseEnd_7703429] using wordTrace_append hprefix tailTrace_7703429
  have hstable : (prefixWord ++ tailWord_7703429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703429).length < 2 ^ (prefixWord ++ tailWord_7703429).sum := by decide
  have hdescent : baseEnd_7703429 < baseStart_7703429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703452 : List Nat := [2, 2, 3, 3, 2, 1, 10]
def baseStart_7703452 : Nat := 118140960795 + 7703452 * 2 ^ 59
def prefixEnd_7703452 : Nat := 4983230072969 + 3 ^ 40 * 7703452 * 2
def baseEnd_7703452 : Nat := 48834241664682709164475

theorem tailTrace_7703452 : CollatzResearch.WordTrace tailWord_7703452 prefixEnd_7703452 48834241664682709164475 := by
  unfold tailWord_7703452
  simp only [CollatzResearch.WordTrace]
  refine ⟨140483988443858261851436305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187311984591811015801915073 140483988443858261851436305)
  ·
    refine ⟨105362991332893696388577229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140483988443858261851436305 105362991332893696388577229)
    ·
      refine ⟨39511121749835136145716461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105362991332893696388577229 39511121749835136145716461)
      ·
        refine ⟨14816670656188176054643673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39511121749835136145716461 14816670656188176054643673)
        ·
          refine ⟨11112502992141132040982755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14816670656188176054643673 11112502992141132040982755)
          ·
            refine ⟨16668754488211698061474133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112502992141132040982755 16668754488211698061474133)
            ·
              refine ⟨48834241664682709164475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16668754488211698061474133 48834241664682709164475)
              ·
                rfl

theorem cell23_7703452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 10].length) (baseStart_7703452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703452 prefixEnd_7703452 := by exact prefixLift 7703452
  have htrace : WordTrace (prefixWord ++ tailWord_7703452) baseStart_7703452 baseEnd_7703452 := by
    simpa [prefixWord, tailWord_7703452, baseEnd_7703452] using wordTrace_append hprefix tailTrace_7703452
  have hstable : (prefixWord ++ tailWord_7703452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703452).length < 2 ^ (prefixWord ++ tailWord_7703452).sum := by decide
  have hdescent : baseEnd_7703452 < baseStart_7703452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703463 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_7703463 : Nat := 118140960795 + 7703463 * 2 ^ 59
def prefixEnd_7703463 : Nat := 4983230072969 + 3 ^ 40 * 7703463 * 2
def baseEnd_7703463 : Nat := 3955579223126498899284925

theorem tailTrace_7703463 : CollatzResearch.WordTrace tailWord_7703463 prefixEnd_7703463 3955579223126498899284925 := by
  unfold tailWord_7703463
  simp only [CollatzResearch.WordTrace]
  refine ⟨280968378090676672581523043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187312252060451115054348695 280968378090676672581523043)
  ·
    refine ⟨421452567136015008872284565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280968378090676672581523043 421452567136015008872284565)
    ·
      refine ⟨19755589084500703540888339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 421452567136015008872284565 19755589084500703540888339)
      ·
        refine ⟨29633383626751055311332509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19755589084500703540888339 29633383626751055311332509)
        ·
          refine ⟨11112518860031645741749691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29633383626751055311332509 11112518860031645741749691)
          ·
            refine ⟨16668778290047468612624537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112518860031645741749691 16668778290047468612624537)
            ·
              refine ⟨12501583717535601459468403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16668778290047468612624537 12501583717535601459468403)
              ·
                refine ⟨18752375576303402189202605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12501583717535601459468403 18752375576303402189202605)
                ·
                  refine ⟨7032140841113775820950977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18752375576303402189202605 7032140841113775820950977)
                  ·
                    refine ⟨5274105630835331865713233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7032140841113775820950977 5274105630835331865713233)
                    ·
                      refine ⟨3955579223126498899284925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274105630835331865713233 3955579223126498899284925)
                      ·
                        rfl

theorem cell23_7703463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_7703463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703463 prefixEnd_7703463 := by exact prefixLift 7703463
  have htrace : WordTrace (prefixWord ++ tailWord_7703463) baseStart_7703463 baseEnd_7703463 := by
    simpa [prefixWord, tailWord_7703463, baseEnd_7703463] using wordTrace_append hprefix tailTrace_7703463
  have hstable : (prefixWord ++ tailWord_7703463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703463).length < 2 ^ (prefixWord ++ tailWord_7703463).sum := by decide
  have hdescent : baseEnd_7703463 < baseStart_7703463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703476 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_7703476 : Nat := 118140960795 + 7703476 * 2 ^ 59
def prefixEnd_7703476 : Nat := 4983230072969 + 3 ^ 40 * 7703476 * 2
def baseEnd_7703476 : Nat := 3955585898375007348422365

theorem tailTrace_7703476 : CollatzResearch.WordTrace tailWord_7703476 prefixEnd_7703476 3955585898375007348422365 := by
  unfold tailWord_7703476
  simp only [CollatzResearch.WordTrace]
  refine ⟨140484426119814787900873141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187312568159753050534497521 140484426119814787900873141)
  ·
    refine ⟨13170414948732636365706857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140484426119814787900873141 13170414948732636365706857)
    ·
      refine ⟨9877811211549477274280143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13170414948732636365706857 9877811211549477274280143)
      ·
        refine ⟨14816716817324215911420215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9877811211549477274280143 14816716817324215911420215)
        ·
          refine ⟨22225075225986323867130323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14816716817324215911420215 22225075225986323867130323)
          ·
            refine ⟨33337612838979485800695485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22225075225986323867130323 33337612838979485800695485)
            ·
              refine ⟨12501604814617307175260807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33337612838979485800695485 12501604814617307175260807)
              ·
                refine ⟨18752407221925960762891211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12501604814617307175260807 18752407221925960762891211)
                ·
                  refine ⟨28128610832888941144336817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18752407221925960762891211 28128610832888941144336817)
                  ·
                    refine ⟨21096458124666705858252613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28128610832888941144336817 21096458124666705858252613)
                    ·
                      refine ⟨3955585898375007348422365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21096458124666705858252613 3955585898375007348422365)
                      ·
                        rfl

theorem cell23_7703476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_7703476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703476 prefixEnd_7703476 := by exact prefixLift 7703476
  have htrace : WordTrace (prefixWord ++ tailWord_7703476) baseStart_7703476 baseEnd_7703476 := by
    simpa [prefixWord, tailWord_7703476, baseEnd_7703476] using wordTrace_append hprefix tailTrace_7703476
  have hstable : (prefixWord ++ tailWord_7703476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703476).length < 2 ^ (prefixWord ++ tailWord_7703476).sum := by decide
  have hdescent : baseEnd_7703476 < baseStart_7703476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703479 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_7703479 : Nat := 118140960795 + 7703479 * 2 ^ 59
def prefixEnd_7703479 : Nat := 4983230072969 + 3 ^ 40 * 7703479 * 2
def baseEnd_7703479 : Nat := 3955587438816970836684851

theorem tailTrace_7703479 : CollatzResearch.WordTrace tailWord_7703479 prefixEnd_7703479 3955587438816970836684851 := by
  unfold tailWord_7703479
  simp only [CollatzResearch.WordTrace]
  refine ⟨280968961658618707314105491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187312641105745804876070327 280968961658618707314105491)
  ·
    refine ⟨421453442487928060971158237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280968961658618707314105491 421453442487928060971158237)
    ·
      refine ⟨158045040932973022864184339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421453442487928060971158237 158045040932973022864184339)
      ·
        refine ⟨237067561399459534296276509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158045040932973022864184339 237067561399459534296276509)
        ·
          refine ⟨88900335524797325361103691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237067561399459534296276509 88900335524797325361103691)
          ·
            refine ⟨133350503287195988041655537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88900335524797325361103691 133350503287195988041655537)
            ·
              refine ⟨100012877465396991031241653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133350503287195988041655537 100012877465396991031241653)
              ·
                refine ⟨9376207262380967909178905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100012877465396991031241653 9376207262380967909178905)
                ·
                  refine ⟨7032155446785725931884179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9376207262380967909178905 7032155446785725931884179)
                  ·
                    refine ⟨10548233170178588897826269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7032155446785725931884179 10548233170178588897826269)
                    ·
                      refine ⟨3955587438816970836684851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10548233170178588897826269 3955587438816970836684851)
                      ·
                        rfl

theorem cell23_7703479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_7703479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703479 prefixEnd_7703479 := by exact prefixLift 7703479
  have htrace : WordTrace (prefixWord ++ tailWord_7703479) baseStart_7703479 baseEnd_7703479 := by
    simpa [prefixWord, tailWord_7703479, baseEnd_7703479] using wordTrace_append hprefix tailTrace_7703479
  have hstable : (prefixWord ++ tailWord_7703479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703479).length < 2 ^ (prefixWord ++ tailWord_7703479).sum := by decide
  have hdescent : baseEnd_7703479 < baseStart_7703479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703495 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 1, 8]
def baseStart_7703495 : Nat := 118140960795 + 7703495 * 2 ^ 59
def prefixEnd_7703495 : Nat := 4983230072969 + 3 ^ 40 * 7703495 * 2
def baseEnd_7703495 : Nat := 1318531884835814258028259

theorem tailTrace_7703495 : CollatzResearch.WordTrace tailWord_7703495 prefixEnd_7703495 1318531884835814258028259 := by
  unfold tailWord_7703495
  simp only [CollatzResearch.WordTrace]
  refine ⟨280969545226560742046687939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187313030151040494697791959 280969545226560742046687939)
  ·
    refine ⟨421454317839841113070031909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280969545226560742046687939 421454317839841113070031909)
    ·
      refine ⟨79022684594970208700630983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421454317839841113070031909 79022684594970208700630983)
      ·
        refine ⟨118534026892455313050946475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79022684594970208700630983 118534026892455313050946475)
        ·
          refine ⟨177801040338682969576419713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118534026892455313050946475 177801040338682969576419713)
          ·
            refine ⟨133350780254012227182314785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177801040338682969576419713 133350780254012227182314785)
            ·
              refine ⟨100013085190509170386736089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133350780254012227182314785 100013085190509170386736089)
              ·
                refine ⟨75009813892881877790052067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100013085190509170386736089 75009813892881877790052067)
                ·
                  refine ⟨112514720839322816685078101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75009813892881877790052067 112514720839322816685078101)
                  ·
                    refine ⟨1318531884835814258028259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112514720839322816685078101 1318531884835814258028259)
                    ·
                      rfl

theorem cell23_7703495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_7703495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703495 prefixEnd_7703495 := by exact prefixLift 7703495
  have htrace : WordTrace (prefixWord ++ tailWord_7703495) baseStart_7703495 baseEnd_7703495 := by
    simpa [prefixWord, tailWord_7703495, baseEnd_7703495] using wordTrace_append hprefix tailTrace_7703495
  have hstable : (prefixWord ++ tailWord_7703495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703495).length < 2 ^ (prefixWord ++ tailWord_7703495).sum := by decide
  have hdescent : baseEnd_7703495 < baseStart_7703495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703559 : List Nat := [1, 1, 4, 3, 1, 1, 2, 5, 5]
def baseStart_7703559 : Nat := 118140960795 + 7703559 * 2 ^ 59
def prefixEnd_7703559 : Nat := 4983230072969 + 3 ^ 40 * 7703559 * 2
def baseEnd_7703559 : Nat := 439514279696592280409387

theorem tailTrace_7703559 : CollatzResearch.WordTrace tailWord_7703559 prefixEnd_7703559 439514279696592280409387 := by
  unfold tailWord_7703559
  simp only [CollatzResearch.WordTrace]
  refine ⟨280971879498328880977017731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187314586332219253984678487 280971879498328880977017731)
  ·
    refine ⟨421457819247493321465526597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280971879498328880977017731 421457819247493321465526597)
    ·
      refine ⟨79023341108904997774786237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421457819247493321465526597 79023341108904997774786237)
      ·
        refine ⟨29633752915839374165544839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79023341108904997774786237 29633752915839374165544839)
        ·
          refine ⟨44450629373759061248317259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29633752915839374165544839 44450629373759061248317259)
          ·
            refine ⟨66675944060638591872475889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44450629373759061248317259 66675944060638591872475889)
            ·
              refine ⟨50006958045478943904356917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66675944060638591872475889 50006958045478943904356917)
              ·
                refine ⟨4688152316763650991033461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50006958045478943904356917 4688152316763650991033461)
                ·
                  refine ⟨439514279696592280409387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4688152316763650991033461 439514279696592280409387)
                  ·
                    rfl

theorem cell23_7703559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 5].length) (baseStart_7703559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703559 prefixEnd_7703559 := by exact prefixLift 7703559
  have htrace : WordTrace (prefixWord ++ tailWord_7703559) baseStart_7703559 baseEnd_7703559 := by
    simpa [prefixWord, tailWord_7703559, baseEnd_7703559] using wordTrace_append hprefix tailTrace_7703559
  have hstable : (prefixWord ++ tailWord_7703559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703559).length < 2 ^ (prefixWord ++ tailWord_7703559).sum := by decide
  have hdescent : baseEnd_7703559 < baseStart_7703559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703576 : List Nat := [2, 1, 2, 3, 2, 2, 4, 2, 5]
def baseStart_7703576 : Nat := 118140960795 + 7703576 * 2 ^ 59
def prefixEnd_7703576 : Nat := 4983230072969 + 3 ^ 40 * 7703576 * 2
def baseEnd_7703576 : Nat := 439515249604495217463545

theorem tailTrace_7703576 : CollatzResearch.WordTrace tailWord_7703576 prefixEnd_7703576 439515249604495217463545 := by
  unfold tailWord_7703576
  simp only [CollatzResearch.WordTrace]
  refine ⟨140486249769633646440193291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187314999692844861920257721 140486249769633646440193291)
  ·
    refine ⟨210729374654450469660289937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140486249769633646440193291 210729374654450469660289937)
    ·
      refine ⟨158047030990837852245217453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210729374654450469660289937 158047030990837852245217453)
      ·
        refine ⟨59267636621564194591956545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158047030990837852245217453 59267636621564194591956545)
        ·
          refine ⟨44450727466173145943967409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59267636621564194591956545 44450727466173145943967409)
          ·
            refine ⟨33338045599629859457975557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44450727466173145943967409 33338045599629859457975557)
            ·
              refine ⟨6250883549930598648370417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33338045599629859457975557 6250883549930598648370417)
              ·
                refine ⟨4688162662447948986277813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6250883549930598648370417 4688162662447948986277813)
                ·
                  refine ⟨439515249604495217463545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4688162662447948986277813 439515249604495217463545)
                  ·
                    rfl

theorem cell23_7703576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 5].length) (baseStart_7703576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703576 prefixEnd_7703576 := by exact prefixLift 7703576
  have htrace : WordTrace (prefixWord ++ tailWord_7703576) baseStart_7703576 baseEnd_7703576 := by
    simpa [prefixWord, tailWord_7703576, baseEnd_7703576] using wordTrace_append hprefix tailTrace_7703576
  have hstable : (prefixWord ++ tailWord_7703576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703576).length < 2 ^ (prefixWord ++ tailWord_7703576).sum := by decide
  have hdescent : baseEnd_7703576 < baseStart_7703576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703606 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_7703606 : Nat := 118140960795 + 7703606 * 2 ^ 59
def prefixEnd_7703606 : Nat := 4983230072969 + 3 ^ 40 * 7703606 * 2
def baseEnd_7703606 : Nat := 1318550883620030613265589

theorem tailTrace_7703606 : CollatzResearch.WordTrace tailWord_7703606 prefixEnd_7703606 1318550883620030613265589 := by
  unfold tailWord_7703606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560849608072413000248667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187315729152772405335985781 17560849608072413000248667)
  ·
    refine ⟨26341274412108619500373001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17560849608072413000248667 26341274412108619500373001)
    ·
      refine ⟨19755955809081464625279751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26341274412108619500373001 19755955809081464625279751)
      ·
        refine ⟨29633933713622196937919627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19755955809081464625279751 29633933713622196937919627)
        ·
          refine ⟨44450900570433295406879441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29633933713622196937919627 44450900570433295406879441)
          ·
            refine ⟨33338175427824971555159581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44450900570433295406879441 33338175427824971555159581)
            ·
              refine ⟨12501815785434364333184843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33338175427824971555159581 12501815785434364333184843)
              ·
                refine ⟨18752723678151546499777265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12501815785434364333184843 18752723678151546499777265)
                ·
                  refine ⟨14064542758613659874832949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18752723678151546499777265 14064542758613659874832949)
                  ·
                    refine ⟨1318550883620030613265589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14064542758613659874832949 1318550883620030613265589)
                    ·
                      rfl

theorem cell23_7703606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_7703606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703606 prefixEnd_7703606 := by exact prefixLift 7703606
  have htrace : WordTrace (prefixWord ++ tailWord_7703606) baseStart_7703606 baseEnd_7703606 := by
    simpa [prefixWord, tailWord_7703606, baseEnd_7703606] using wordTrace_append hprefix tailTrace_7703606
  have hstable : (prefixWord ++ tailWord_7703606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703606).length < 2 ^ (prefixWord ++ tailWord_7703606).sum := by decide
  have hdescent : baseEnd_7703606 < baseStart_7703606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703609 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7703609 : Nat := 118140960795 + 7703609 * 2 ^ 59
def prefixEnd_7703609 : Nat := 4983230072969 + 3 ^ 40 * 7703609 * 2
def baseEnd_7703609 : Nat := 3955654191302055328059253

theorem tailTrace_7703609 : CollatzResearch.WordTrace tailWord_7703609 prefixEnd_7703609 3955654191302055328059253 := by
  unfold tailWord_7703609
  simp only [CollatzResearch.WordTrace]
  refine ⟨280973703148147739516337881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187315802098765159677558587 280973703148147739516337881)
  ·
    refine ⟨210730277361110804637253411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280973703148147739516337881 210730277361110804637253411)
    ·
      refine ⟨316095416041666206955880117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210730277361110804637253411 316095416041666206955880117)
      ·
        refine ⟨29633945253906206902113761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316095416041666206955880117 29633945253906206902113761)
        ·
          refine ⟨22225458940429655176585321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29633945253906206902113761 22225458940429655176585321)
          ·
            refine ⟨16669094205322241382438991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22225458940429655176585321 16669094205322241382438991)
            ·
              refine ⟨25003641307983362073658487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16669094205322241382438991 25003641307983362073658487)
              ·
                refine ⟨37505461961975043110487731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25003641307983362073658487 37505461961975043110487731)
                ·
                  refine ⟨56258192942962564665731597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37505461961975043110487731 56258192942962564665731597)
                  ·
                    refine ⟨21096822353610961749649349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56258192942962564665731597 21096822353610961749649349)
                    ·
                      refine ⟨3955654191302055328059253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21096822353610961749649349 3955654191302055328059253)
                      ·
                        rfl

theorem cell23_7703609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7703609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703609 prefixEnd_7703609 := by exact prefixLift 7703609
  have htrace : WordTrace (prefixWord ++ tailWord_7703609) baseStart_7703609 baseEnd_7703609 := by
    simpa [prefixWord, tailWord_7703609, baseEnd_7703609] using wordTrace_append hprefix tailTrace_7703609
  have hstable : (prefixWord ++ tailWord_7703609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703609).length < 2 ^ (prefixWord ++ tailWord_7703609).sum := by decide
  have hdescent : baseEnd_7703609 < baseStart_7703609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703652 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_7703652 : Nat := 118140960795 + 7703652 * 2 ^ 59
def prefixEnd_7703652 : Nat := 4983230072969 + 3 ^ 40 * 7703652 * 2
def baseEnd_7703652 : Nat := 3955676270970198659821555

theorem tailTrace_7703652 : CollatzResearch.WordTrace tailWord_7703652 prefixEnd_7703652 3955676270970198659821555 := by
  unfold tailWord_7703652
  simp only [CollatzResearch.WordTrace]
  refine ⟨140487635743495978930076605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187316847657994638573435473 140487635743495978930076605)
  ·
    refine ⟨52682863403810992098778727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140487635743495978930076605 52682863403810992098778727)
    ·
      refine ⟨79024295105716488148168091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52682863403810992098778727 79024295105716488148168091)
      ·
        refine ⟨118536442658574732222252137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79024295105716488148168091 118536442658574732222252137)
        ·
          refine ⟨88902331993931049166689103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118536442658574732222252137 88902331993931049166689103)
          ·
            refine ⟨133353497990896573750033655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88902331993931049166689103 133353497990896573750033655)
            ·
              refine ⟨200030246986344860625050483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133353497990896573750033655 200030246986344860625050483)
              ·
                refine ⟨300045370479517290937575725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200030246986344860625050483 300045370479517290937575725)
                ·
                  refine ⟨112517013929818984101590897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300045370479517290937575725 112517013929818984101590897)
                  ·
                    refine ⟨84387760447364238076193173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112517013929818984101590897 84387760447364238076193173)
                    ·
                      refine ⟨3955676270970198659821555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84387760447364238076193173 3955676270970198659821555)
                      ·
                        rfl

theorem cell23_7703652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_7703652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703652 prefixEnd_7703652 := by exact prefixLift 7703652
  have htrace : WordTrace (prefixWord ++ tailWord_7703652) baseStart_7703652 baseEnd_7703652 := by
    simpa [prefixWord, tailWord_7703652, baseEnd_7703652] using wordTrace_append hprefix tailTrace_7703652
  have hstable : (prefixWord ++ tailWord_7703652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703652).length < 2 ^ (prefixWord ++ tailWord_7703652).sum := by decide
  have hdescent : baseEnd_7703652 < baseStart_7703652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703709 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7703709 : Nat := 118140960795 + 7703709 * 2 ^ 59
def prefixEnd_7703709 : Nat := 4983230072969 + 3 ^ 40 * 7703709 * 2
def baseEnd_7703709 : Nat := 1318568513122501645602931

theorem tailTrace_7703709 : CollatzResearch.WordTrace tailWord_7703709 prefixEnd_7703709 1318568513122501645602931 := by
  unfold tailWord_7703709
  simp only [CollatzResearch.WordTrace]
  refine ⟨280977350447785456594978181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187318233631856971063318787 280977350447785456594978181)
  ·
    refine ⟨52683253208959773111558409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280977350447785456594978181 52683253208959773111558409)
    ·
      refine ⟨39512439906719829833668807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52683253208959773111558409 39512439906719829833668807)
      ·
        refine ⟨59268659860079744750503211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39512439906719829833668807 59268659860079744750503211)
        ·
          refine ⟨88902989790119617125754817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59268659860079744750503211 88902989790119617125754817)
          ·
            refine ⟨66677242342589712844316113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88902989790119617125754817 66677242342589712844316113)
            ·
              refine ⟨50007931756942284633237085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66677242342589712844316113 50007931756942284633237085)
              ·
                refine ⟨18752974408853356737463907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50007931756942284633237085 18752974408853356737463907)
                ·
                  refine ⟨28129461613280035106195861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18752974408853356737463907 28129461613280035106195861)
                  ·
                    refine ⟨1318568513122501645602931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28129461613280035106195861 1318568513122501645602931)
                    ·
                      rfl

theorem cell23_7703709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7703709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703709 prefixEnd_7703709 := by exact prefixLift 7703709
  have htrace : WordTrace (prefixWord ++ tailWord_7703709) baseStart_7703709 baseEnd_7703709 := by
    simpa [prefixWord, tailWord_7703709, baseEnd_7703709] using wordTrace_append hprefix tailTrace_7703709
  have hstable : (prefixWord ++ tailWord_7703709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703709).length < 2 ^ (prefixWord ++ tailWord_7703709).sum := by decide
  have hdescent : baseEnd_7703709 < baseStart_7703709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703716 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_7703716 : Nat := 118140960795 + 7703716 * 2 ^ 59
def prefixEnd_7703716 : Nat := 4983230072969 + 3 ^ 40 * 7703716 * 2
def baseEnd_7703716 : Nat := 3955709133732086409421261

theorem tailTrace_7703716 : CollatzResearch.WordTrace tailWord_7703716 prefixEnd_7703716 3955709133732086409421261 := by
  unfold tailWord_7703716
  simp only [CollatzResearch.WordTrace]
  refine ⟨140488802879380048395241501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187318403839173397860322001 140488802879380048395241501)
  ·
    refine ⟨52683301079767518148215563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140488802879380048395241501 52683301079767518148215563)
    ·
      refine ⟨79024951619651277222323345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52683301079767518148215563 79024951619651277222323345)
      ·
        refine ⟨59268713714738457916742509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79024951619651277222323345 59268713714738457916742509)
        ·
          refine ⟨22225767643026921718778441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59268713714738457916742509 22225767643026921718778441)
          ·
            refine ⟨16669325732270191289083831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22225767643026921718778441 16669325732270191289083831)
            ·
              refine ⟨25003988598405286933625747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16669325732270191289083831 25003988598405286933625747)
              ·
                refine ⟨37505982897607930400438621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25003988598405286933625747 37505982897607930400438621)
                ·
                  refine ⟨14064743586602973900164483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37505982897607930400438621 14064743586602973900164483)
                  ·
                    refine ⟨21097115379904460850246725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14064743586602973900164483 21097115379904460850246725)
                    ·
                      refine ⟨3955709133732086409421261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21097115379904460850246725 3955709133732086409421261)
                      ·
                        rfl

theorem cell23_7703716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_7703716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703716 prefixEnd_7703716 := by exact prefixLift 7703716
  have htrace : WordTrace (prefixWord ++ tailWord_7703716) baseStart_7703716 baseEnd_7703716 := by
    simpa [prefixWord, tailWord_7703716, baseEnd_7703716] using wordTrace_append hprefix tailTrace_7703716
  have hstable : (prefixWord ++ tailWord_7703716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703716).length < 2 ^ (prefixWord ++ tailWord_7703716).sum := by decide
  have hdescent : baseEnd_7703716 < baseStart_7703716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703744 : List Nat := [2, 1, 1, 2, 7, 1, 2, 2, 1, 1, 3]
def baseStart_7703744 : Nat := 118140960795 + 7703744 * 2 ^ 59
def prefixEnd_7703744 : Nat := 4983230072969 + 3 ^ 40 * 7703744 * 2
def baseEnd_7703744 : Nat := 3955723511190412299871133

theorem tailTrace_7703744 : CollatzResearch.WordTrace tailWord_7703744 prefixEnd_7703744 3955723511190412299871133 := by
  unfold tailWord_7703744
  simp only [CollatzResearch.WordTrace]
  refine ⟨140489313501329328786251143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187319084668439105048334857 140489313501329328786251143)
  ·
    refine ⟨210733970251993993179376715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140489313501329328786251143 210733970251993993179376715)
    ·
      refine ⟨316100955377990989769065073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210733970251993993179376715 316100955377990989769065073)
      ·
        refine ⟨237075716533493242326798805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316100955377990989769065073 237075716533493242326798805)
        ·
          refine ⟨5556462106253747867034347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 237075716533493242326798805 5556462106253747867034347)
          ·
            refine ⟨8334693159380621800551521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556462106253747867034347 8334693159380621800551521)
            ·
              refine ⟨6251019869535466350413641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8334693159380621800551521 6251019869535466350413641)
              ·
                refine ⟨4688264902151599762810231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251019869535466350413641 4688264902151599762810231)
                ·
                  refine ⟨7032397353227399644215347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688264902151599762810231 7032397353227399644215347)
                  ·
                    refine ⟨10548596029841099466323021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7032397353227399644215347 10548596029841099466323021)
                    ·
                      refine ⟨3955723511190412299871133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10548596029841099466323021 3955723511190412299871133)
                      ·
                        rfl

theorem cell23_7703744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_7703744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703744 prefixEnd_7703744 := by exact prefixLift 7703744
  have htrace : WordTrace (prefixWord ++ tailWord_7703744) baseStart_7703744 baseEnd_7703744 := by
    simpa [prefixWord, tailWord_7703744, baseEnd_7703744] using wordTrace_append hprefix tailTrace_7703744
  have hstable : (prefixWord ++ tailWord_7703744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703744).length < 2 ^ (prefixWord ++ tailWord_7703744).sum := by decide
  have hdescent : baseEnd_7703744 < baseStart_7703744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703749 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_7703749 : Nat := 118140960795 + 7703749 * 2 ^ 59
def prefixEnd_7703749 : Nat := 4983230072969 + 3 ^ 40 * 7703749 * 2
def baseEnd_7703749 : Nat := 3955726078593684780308609

theorem tailTrace_7703749 : CollatzResearch.WordTrace tailWord_7703749 prefixEnd_7703749 3955726078593684780308609 := by
  unfold tailWord_7703749
  simp only [CollatzResearch.WordTrace]
  refine ⟨280978809367640543426434301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187319206245093695617622867 280978809367640543426434301)
  ·
    refine ⟨105367053512865203784912863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280978809367640543426434301 105367053512865203784912863)
    ·
      refine ⟨158050580269297805677369295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105367053512865203784912863 158050580269297805677369295)
      ·
        refine ⟨237075870403946708516053943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158050580269297805677369295 237075870403946708516053943)
        ·
          refine ⟨355613805605920062774080915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237075870403946708516053943 355613805605920062774080915)
          ·
            refine ⟨533420708408880094161121373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355613805605920062774080915 533420708408880094161121373)
            ·
              refine ⟨200032765653330035310420515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533420708408880094161121373 200032765653330035310420515)
              ·
                refine ⟨300049148479995052965630773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200032765653330035310420515 300049148479995052965630773)
                ·
                  refine ⟨28129607669999536215527885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300049148479995052965630773 28129607669999536215527885)
                  ·
                    refine ⟨10548602876249826080822957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28129607669999536215527885 10548602876249826080822957)
                    ·
                      refine ⟨3955726078593684780308609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10548602876249826080822957 3955726078593684780308609)
                      ·
                        rfl

theorem cell23_7703749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_7703749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703749 prefixEnd_7703749 := by exact prefixLift 7703749
  have htrace : WordTrace (prefixWord ++ tailWord_7703749) baseStart_7703749 baseEnd_7703749 := by
    simpa [prefixWord, tailWord_7703749, baseEnd_7703749] using wordTrace_append hprefix tailTrace_7703749
  have hstable : (prefixWord ++ tailWord_7703749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703749).length < 2 ^ (prefixWord ++ tailWord_7703749).sum := by decide
  have hdescent : baseEnd_7703749 < baseStart_7703749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703773 : List Nat := [1, 4, 3, 2, 2, 1, 3, 7]
def baseStart_7703773 : Nat := 118140960795 + 7703773 * 2 ^ 59
def prefixEnd_7703773 : Nat := 4983230072969 + 3 ^ 40 * 7703773 * 2
def baseEnd_7703773 : Nat := 146508829708496025422537

theorem tailTrace_7703773 : CollatzResearch.WordTrace tailWord_7703773 prefixEnd_7703773 146508829708496025422537 := by
  unfold tailWord_7703773
  simp only [CollatzResearch.WordTrace]
  refine ⟨280979684719553595525307973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187319789813035730350205315 280979684719553595525307973)
  ·
    refine ⟨52683690884916299160995245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280979684719553595525307973 52683690884916299160995245)
    ·
      refine ⟨19756384081843612185373217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52683690884916299160995245 19756384081843612185373217)
      ·
        refine ⟨14817288061382709139029913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19756384081843612185373217 14817288061382709139029913)
        ·
          refine ⟨11112966046037031854272435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14817288061382709139029913 11112966046037031854272435)
          ·
            refine ⟨16669449069055547781408653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112966046037031854272435 16669449069055547781408653)
            ·
              refine ⟨6251043400895830418028245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16669449069055547781408653 6251043400895830418028245)
              ·
                refine ⟨146508829708496025422537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6251043400895830418028245 146508829708496025422537)
                ·
                  rfl

theorem cell23_7703773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 7].length) (baseStart_7703773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703773 prefixEnd_7703773 := by exact prefixLift 7703773
  have htrace : WordTrace (prefixWord ++ tailWord_7703773) baseStart_7703773 baseEnd_7703773 := by
    simpa [prefixWord, tailWord_7703773, baseEnd_7703773] using wordTrace_append hprefix tailTrace_7703773
  have hstable : (prefixWord ++ tailWord_7703773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703773).length < 2 ^ (prefixWord ++ tailWord_7703773).sum := by decide
  have hdescent : baseEnd_7703773 < baseStart_7703773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703878 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7703878 : Nat := 118140960795 + 7703878 * 2 ^ 59
def prefixEnd_7703878 : Nat := 4983230072969 + 3 ^ 40 * 7703878 * 2
def baseEnd_7703878 : Nat := 3955792317598114775595517

theorem tailTrace_7703878 : CollatzResearch.WordTrace tailWord_7703878 prefixEnd_7703878 3955792317598114775595517 := by
  unfold tailWord_7703878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780734824505412451808759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187322342922782132305253525 8780734824505412451808759)
  ·
    refine ⟨13171102236758118677713139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8780734824505412451808759 13171102236758118677713139)
    ·
      refine ⟨19756653355137178016569709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13171102236758118677713139 19756653355137178016569709)
      ·
        refine ⟨7408745008176441756213641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19756653355137178016569709 7408745008176441756213641)
        ·
          refine ⟨5556558756132331317160231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7408745008176441756213641 5556558756132331317160231)
          ·
            refine ⟨8334838134198496975740347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556558756132331317160231 8334838134198496975740347)
            ·
              refine ⟨12502257201297745463610521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8334838134198496975740347 12502257201297745463610521)
              ·
                refine ⟨9376692900973309097707891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12502257201297745463610521 9376692900973309097707891)
                ·
                  refine ⟨14065039351459963646561837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9376692900973309097707891 14065039351459963646561837)
                  ·
                    refine ⟨5274389756797486367460689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14065039351459963646561837 5274389756797486367460689)
                    ·
                      refine ⟨3955792317598114775595517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274389756797486367460689 3955792317598114775595517)
                      ·
                        rfl

theorem cell23_7703878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7703878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703878 prefixEnd_7703878 := by exact prefixLift 7703878
  have htrace : WordTrace (prefixWord ++ tailWord_7703878) baseStart_7703878 baseEnd_7703878 := by
    simpa [prefixWord, tailWord_7703878, baseEnd_7703878] using wordTrace_append hprefix tailTrace_7703878
  have hstable : (prefixWord ++ tailWord_7703878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703878).length < 2 ^ (prefixWord ++ tailWord_7703878).sum := by decide
  have hdescent : baseEnd_7703878 < baseStart_7703878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703893 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_7703893 : Nat := 118140960795 + 7703893 * 2 ^ 59
def prefixEnd_7703893 : Nat := 4983230072969 + 3 ^ 40 * 7703893 * 2
def baseEnd_7703893 : Nat := 1318600006602644072302649

theorem tailTrace_7703893 : CollatzResearch.WordTrace tailWord_7703893 prefixEnd_7703893 1318600006602644072302649 := by
  unfold tailWord_7703893
  simp only [CollatzResearch.WordTrace]
  refine ⟨280984061479118856019676333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187322707652745904013117555 280984061479118856019676333)
  ·
    refine ⟨105369023054669571007378625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280984061479118856019676333 105369023054669571007378625)
    ·
      refine ⟨79026767291002178255533969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105369023054669571007378625 79026767291002178255533969)
      ·
        refine ⟨59270075468251633691650477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79026767291002178255533969 59270075468251633691650477)
        ·
          refine ⟨22226278300594362634368929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59270075468251633691650477 22226278300594362634368929)
          ·
            refine ⟨16669708725445771975776697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22226278300594362634368929 16669708725445771975776697)
            ·
              refine ⟨12502281544084328981832523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16669708725445771975776697 12502281544084328981832523)
              ·
                refine ⟨18753422316126493472748785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12502281544084328981832523 18753422316126493472748785)
                ·
                  refine ⟨14065066737094870104561589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18753422316126493472748785 14065066737094870104561589)
                  ·
                    refine ⟨1318600006602644072302649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14065066737094870104561589 1318600006602644072302649)
                    ·
                      rfl

theorem cell23_7703893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_7703893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703893 prefixEnd_7703893 := by exact prefixLift 7703893
  have htrace : WordTrace (prefixWord ++ tailWord_7703893) baseStart_7703893 baseEnd_7703893 := by
    simpa [prefixWord, tailWord_7703893, baseEnd_7703893] using wordTrace_append hprefix tailTrace_7703893
  have hstable : (prefixWord ++ tailWord_7703893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703893).length < 2 ^ (prefixWord ++ tailWord_7703893).sum := by decide
  have hdescent : baseEnd_7703893 < baseStart_7703893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703914 : List Nat := [3, 1, 3, 3, 3, 1, 2, 2, 5]
def baseStart_7703914 : Nat := 118140960795 + 7703914 * 2 ^ 59
def prefixEnd_7703914 : Nat := 4983230072969 + 3 ^ 40 * 7703914 * 2
def baseEnd_7703914 : Nat := 439534533655741848305039

theorem tailTrace_7703914 : CollatzResearch.WordTrace tailWord_7703914 prefixEnd_7703914 439534533655741848305039 := by
  unfold tailWord_7703914
  simp only [CollatzResearch.WordTrace]
  refine ⟨70246206853010694151547699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187323218274695184404127197 70246206853010694151547699)
  ·
    refine ⟨105369310279516041227321549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70246206853010694151547699 105369310279516041227321549)
    ·
      refine ⟨39513491354818515460245581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105369310279516041227321549 39513491354818515460245581)
      ·
        refine ⟨14817559258056943297592093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39513491354818515460245581 14817559258056943297592093)
        ·
          refine ⟨5556584721771353736597035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14817559258056943297592093 5556584721771353736597035)
          ·
            refine ⟨8334877082657030604895553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556584721771353736597035 8334877082657030604895553)
            ·
              refine ⟨6251157811992772953671665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8334877082657030604895553 6251157811992772953671665)
              ·
                refine ⟨4688368358994579715253749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251157811992772953671665 4688368358994579715253749)
                ·
                  refine ⟨439534533655741848305039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4688368358994579715253749 439534533655741848305039)
                  ·
                    rfl

theorem cell23_7703914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_7703914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703914 prefixEnd_7703914 := by exact prefixLift 7703914
  have htrace : WordTrace (prefixWord ++ tailWord_7703914) baseStart_7703914 baseEnd_7703914 := by
    simpa [prefixWord, tailWord_7703914, baseEnd_7703914] using wordTrace_append hprefix tailTrace_7703914
  have hstable : (prefixWord ++ tailWord_7703914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703914).length < 2 ^ (prefixWord ++ tailWord_7703914).sum := by decide
  have hdescent : baseEnd_7703914 < baseStart_7703914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703950 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7703950 : Nat := 118140960795 + 7703950 * 2 ^ 59
def prefixEnd_7703950 : Nat := 4983230072969 + 3 ^ 40 * 7703950 * 2
def baseEnd_7703950 : Nat := 3955829288205238493895185

theorem tailTrace_7703950 : CollatzResearch.WordTrace tailWord_7703950 prefixEnd_7703950 3955829288205238493895185 := by
  unfold tailWord_7703950
  simp only [CollatzResearch.WordTrace]
  refine ⟨35123267554989044344312663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187324093626608236503000869 35123267554989044344312663)
  ·
    refine ⟨52684901332483566516468995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35123267554989044344312663 52684901332483566516468995)
    ·
      refine ⟨79027351998725349774703493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52684901332483566516468995 79027351998725349774703493)
      ·
        refine ⟨14817628499761003082756905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79027351998725349774703493 14817628499761003082756905)
        ·
          refine ⟨11113221374820752312067679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14817628499761003082756905 11113221374820752312067679)
          ·
            refine ⟨16669832062231128468101519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11113221374820752312067679 16669832062231128468101519)
            ·
              refine ⟨25004748093346692702152279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16669832062231128468101519 25004748093346692702152279)
              ·
                refine ⟨37507122140020039053228419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25004748093346692702152279 37507122140020039053228419)
                ·
                  refine ⟨56260683210030058579842629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37507122140020039053228419 56260683210030058579842629)
                  ·
                    refine ⟨10548878101880635983720493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56260683210030058579842629 10548878101880635983720493)
                    ·
                      refine ⟨3955829288205238493895185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10548878101880635983720493 3955829288205238493895185)
                      ·
                        rfl

theorem cell23_7703950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7703950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703950 prefixEnd_7703950 := by exact prefixLift 7703950
  have htrace : WordTrace (prefixWord ++ tailWord_7703950) baseStart_7703950 baseEnd_7703950 := by
    simpa [prefixWord, tailWord_7703950, baseEnd_7703950] using wordTrace_append hprefix tailTrace_7703950
  have hstable : (prefixWord ++ tailWord_7703950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703950).length < 2 ^ (prefixWord ++ tailWord_7703950).sum := by decide
  have hdescent : baseEnd_7703950 < baseStart_7703950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703970 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 6]
def baseStart_7703970 : Nat := 118140960795 + 7703970 * 2 ^ 59
def prefixEnd_7703970 : Nat := 4983230072969 + 3 ^ 40 * 7703970 * 2
def baseEnd_7703970 : Nat := 439537728646480935071677

theorem tailTrace_7703970 : CollatzResearch.WordTrace tailWord_7703970 prefixEnd_7703970 439537728646480935071677 := by
  unfold tailWord_7703970
  simp only [CollatzResearch.WordTrace]
  refine ⟨70246717474959974542557341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187324579933226598780152909 70246717474959974542557341)
  ·
    refine ⟨26342519053109990453459003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70246717474959974542557341 26342519053109990453459003)
    ·
      refine ⟨39513778579664985680188505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26342519053109990453459003 39513778579664985680188505)
      ·
        refine ⟨29635333934748739260141379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39513778579664985680188505 29635333934748739260141379)
        ·
          refine ⟨44453000902123108890212069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29635333934748739260141379 44453000902123108890212069)
          ·
            refine ⟨8334937669148082916914763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44453000902123108890212069 8334937669148082916914763)
            ·
              refine ⟨12502406503722124375372145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8334937669148082916914763 12502406503722124375372145)
              ·
                refine ⟨9376804877791593281529109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12502406503722124375372145 9376804877791593281529109)
                ·
                  refine ⟨439537728646480935071677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9376804877791593281529109 439537728646480935071677)
                  ·
                    rfl

theorem cell23_7703970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_7703970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703970 prefixEnd_7703970 := by exact prefixLift 7703970
  have htrace : WordTrace (prefixWord ++ tailWord_7703970) baseStart_7703970 baseEnd_7703970 := by
    simpa [prefixWord, tailWord_7703970, baseEnd_7703970] using wordTrace_append hprefix tailTrace_7703970
  have hstable : (prefixWord ++ tailWord_7703970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703970).length < 2 ^ (prefixWord ++ tailWord_7703970).sum := by decide
  have hdescent : baseEnd_7703970 < baseStart_7703970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7703986 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_7703986 : Nat := 118140960795 + 7703986 * 2 ^ 59
def prefixEnd_7703986 : Nat := 4983230072969 + 3 ^ 40 * 7703986 * 2
def baseEnd_7703986 : Nat := 3955847773508800353045019

theorem tailTrace_7703986 : CollatzResearch.WordTrace tailWord_7703986 prefixEnd_7703986 3955847773508800353045019 := by
  unfold tailWord_7703986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70246863366945483225702953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187324968978521288601874541 70246863366945483225702953)
  ·
    refine ⟨52685147525209112419277215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70246863366945483225702953 52685147525209112419277215)
    ·
      refine ⟨79027721287813668628915823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52685147525209112419277215 79027721287813668628915823)
      ·
        refine ⟨118541581931720502943373735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79027721287813668628915823 118541581931720502943373735)
        ·
          refine ⟨177812372897580754415060603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118541581931720502943373735 177812372897580754415060603)
          ·
            refine ⟨266718559346371131622590905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177812372897580754415060603 266718559346371131622590905)
            ·
              refine ⟨200038919509778348716943179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266718559346371131622590905 200038919509778348716943179)
              ·
                refine ⟨300058379264667523075414769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200038919509778348716943179 300058379264667523075414769)
                ·
                  refine ⟨225043784448500642306561077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300058379264667523075414769 225043784448500642306561077)
                  ·
                    refine ⟨21097854792046935216240101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225043784448500642306561077 21097854792046935216240101)
                    ·
                      refine ⟨3955847773508800353045019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21097854792046935216240101 3955847773508800353045019)
                      ·
                        rfl

theorem cell23_7703986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_7703986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7703986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7703986 prefixEnd_7703986 := by exact prefixLift 7703986
  have htrace : WordTrace (prefixWord ++ tailWord_7703986) baseStart_7703986 baseEnd_7703986 := by
    simpa [prefixWord, tailWord_7703986, baseEnd_7703986] using wordTrace_append hprefix tailTrace_7703986
  have hstable : (prefixWord ++ tailWord_7703986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7703986).length < 2 ^ (prefixWord ++ tailWord_7703986).sum := by decide
  have hdescent : baseEnd_7703986 < baseStart_7703986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7703986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704003 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 4]
def baseStart_7704003 : Nat := 118140960795 + 7704003 * 2 ^ 59
def prefixEnd_7704003 : Nat := 4983230072969 + 3 ^ 40 * 7704003 * 2
def baseEnd_7704003 : Nat := 3955856502679926786532441

theorem tailTrace_7704003 : CollatzResearch.WordTrace tailWord_7704003 prefixEnd_7704003 3955856502679926786532441 := by
  unfold tailWord_7704003
  simp only [CollatzResearch.WordTrace]
  refine ⟨280988073508720344806180663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187325382339146896537453775 280988073508720344806180663)
  ·
    refine ⟨421482110263080517209270995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280988073508720344806180663 421482110263080517209270995)
    ·
      refine ⟨632223165394620775813906493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421482110263080517209270995 632223165394620775813906493)
      ·
        refine ⟨237083687022982790930214935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 632223165394620775813906493 237083687022982790930214935)
        ·
          refine ⟨355625530534474186395322403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237083687022982790930214935 355625530534474186395322403)
          ·
            refine ⟨533438295801711279592983605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355625530534474186395322403 533438295801711279592983605)
            ·
              refine ⟨50009840231410432461842213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533438295801711279592983605 50009840231410432461842213)
              ·
                refine ⟨9376845043389456086595415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50009840231410432461842213 9376845043389456086595415)
                ·
                  refine ⟨14065267565084184129893123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9376845043389456086595415 14065267565084184129893123)
                  ·
                    refine ⟨21097901347626276194839685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14065267565084184129893123 21097901347626276194839685)
                    ·
                      refine ⟨3955856502679926786532441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21097901347626276194839685 3955856502679926786532441)
                      ·
                        rfl

theorem cell23_7704003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_7704003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704003 prefixEnd_7704003 := by exact prefixLift 7704003
  have htrace : WordTrace (prefixWord ++ tailWord_7704003) baseStart_7704003 baseEnd_7704003 := by
    simpa [prefixWord, tailWord_7704003, baseEnd_7704003] using wordTrace_append hprefix tailTrace_7704003
  have hstable : (prefixWord ++ tailWord_7704003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704003).length < 2 ^ (prefixWord ++ tailWord_7704003).sum := by decide
  have hdescent : baseEnd_7704003 < baseStart_7704003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704026 : List Nat := [3, 1, 1, 2, 3, 2, 11]
def baseStart_7704026 : Nat := 118140960795 + 7704026 * 2 ^ 59
def prefixEnd_7704026 : Nat := 4983230072969 + 3 ^ 40 * 7704026 * 2
def baseEnd_7704026 : Nat := 48837880404135557982035

theorem tailTrace_7704026 : CollatzResearch.WordTrace tailWord_7704026 prefixEnd_7704026 48837880404135557982035 := by
  unfold tailWord_7704026
  simp only [CollatzResearch.WordTrace]
  refine ⟨70247228096909254933566983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187325941591758013156178621 70247228096909254933566983)
  ·
    refine ⟨105370842145363882400350475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70247228096909254933566983 105370842145363882400350475)
    ·
      refine ⟨158056263218045823600525713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105370842145363882400350475 158056263218045823600525713)
      ·
        refine ⟨118542197413534367700394285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158056263218045823600525713 118542197413534367700394285)
        ·
          refine ⟨44453324030075387887647857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118542197413534367700394285 44453324030075387887647857)
          ·
            refine ⟨33339993022556540915735893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44453324030075387887647857 33339993022556540915735893)
            ·
              refine ⟨48837880404135557982035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33339993022556540915735893 48837880404135557982035)
              ·
                rfl

theorem cell23_7704026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 11].length) (baseStart_7704026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704026 prefixEnd_7704026 := by exact prefixLift 7704026
  have htrace : WordTrace (prefixWord ++ tailWord_7704026) baseStart_7704026 baseEnd_7704026 := by
    simpa [prefixWord, tailWord_7704026, baseEnd_7704026] using wordTrace_append hprefix tailTrace_7704026
  have hstable : (prefixWord ++ tailWord_7704026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704026).length < 2 ^ (prefixWord ++ tailWord_7704026).sum := by decide
  have hdescent : baseEnd_7704026 < baseStart_7704026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704077 : List Nat := [1, 7, 1, 1, 3, 10]
def baseStart_7704077 : Nat := 118140960795 + 7704077 * 2 ^ 59
def prefixEnd_7704077 : Nat := 4983230072969 + 3 ^ 40 * 7704077 * 2
def baseEnd_7704077 : Nat := 16279401235589956777807

theorem tailTrace_7704077 : CollatzResearch.WordTrace tailWord_7704077 prefixEnd_7704077 16279401235589956777807 := by
  unfold tailWord_7704077
  simp only [CollatzResearch.WordTrace]
  refine ⟨280990772510452255444374485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187327181673634836962916323 280990772510452255444374485)
  ·
    refine ⟨6585721230713724736977527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 280990772510452255444374485 6585721230713724736977527)
    ·
      refine ⟨9878581846070587105466291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6585721230713724736977527 9878581846070587105466291)
      ·
        refine ⟨14817872769105880658199437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9878581846070587105466291 14817872769105880658199437)
        ·
          refine ⟨5556702288414705246824789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14817872769105880658199437 5556702288414705246824789)
          ·
            refine ⟨16279401235589956777807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5556702288414705246824789 16279401235589956777807)
            ·
              rfl

theorem cell23_7704077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 10].length) (baseStart_7704077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704077 prefixEnd_7704077 := by exact prefixLift 7704077
  have htrace : WordTrace (prefixWord ++ tailWord_7704077) baseStart_7704077 baseEnd_7704077 := by
    simpa [prefixWord, tailWord_7704077, baseEnd_7704077] using wordTrace_append hprefix tailTrace_7704077
  have hstable : (prefixWord ++ tailWord_7704077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704077).length < 2 ^ (prefixWord ++ tailWord_7704077).sum := by decide
  have hdescent : baseEnd_7704077 < baseStart_7704077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704088 : List Nat := [2, 1, 2, 3, 4, 2, 2, 2, 1, 2, 2]
def baseStart_7704088 : Nat := 118140960795 + 7704088 * 2 ^ 59
def prefixEnd_7704088 : Nat := 4983230072969 + 3 ^ 40 * 7704088 * 2
def baseEnd_7704088 : Nat := 3955900148535558953969551

theorem tailTrace_7704088 : CollatzResearch.WordTrace tailWord_7704088 prefixEnd_7704088 3955900148535558953969551 := by
  unfold tailWord_7704088
  simp only [CollatzResearch.WordTrace]
  refine ⟨140495586856706202161512459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187327449142274936215349945 140495586856706202161512459)
  ·
    refine ⟨210743380285059303242268689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140495586856706202161512459 210743380285059303242268689)
    ·
      refine ⟨158057535213794477431701517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210743380285059303242268689 158057535213794477431701517)
      ·
        refine ⟨59271575705172929036888069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158057535213794477431701517 59271575705172929036888069)
        ·
          refine ⟨11113420444719924194416513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59271575705172929036888069 11113420444719924194416513)
          ·
            refine ⟨8335065333539943145812385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11113420444719924194416513 8335065333539943145812385)
            ·
              refine ⟨6251299000154957359359289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8335065333539943145812385 6251299000154957359359289)
              ·
                refine ⟨4688474250116218019519467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251299000154957359359289 4688474250116218019519467)
                ·
                  refine ⟨7032711375174327029279201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688474250116218019519467 7032711375174327029279201)
                  ·
                    refine ⟨5274533531380745271959401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7032711375174327029279201 5274533531380745271959401)
                    ·
                      refine ⟨3955900148535558953969551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274533531380745271959401 3955900148535558953969551)
                      ·
                        rfl

theorem cell23_7704088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_7704088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704088 prefixEnd_7704088 := by exact prefixLift 7704088
  have htrace : WordTrace (prefixWord ++ tailWord_7704088) baseStart_7704088 baseEnd_7704088 := by
    simpa [prefixWord, tailWord_7704088, baseEnd_7704088] using wordTrace_append hprefix tailTrace_7704088
  have hstable : (prefixWord ++ tailWord_7704088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704088).length < 2 ^ (prefixWord ++ tailWord_7704088).sum := by decide
  have hdescent : baseEnd_7704088 < baseStart_7704088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704093 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_7704093 : Nat := 118140960795 + 7704093 * 2 ^ 59
def prefixEnd_7704093 : Nat := 4983230072969 + 3 ^ 40 * 7704093 * 2
def baseEnd_7704093 : Nat := 3955902715938831434407027

theorem tailTrace_7704093 : CollatzResearch.WordTrace tailWord_7704093 prefixEnd_7704093 3955902715938831434407027 := by
  unfold tailWord_7704093
  simp only [CollatzResearch.WordTrace]
  refine ⟨280991356078394290176956933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187327570718929526784637955 280991356078394290176956933)
  ·
    refine ⟨52685879264698929408179425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280991356078394290176956933 52685879264698929408179425)
    ·
      refine ⟨39514409448524197056134569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52685879264698929408179425 39514409448524197056134569)
      ·
        refine ⟨29635807086393147792100927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39514409448524197056134569 29635807086393147792100927)
        ·
          refine ⟨44453710629589721688151391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29635807086393147792100927 44453710629589721688151391)
          ·
            refine ⟨66680565944384582532227087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44453710629589721688151391 66680565944384582532227087)
            ·
              refine ⟨100020848916576873798340631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66680565944384582532227087 100020848916576873798340631)
              ·
                refine ⟨150031273374865310697510947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100020848916576873798340631 150031273374865310697510947)
                ·
                  refine ⟨225046910062297966046266421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150031273374865310697510947 225046910062297966046266421)
                  ·
                    refine ⟨21098147818340434316837477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225046910062297966046266421 21098147818340434316837477)
                    ·
                      refine ⟨3955902715938831434407027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21098147818340434316837477 3955902715938831434407027)
                      ·
                        rfl

theorem cell23_7704093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_7704093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704093 prefixEnd_7704093 := by exact prefixLift 7704093
  have htrace : WordTrace (prefixWord ++ tailWord_7704093) baseStart_7704093 baseEnd_7704093 := by
    simpa [prefixWord, tailWord_7704093, baseEnd_7704093] using wordTrace_append hprefix tailTrace_7704093
  have hstable : (prefixWord ++ tailWord_7704093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704093).length < 2 ^ (prefixWord ++ tailWord_7704093).sum := by decide
  have hdescent : baseEnd_7704093 < baseStart_7704093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704113 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_7704113 : Nat := 118140960795 + 7704113 * 2 ^ 59
def prefixEnd_7704113 : Nat := 4983230072969 + 3 ^ 40 * 7704113 * 2
def baseEnd_7704113 : Nat := 3955912985551921356156935

theorem tailTrace_7704113 : CollatzResearch.WordTrace tailWord_7704113 prefixEnd_7704113 3955912985551921356156935 := by
  unfold tailWord_7704113
  simp only [CollatzResearch.WordTrace]
  refine ⟨280992085538321833592684993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187328057025547889061789995 280992085538321833592684993)
  ·
    refine ⟨210744064153741375194513745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280992085538321833592684993 210744064153741375194513745)
    ·
      refine ⟨158058048115306031395885309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210744064153741375194513745 158058048115306031395885309)
      ·
        refine ⟨59271768043239761773456991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158058048115306031395885309 59271768043239761773456991)
        ·
          refine ⟨88907652064859642660185487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59271768043239761773456991 88907652064859642660185487)
          ·
            refine ⟨133361478097289463990278231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88907652064859642660185487 133361478097289463990278231)
            ·
              refine ⟨200042217145934195985417347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133361478097289463990278231 200042217145934195985417347)
              ·
                refine ⟨300063325718901293978126021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200042217145934195985417347 300063325718901293978126021)
                ·
                  refine ⟨56261873572293992620898629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300063325718901293978126021 56261873572293992620898629)
                  ·
                    refine ⟨10549101294805123616418493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56261873572293992620898629 10549101294805123616418493)
                    ·
                      refine ⟨3955912985551921356156935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10549101294805123616418493 3955912985551921356156935)
                      ·
                        rfl

theorem cell23_7704113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_7704113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704113 prefixEnd_7704113 := by exact prefixLift 7704113
  have htrace : WordTrace (prefixWord ++ tailWord_7704113) baseStart_7704113 baseEnd_7704113 := by
    simpa [prefixWord, tailWord_7704113, baseEnd_7704113] using wordTrace_append hprefix tailTrace_7704113
  have hstable : (prefixWord ++ tailWord_7704113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704113).length < 2 ^ (prefixWord ++ tailWord_7704113).sum := by decide
  have hdescent : baseEnd_7704113 < baseStart_7704113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704163 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 1, 7]
def baseStart_7704163 : Nat := 118140960795 + 7704163 * 2 ^ 59
def prefixEnd_7704163 : Nat := 4983230072969 + 3 ^ 40 * 7704163 * 2
def baseEnd_7704163 : Nat := 1318646219861548720177235

theorem tailTrace_7704163 : CollatzResearch.WordTrace tailWord_7704163 prefixEnd_7704163 1318646219861548720177235 := by
  unfold tailWord_7704163
  simp only [CollatzResearch.WordTrace]
  refine ⟨280993909188140692132005143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187329272792093794754670095 280993909188140692132005143)
  ·
    refine ⟨421490863782211038198007715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280993909188140692132005143 421490863782211038198007715)
    ·
      refine ⟨632236295673316557297011573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421490863782211038198007715 632236295673316557297011573)
      ·
        refine ⟨59272152719373427246594835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 632236295673316557297011573 59272152719373427246594835)
        ·
          refine ⟨88908229079060140869892253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59272152719373427246594835 88908229079060140869892253)
          ·
            refine ⟨33340585904647552826209595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88908229079060140869892253 33340585904647552826209595)
            ·
              refine ⟨50010878856971329239314393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33340585904647552826209595 50010878856971329239314393)
              ·
                refine ⟨37508159142728496929485795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50010878856971329239314393 37508159142728496929485795)
                ·
                  refine ⟨56262238714092745394228693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37508159142728496929485795 56262238714092745394228693)
                  ·
                    refine ⟨1318646219861548720177235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56262238714092745394228693 1318646219861548720177235)
                    ·
                      rfl

theorem cell23_7704163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 7].length) (baseStart_7704163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704163 prefixEnd_7704163 := by exact prefixLift 7704163
  have htrace : WordTrace (prefixWord ++ tailWord_7704163) baseStart_7704163 baseEnd_7704163 := by
    simpa [prefixWord, tailWord_7704163, baseEnd_7704163] using wordTrace_append hprefix tailTrace_7704163
  have hstable : (prefixWord ++ tailWord_7704163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704163).length < 2 ^ (prefixWord ++ tailWord_7704163).sum := by decide
  have hdescent : baseEnd_7704163 < baseStart_7704163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704213 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_7704213 : Nat := 118140960795 + 7704213 * 2 ^ 59
def prefixEnd_7704213 : Nat := 4983230072969 + 3 ^ 40 * 7704213 * 2
def baseEnd_7704213 : Nat := 3955964333617370964906475

theorem tailTrace_7704213 : CollatzResearch.WordTrace tailWord_7704213 prefixEnd_7704213 3955964333617370964906475 := by
  unfold tailWord_7704213
  simp only [CollatzResearch.WordTrace]
  refine ⟨280995732837959550671325293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187330488558639700447550195 280995732837959550671325293)
  ·
    refine ⟨105373399814234831501746985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280995732837959550671325293 105373399814234831501746985)
    ·
      refine ⟨79030049860676123626310239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105373399814234831501746985 79030049860676123626310239)
      ·
        refine ⟨118545074791014185439465359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79030049860676123626310239 118545074791014185439465359)
        ·
          refine ⟨177817612186521278159198039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118545074791014185439465359 177817612186521278159198039)
          ·
            refine ⟨266726418279781917238797059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177817612186521278159198039 266726418279781917238797059)
            ·
              refine ⟨400089627419672875858195589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266726418279781917238797059 400089627419672875858195589)
              ·
                refine ⟨75016805141188664223411673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400089627419672875858195589 75016805141188664223411673)
                ·
                  refine ⟨56262603855891498167558755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75016805141188664223411673 56262603855891498167558755)
                  ·
                    refine ⟨84393905783837247251338133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56262603855891498167558755 84393905783837247251338133)
                    ·
                      refine ⟨3955964333617370964906475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84393905783837247251338133 3955964333617370964906475)
                      ·
                        rfl

theorem cell23_7704213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_7704213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704213 prefixEnd_7704213 := by exact prefixLift 7704213
  have htrace : WordTrace (prefixWord ++ tailWord_7704213) baseStart_7704213 baseEnd_7704213 := by
    simpa [prefixWord, tailWord_7704213, baseEnd_7704213] using wordTrace_append hprefix tailTrace_7704213
  have hstable : (prefixWord ++ tailWord_7704213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704213).length < 2 ^ (prefixWord ++ tailWord_7704213).sum := by decide
  have hdescent : baseEnd_7704213 < baseStart_7704213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704260 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_7704260 : Nat := 118140960795 + 7704260 * 2 ^ 59
def prefixEnd_7704260 : Nat := 4983230072969 + 3 ^ 40 * 7704260 * 2
def baseEnd_7704260 : Nat := 3955988467208132281018759

theorem tailTrace_7704260 : CollatzResearch.WordTrace tailWord_7704260 prefixEnd_7704260 3955988467208132281018759 := by
  unfold tailWord_7704260
  simp only [CollatzResearch.WordTrace]
  refine ⟨140498723534394638849143117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187331631379192851798857489 140498723534394638849143117)
  ·
    refine ⟨52687021325397989568428669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140498723534394638849143117 52687021325397989568428669)
    ·
      refine ⟨19757632997024246088160751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52687021325397989568428669 19757632997024246088160751)
      ·
        refine ⟨29636449495536369132241127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19757632997024246088160751 29636449495536369132241127)
        ·
          refine ⟨44454674243304553698361691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29636449495536369132241127 44454674243304553698361691)
          ·
            refine ⟨66682011364956830547542537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44454674243304553698361691 66682011364956830547542537)
            ·
              refine ⟨50011508523717622910656903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66682011364956830547542537 50011508523717622910656903)
              ·
                refine ⟨75017262785576434365985355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50011508523717622910656903 75017262785576434365985355)
                ·
                  refine ⟨112525894178364651548978033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75017262785576434365985355 112525894178364651548978033)
                  ·
                    refine ⟨84394420633773488661733525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112525894178364651548978033 84394420633773488661733525)
                    ·
                      refine ⟨3955988467208132281018759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84394420633773488661733525 3955988467208132281018759)
                      ·
                        rfl

theorem cell23_7704260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_7704260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704260 prefixEnd_7704260 := by exact prefixLift 7704260
  have htrace : WordTrace (prefixWord ++ tailWord_7704260) baseStart_7704260 baseEnd_7704260 := by
    simpa [prefixWord, tailWord_7704260, baseEnd_7704260] using wordTrace_append hprefix tailTrace_7704260
  have hstable : (prefixWord ++ tailWord_7704260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704260).length < 2 ^ (prefixWord ++ tailWord_7704260).sum := by decide
  have hdescent : baseEnd_7704260 < baseStart_7704260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704270 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_7704270 : Nat := 118140960795 + 7704270 * 2 ^ 59
def prefixEnd_7704270 : Nat := 4983230072969 + 3 ^ 40 * 7704270 * 2
def baseEnd_7704270 : Nat := 1318664534004892413964571

theorem tailTrace_7704270 : CollatzResearch.WordTrace tailWord_7704270 prefixEnd_7704270 1318664534004892413964571 := by
  unfold tailWord_7704270
  simp only [CollatzResearch.WordTrace]
  refine ⟨35124726474844131175768783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187331874532502032937433509 35124726474844131175768783)
  ·
    refine ⟨52687089712266196763653175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35124726474844131175768783 52687089712266196763653175)
    ·
      refine ⟨79030634568399295145479763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52687089712266196763653175 79030634568399295145479763)
      ·
        refine ⟨118545951852598942718219645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79030634568399295145479763 118545951852598942718219645)
        ·
          refine ⟨44454731944724603519332367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118545951852598942718219645 44454731944724603519332367)
          ·
            refine ⟨66682097917086905278998551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44454731944724603519332367 66682097917086905278998551)
            ·
              refine ⟨100023146875630357918497827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66682097917086905278998551 100023146875630357918497827)
              ·
                refine ⟨150034720313445536877746741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100023146875630357918497827 150034720313445536877746741)
                ·
                  refine ⟨14065755029385519082288757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150034720313445536877746741 14065755029385519082288757)
                  ·
                    refine ⟨1318664534004892413964571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14065755029385519082288757 1318664534004892413964571)
                    ·
                      rfl

theorem cell23_7704270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_7704270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704270 prefixEnd_7704270 := by exact prefixLift 7704270
  have htrace : WordTrace (prefixWord ++ tailWord_7704270) baseStart_7704270 baseEnd_7704270 := by
    simpa [prefixWord, tailWord_7704270, baseEnd_7704270] using wordTrace_append hprefix tailTrace_7704270
  have hstable : (prefixWord ++ tailWord_7704270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704270).length < 2 ^ (prefixWord ++ tailWord_7704270).sum := by decide
  have hdescent : baseEnd_7704270 < baseStart_7704270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704300 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_7704300 : Nat := 118140960795 + 7704300 * 2 ^ 59
def prefixEnd_7704300 : Nat := 4983230072969 + 3 ^ 40 * 7704300 * 2
def baseEnd_7704300 : Nat := 1318669668811437374839525

theorem tailTrace_7704300 : CollatzResearch.WordTrace tailWord_7704300 prefixEnd_7704300 1318669668811437374839525 := by
  unfold tailWord_7704300
  simp only [CollatzResearch.WordTrace]
  refine ⟨140499452994322182264871177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187332603992429576353161569 140499452994322182264871177)
  ·
    refine ⟨105374589745741636698653383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140499452994322182264871177 105374589745741636698653383)
    ·
      refine ⟨158061884618612455047980075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105374589745741636698653383 158061884618612455047980075)
      ·
        refine ⟨237092826927918682571970113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158061884618612455047980075 237092826927918682571970113)
        ·
          refine ⟨177819620195939011928977585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237092826927918682571970113 177819620195939011928977585)
          ·
            refine ⟨133364715146954258946733189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177819620195939011928977585 133364715146954258946733189)
            ·
              refine ⟨25005884090053923552512473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133364715146954258946733189 25005884090053923552512473)
              ·
                refine ⟨18754413067540442664384355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25005884090053923552512473 18754413067540442664384355)
                ·
                  refine ⟨28131619601310663996576533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18754413067540442664384355 28131619601310663996576533)
                  ·
                    refine ⟨1318669668811437374839525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28131619601310663996576533 1318669668811437374839525)
                    ·
                      rfl

theorem cell23_7704300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_7704300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704300 prefixEnd_7704300 := by exact prefixLift 7704300
  have htrace : WordTrace (prefixWord ++ tailWord_7704300) baseStart_7704300 baseEnd_7704300 := by
    simpa [prefixWord, tailWord_7704300, baseEnd_7704300] using wordTrace_append hprefix tailTrace_7704300
  have hstable : (prefixWord ++ tailWord_7704300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704300).length < 2 ^ (prefixWord ++ tailWord_7704300).sum := by decide
  have hdescent : baseEnd_7704300 < baseStart_7704300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704301 : List Nat := [1, 5, 1, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_7704301 : Nat := 118140960795 + 7704301 * 2 ^ 59
def prefixEnd_7704301 : Nat := 4983230072969 + 3 ^ 40 * 7704301 * 2
def baseEnd_7704301 : Nat := 3956009519914966620606071

theorem tailTrace_7704301 : CollatzResearch.WordTrace tailWord_7704301 prefixEnd_7704301 3956009519914966620606071 := by
  unfold tailWord_7704301
  simp only [CollatzResearch.WordTrace]
  refine ⟨280998942461640741700528757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187332628307760494467019171 280998942461640741700528757)
  ·
    refine ⟨26343650855778819534424571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280998942461640741700528757 26343650855778819534424571)
    ·
      refine ⟨39515476283668229301636857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26343650855778819534424571 39515476283668229301636857)
      ·
        refine ⟨29636607212751171976227643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39515476283668229301636857 29636607212751171976227643)
        ·
          refine ⟨44454910819126757964341465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29636607212751171976227643 44454910819126757964341465)
          ·
            refine ⟨33341183114345068473256099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44454910819126757964341465 33341183114345068473256099)
            ·
              refine ⟨50011774671517602709884149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33341183114345068473256099 50011774671517602709884149)
              ·
                refine ⟨4688603875454775254051639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50011774671517602709884149 4688603875454775254051639)
                ·
                  refine ⟨7032905813182162881077459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688603875454775254051639 7032905813182162881077459)
                  ·
                    refine ⟨10549358719773244321616189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7032905813182162881077459 10549358719773244321616189)
                    ·
                      refine ⟨3956009519914966620606071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10549358719773244321616189 3956009519914966620606071)
                      ·
                        rfl

theorem cell23_7704301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_7704301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704301 prefixEnd_7704301 := by exact prefixLift 7704301
  have htrace : WordTrace (prefixWord ++ tailWord_7704301) baseStart_7704301 baseEnd_7704301 := by
    simpa [prefixWord, tailWord_7704301, baseEnd_7704301] using wordTrace_append hprefix tailTrace_7704301
  have hstable : (prefixWord ++ tailWord_7704301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704301).length < 2 ^ (prefixWord ++ tailWord_7704301).sum := by decide
  have hdescent : baseEnd_7704301 < baseStart_7704301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704317 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_7704317 : Nat := 118140960795 + 7704317 * 2 ^ 59
def prefixEnd_7704317 : Nat := 4983230072969 + 3 ^ 40 * 7704317 * 2
def baseEnd_7704317 : Nat := 1318672578535146186001999

theorem tailTrace_7704317 : CollatzResearch.WordTrace tailWord_7704317 prefixEnd_7704317 1318672578535146186001999 := by
  unfold tailWord_7704317
  simp only [CollatzResearch.WordTrace]
  refine ⟨280999526029582776433111205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187333017353055184288740803 280999526029582776433111205)
  ·
    refine ⟨52687411130546770581208351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280999526029582776433111205 52687411130546770581208351)
    ·
      refine ⟨79031116695820155871812527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52687411130546770581208351 79031116695820155871812527)
      ·
        refine ⟨118546675043730233807718791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79031116695820155871812527 118546675043730233807718791)
        ·
          refine ⟨177820012565595350711578187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118546675043730233807718791 177820012565595350711578187)
          ·
            refine ⟨266730018848393026067367281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177820012565595350711578187 266730018848393026067367281)
            ·
              refine ⟨200047514136294769550525461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266730018848393026067367281 200047514136294769550525461)
              ·
                refine ⟨9377227225138817322680881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200047514136294769550525461 9377227225138817322680881)
                ·
                  refine ⟨7032920418854112992010661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9377227225138817322680881 7032920418854112992010661)
                  ·
                    refine ⟨1318672578535146186001999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7032920418854112992010661 1318672578535146186001999)
                    ·
                      rfl

theorem cell23_7704317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_7704317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704317 prefixEnd_7704317 := by exact prefixLift 7704317
  have htrace : WordTrace (prefixWord ++ tailWord_7704317) baseStart_7704317 baseEnd_7704317 := by
    simpa [prefixWord, tailWord_7704317, baseEnd_7704317] using wordTrace_append hprefix tailTrace_7704317
  have hstable : (prefixWord ++ tailWord_7704317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704317).length < 2 ^ (prefixWord ++ tailWord_7704317).sum := by decide
  have hdescent : baseEnd_7704317 < baseStart_7704317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704391 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_7704391 : Nat := 118140960795 + 7704391 * 2 ^ 59
def prefixEnd_7704391 : Nat := 4983230072969 + 3 ^ 40 * 7704391 * 2
def baseEnd_7704391 : Nat := 3956055733173871268480657

theorem tailTrace_7704391 : CollatzResearch.WordTrace tailWord_7704391 prefixEnd_7704391 3956055733173871268480657 := by
  unfold tailWord_7704391
  simp only [CollatzResearch.WordTrace]
  refine ⟨281002225031314687071305027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187334816687543124714203351 281002225031314687071305027)
  ·
    refine ⟨421503337546972030606957541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281002225031314687071305027 421503337546972030606957541)
    ·
      refine ⟨79031875790057255738804539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421503337546972030606957541 79031875790057255738804539)
      ·
        refine ⟨118547813685085883608206809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79031875790057255738804539 118547813685085883608206809)
        ·
          refine ⟨88910860263814412706155107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118547813685085883608206809 88910860263814412706155107)
          ·
            refine ⟨133366290395721619059232661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88910860263814412706155107 133366290395721619059232661)
            ·
              refine ⟨6251544862299450893401531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133366290395721619059232661 6251544862299450893401531)
              ·
                refine ⟨9377317293449176340102297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6251544862299450893401531 9377317293449176340102297)
                ·
                  refine ⟨7032987970086882255076723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9377317293449176340102297 7032987970086882255076723)
                  ·
                    refine ⟨10549481955130323382615085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7032987970086882255076723 10549481955130323382615085)
                    ·
                      refine ⟨3956055733173871268480657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10549481955130323382615085 3956055733173871268480657)
                      ·
                        rfl

theorem cell23_7704391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_7704391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704391 prefixEnd_7704391 := by exact prefixLift 7704391
  have htrace : WordTrace (prefixWord ++ tailWord_7704391) baseStart_7704391 baseEnd_7704391 := by
    simpa [prefixWord, tailWord_7704391, baseEnd_7704391] using wordTrace_append hprefix tailTrace_7704391
  have hstable : (prefixWord ++ tailWord_7704391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704391).length < 2 ^ (prefixWord ++ tailWord_7704391).sum := by decide
  have hdescent : baseEnd_7704391 < baseStart_7704391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704401 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 1, 3, 2]
def baseStart_7704401 : Nat := 118140960795 + 7704401 * 2 ^ 59
def prefixEnd_7704401 : Nat := 4983230072969 + 3 ^ 40 * 7704401 * 2
def baseEnd_7704401 : Nat := 3956060867980416229355611

theorem tailTrace_7704401 : CollatzResearch.WordTrace tailWord_7704401 prefixEnd_7704401 3956060867980416229355611 := by
  unfold tailWord_7704401
  simp only [CollatzResearch.WordTrace]
  refine ⟨281002589761278458779169057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187335059840852305852779371 281002589761278458779169057)
  ·
    refine ⟨210751942320958844084376793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281002589761278458779169057 210751942320958844084376793)
    ·
      refine ⟨158063956740719133063282595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210751942320958844084376793 158063956740719133063282595)
      ·
        refine ⟨237095935111078699594923893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158063956740719133063282595 237095935111078699594923893)
        ·
          refine ⟨22227743916663628087024115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237095935111078699594923893 22227743916663628087024115)
          ·
            refine ⟨33341615874995442130536173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22227743916663628087024115 33341615874995442130536173)
            ·
              refine ⟨12503105953123290798951065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33341615874995442130536173 12503105953123290798951065)
              ·
                refine ⟨9377329464842468099213299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12503105953123290798951065 9377329464842468099213299)
                ·
                  refine ⟨14065994197263702148819949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9377329464842468099213299 14065994197263702148819949)
                  ·
                    refine ⟨5274747823973888305807481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14065994197263702148819949 5274747823973888305807481)
                    ·
                      refine ⟨3956060867980416229355611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274747823973888305807481 3956060867980416229355611)
                      ·
                        rfl

theorem cell23_7704401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_7704401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704401 prefixEnd_7704401 := by exact prefixLift 7704401
  have htrace : WordTrace (prefixWord ++ tailWord_7704401) baseStart_7704401 baseEnd_7704401 := by
    simpa [prefixWord, tailWord_7704401, baseEnd_7704401] using wordTrace_append hprefix tailTrace_7704401
  have hstable : (prefixWord ++ tailWord_7704401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704401).length < 2 ^ (prefixWord ++ tailWord_7704401).sum := by decide
  have hdescent : baseEnd_7704401 < baseStart_7704401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704437 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 7]
def baseStart_7704437 : Nat := 118140960795 + 7704437 * 2 ^ 59
def prefixEnd_7704437 : Nat := 4983230072969 + 3 ^ 40 * 7704437 * 2
def baseEnd_7704437 : Nat := 439564372587108676500605

theorem tailTrace_7704437 : CollatzResearch.WordTrace tailWord_7704437 prefixEnd_7704437 439564372587108676500605 := by
  unfold tailWord_7704437
  simp only [CollatzResearch.WordTrace]
  refine ⟨281003902789148036927479565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187335935192765357951653043 281003902789148036927479565)
  ·
    refine ⟨105376463545930513847804837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281003902789148036927479565 105376463545930513847804837)
    ·
      refine ⟨19758086914861971346463407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105376463545930513847804837 19758086914861971346463407)
      ·
        refine ⟨29637130372292957019695111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19758086914861971346463407 29637130372292957019695111)
        ·
          refine ⟨44455695558439435529542667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29637130372292957019695111 44455695558439435529542667)
          ·
            refine ⟨66683543337659153294314001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44455695558439435529542667 66683543337659153294314001)
            ·
              refine ⟨50012657503244364970735501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66683543337659153294314001 50012657503244364970735501)
              ·
                refine ⟨18754746563716636864025813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50012657503244364970735501 18754746563716636864025813)
                ·
                  refine ⟨439564372587108676500605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18754746563716636864025813 439564372587108676500605)
                  ·
                    rfl

theorem cell23_7704437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_7704437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704437 prefixEnd_7704437 := by exact prefixLift 7704437
  have htrace : WordTrace (prefixWord ++ tailWord_7704437) baseStart_7704437 baseEnd_7704437 := by
    simpa [prefixWord, tailWord_7704437, baseEnd_7704437] using wordTrace_append hprefix tailTrace_7704437
  have hstable : (prefixWord ++ tailWord_7704437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704437).length < 2 ^ (prefixWord ++ tailWord_7704437).sum := by decide
  have hdescent : baseEnd_7704437 < baseStart_7704437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704482 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_7704482 : Nat := 118140960795 + 7704482 * 2 ^ 59
def prefixEnd_7704482 : Nat := 4983230072969 + 3 ^ 40 * 7704482 * 2
def baseEnd_7704482 : Nat := 3956102459913430412442739

theorem tailTrace_7704482 : CollatzResearch.WordTrace tailWord_7704482 prefixEnd_7704482 3956102459913430412442739 := by
  unfold tailWord_7704482
  simp only [CollatzResearch.WordTrace]
  refine ⟨70251386018496252403216925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187337029382656673075245133 70251386018496252403216925)
  ·
    refine ⟨26344269756936094651206347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70251386018496252403216925 26344269756936094651206347)
    ·
      refine ⟨39516404635404141976809521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26344269756936094651206347 39516404635404141976809521)
      ·
        refine ⟨29637303476553106482607141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39516404635404141976809521 29637303476553106482607141)
        ·
          refine ⟨5556994401853707465488839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29637303476553106482607141 5556994401853707465488839)
          ·
            refine ⟨8335491602780561198233259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556994401853707465488839 8335491602780561198233259)
            ·
              refine ⟨12503237404170841797349889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335491602780561198233259 12503237404170841797349889)
              ·
                refine ⟨9377428053128131348012417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12503237404170841797349889 9377428053128131348012417)
                ·
                  refine ⟨7033071039846098511009313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9377428053128131348012417 7033071039846098511009313)
                  ·
                    refine ⟨5274803279884573883256985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7033071039846098511009313 5274803279884573883256985)
                    ·
                      refine ⟨3956102459913430412442739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274803279884573883256985 3956102459913430412442739)
                      ·
                        rfl

theorem cell23_7704482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_7704482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704482 prefixEnd_7704482 := by exact prefixLift 7704482
  have htrace : WordTrace (prefixWord ++ tailWord_7704482) baseStart_7704482 baseEnd_7704482 := by
    simpa [prefixWord, tailWord_7704482, baseEnd_7704482] using wordTrace_append hprefix tailTrace_7704482
  have hstable : (prefixWord ++ tailWord_7704482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704482).length < 2 ^ (prefixWord ++ tailWord_7704482).sum := by decide
  have hdescent : baseEnd_7704482 < baseStart_7704482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704504 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 2, 4, 2]
def baseStart_7704504 : Nat := 118140960795 + 7704504 * 2 ^ 59
def prefixEnd_7704504 : Nat := 4983230072969 + 3 ^ 40 * 7704504 * 2
def baseEnd_7704504 : Nat := 3956113756487829326367637

theorem tailTrace_7704504 : CollatzResearch.WordTrace tailWord_7704504 prefixEnd_7704504 3956113756487829326367637 := by
  unfold tailWord_7704504
  simp only [CollatzResearch.WordTrace]
  refine ⟨140503173239952653685084283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187337564319936871580112377 140503173239952653685084283)
  ·
    refine ⟨210754759859928980527626425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140503173239952653685084283 210754759859928980527626425)
    ·
      refine ⟨158066069894946735395719819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210754759859928980527626425 158066069894946735395719819)
      ·
        refine ⟨237099104842420103093579729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158066069894946735395719819 237099104842420103093579729)
        ·
          refine ⟨177824328631815077320184797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237099104842420103093579729 177824328631815077320184797)
          ·
            refine ⟨66684123236930653995069299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177824328631815077320184797 66684123236930653995069299)
            ·
              refine ⟨100026184855395980992603949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66684123236930653995069299 100026184855395980992603949)
              ·
                refine ⟨37509819320773492872226481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100026184855395980992603949 37509819320773492872226481)
                ·
                  refine ⟨28132364490580119654169861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37509819320773492872226481 28132364490580119654169861)
                  ·
                    refine ⟨5274818341983772435156849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28132364490580119654169861 5274818341983772435156849)
                    ·
                      refine ⟨3956113756487829326367637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274818341983772435156849 3956113756487829326367637)
                      ·
                        rfl

theorem cell23_7704504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_7704504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704504 prefixEnd_7704504 := by exact prefixLift 7704504
  have htrace : WordTrace (prefixWord ++ tailWord_7704504) baseStart_7704504 baseEnd_7704504 := by
    simpa [prefixWord, tailWord_7704504, baseEnd_7704504] using wordTrace_append hprefix tailTrace_7704504
  have hstable : (prefixWord ++ tailWord_7704504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704504).length < 2 ^ (prefixWord ++ tailWord_7704504).sum := by decide
  have hdescent : baseEnd_7704504 < baseStart_7704504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704507 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 3]
def baseStart_7704507 : Nat := 118140960795 + 7704507 * 2 ^ 59
def prefixEnd_7704507 : Nat := 4983230072969 + 3 ^ 40 * 7704507 * 2
def baseEnd_7704507 : Nat := 3956115296929792814630123

theorem tailTrace_7704507 : CollatzResearch.WordTrace tailWord_7704507 prefixEnd_7704507 3956115296929792814630123 := by
  unfold tailWord_7704507
  simp only [CollatzResearch.WordTrace]
  refine ⟨281006455898894438882527775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187337637265929625921685183 281006455898894438882527775)
  ·
    refine ⟨421509683848341658323791663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281006455898894438882527775 421509683848341658323791663)
    ·
      refine ⟨632264525772512487485687495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421509683848341658323791663 632264525772512487485687495)
      ·
        refine ⟨948396788658768731228531243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632264525772512487485687495 948396788658768731228531243)
        ·
          refine ⟨1422595182988153096842796865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948396788658768731228531243 1422595182988153096842796865)
          ·
            refine ⟨1066946387241114822632097649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422595182988153096842796865 1066946387241114822632097649)
            ·
              refine ⟨800209790430836116974073237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066946387241114822632097649 800209790430836116974073237)
              ·
                refine ⟨37509833926445442983159683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 800209790430836116974073237 37509833926445442983159683)
                ·
                  refine ⟨56264750889668164474739525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37509833926445442983159683 56264750889668164474739525)
                  ·
                    refine ⟨10549640791812780839013661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56264750889668164474739525 10549640791812780839013661)
                    ·
                      refine ⟨3956115296929792814630123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10549640791812780839013661 3956115296929792814630123)
                      ·
                        rfl

theorem cell23_7704507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 3].length) (baseStart_7704507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704507 prefixEnd_7704507 := by exact prefixLift 7704507
  have htrace : WordTrace (prefixWord ++ tailWord_7704507) baseStart_7704507 baseEnd_7704507 := by
    simpa [prefixWord, tailWord_7704507, baseEnd_7704507] using wordTrace_append hprefix tailTrace_7704507
  have hstable : (prefixWord ++ tailWord_7704507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704507).length < 2 ^ (prefixWord ++ tailWord_7704507).sum := by decide
  have hdescent : baseEnd_7704507 < baseStart_7704507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704524 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_7704524 : Nat := 118140960795 + 7704524 * 2 ^ 59
def prefixEnd_7704524 : Nat := 4983230072969 + 3 ^ 40 * 7704524 * 2
def baseEnd_7704524 : Nat := 3956124026100919248117545

theorem tailTrace_7704524 : CollatzResearch.WordTrace tailWord_7704524 prefixEnd_7704524 3956124026100919248117545 := by
  unfold tailWord_7704524
  simp only [CollatzResearch.WordTrace]
  refine ⟨140503537969916425392948313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187338050626555233857264417 140503537969916425392948313)
  ·
    refine ⟨105377653477437319044711235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140503537969916425392948313 105377653477437319044711235)
    ·
      refine ⟨158066480216155978567066853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105377653477437319044711235 158066480216155978567066853)
      ·
        refine ⟨29637465040529245981325035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158066480216155978567066853 29637465040529245981325035)
        ·
          refine ⟨44456197560793868971987553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29637465040529245981325035 44456197560793868971987553)
          ·
            refine ⟨33342148170595401728990665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44456197560793868971987553 33342148170595401728990665)
            ·
              refine ⟨25006611127946551296742999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33342148170595401728990665 25006611127946551296742999)
              ·
                refine ⟨37509916691919826945114499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25006611127946551296742999 37509916691919826945114499)
                ·
                  refine ⟨56264875037879740417671749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37509916691919826945114499 56264875037879740417671749)
                  ·
                    refine ⟨10549664069602451328313453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56264875037879740417671749 10549664069602451328313453)
                    ·
                      refine ⟨3956124026100919248117545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10549664069602451328313453 3956124026100919248117545)
                      ·
                        rfl

theorem cell23_7704524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_7704524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704524 prefixEnd_7704524 := by exact prefixLift 7704524
  have htrace : WordTrace (prefixWord ++ tailWord_7704524) baseStart_7704524 baseEnd_7704524 := by
    simpa [prefixWord, tailWord_7704524, baseEnd_7704524] using wordTrace_append hprefix tailTrace_7704524
  have hstable : (prefixWord ++ tailWord_7704524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704524).length < 2 ^ (prefixWord ++ tailWord_7704524).sum := by decide
  have hdescent : baseEnd_7704524 < baseStart_7704524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704548 : List Nat := [2, 3, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_7704548 : Nat := 118140960795 + 7704548 * 2 ^ 59
def prefixEnd_7704548 : Nat := 4983230072969 + 3 ^ 40 * 7704548 * 2
def baseEnd_7704548 : Nat := 1318712116545542384739145

theorem tailTrace_7704548 : CollatzResearch.WordTrace tailWord_7704548 prefixEnd_7704548 1318712116545542384739145 := by
  unfold tailWord_7704548
  simp only [CollatzResearch.WordTrace]
  refine ⟨140503975645872951442385149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187338634194497268589846865 140503975645872951442385149)
  ·
    refine ⟨52688990867202356790894431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140503975645872951442385149 52688990867202356790894431)
    ·
      refine ⟨79033486300803535186341647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52688990867202356790894431 79033486300803535186341647)
      ·
        refine ⟨118550229451205302779512471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79033486300803535186341647 118550229451205302779512471)
        ·
          refine ⟨177825344176807954169268707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118550229451205302779512471 177825344176807954169268707)
          ·
            refine ⟨266738016265211931253903061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177825344176807954169268707 266738016265211931253903061)
            ·
              refine ⟨6251672256215904638763353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 266738016265211931253903061 6251672256215904638763353)
              ·
                refine ⟨4688754192161928479072515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6251672256215904638763353 4688754192161928479072515)
                ·
                  refine ⟨7033131288242892718608773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688754192161928479072515 7033131288242892718608773)
                  ·
                    refine ⟨1318712116545542384739145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7033131288242892718608773 1318712116545542384739145)
                    ·
                      rfl

theorem cell23_7704548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_7704548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704548 prefixEnd_7704548 := by exact prefixLift 7704548
  have htrace : WordTrace (prefixWord ++ tailWord_7704548) baseStart_7704548 baseEnd_7704548 := by
    simpa [prefixWord, tailWord_7704548, baseEnd_7704548] using wordTrace_append hprefix tailTrace_7704548
  have hstable : (prefixWord ++ tailWord_7704548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704548).length < 2 ^ (prefixWord ++ tailWord_7704548).sum := by decide
  have hdescent : baseEnd_7704548 < baseStart_7704548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704581 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 2, 3, 2]
def baseStart_7704581 : Nat := 118140960795 + 7704581 * 2 ^ 59
def prefixEnd_7704581 : Nat := 4983230072969 + 3 ^ 40 * 7704581 * 2
def baseEnd_7704581 : Nat := 3956153294498225525104783

theorem tailTrace_7704581 : CollatzResearch.WordTrace tailWord_7704581 prefixEnd_7704581 3956153294498225525104783 := by
  unfold tailWord_7704581
  simp only [CollatzResearch.WordTrace]
  refine ⟨281009154900626349520721597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187339436600417566347147731 281009154900626349520721597)
  ·
    refine ⟨105378433087734881070270599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281009154900626349520721597 105378433087734881070270599)
    ·
      refine ⟨158067649631602321605405899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105378433087734881070270599 158067649631602321605405899)
      ·
        refine ⟨237101474447403482408108849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158067649631602321605405899 237101474447403482408108849)
        ·
          refine ⟨177826105835552611806081637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237101474447403482408108849 177826105835552611806081637)
          ·
            refine ⟨33342394844166114713640307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177826105835552611806081637 33342394844166114713640307)
            ·
              refine ⟨50013592266249172070460461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33342394844166114713640307 50013592266249172070460461)
              ·
                refine ⟨18755097099843439526422673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50013592266249172070460461 18755097099843439526422673)
                ·
                  refine ⟨14066322824882579644817005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18755097099843439526422673 14066322824882579644817005)
                  ·
                    refine ⟨5274871059330967366806377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14066322824882579644817005 5274871059330967366806377)
                    ·
                      refine ⟨3956153294498225525104783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274871059330967366806377 3956153294498225525104783)
                      ·
                        rfl

theorem cell23_7704581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_7704581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704581 prefixEnd_7704581 := by exact prefixLift 7704581
  have htrace : WordTrace (prefixWord ++ tailWord_7704581) baseStart_7704581 baseEnd_7704581 := by
    simpa [prefixWord, tailWord_7704581, baseEnd_7704581] using wordTrace_append hprefix tailTrace_7704581
  have hstable : (prefixWord ++ tailWord_7704581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704581).length < 2 ^ (prefixWord ++ tailWord_7704581).sum := by decide
  have hdescent : baseEnd_7704581 < baseStart_7704581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704588 : List Nat := [2, 2, 1, 2, 3, 1, 2, 5, 1, 1, 3]
def baseStart_7704588 : Nat := 118140960795 + 7704588 * 2 ^ 59
def prefixEnd_7704588 : Nat := 4983230072969 + 3 ^ 40 * 7704588 * 2
def baseEnd_7704588 : Nat := 3956156888862806997717251

theorem tailTrace_7704588 : CollatzResearch.WordTrace tailWord_7704588 prefixEnd_7704588 3956156888862806997717251 := by
  unfold tailWord_7704588
  simp only [CollatzResearch.WordTrace]
  refine ⟨140504705105800494858113209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187339606807733993144150945 140504705105800494858113209)
  ·
    refine ⟨105378528829350371143584907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140504705105800494858113209 105378528829350371143584907)
    ·
      refine ⟨158067793244025556715377361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105378528829350371143584907 158067793244025556715377361)
      ·
        refine ⟨118550844933019167536533021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158067793244025556715377361 118550844933019167536533021)
        ·
          refine ⟨44456566849882187826199883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118550844933019167536533021 44456566849882187826199883)
          ·
            refine ⟨66684850274823281739299825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44456566849882187826199883 66684850274823281739299825)
            ·
              refine ⟨50013637706117461304474869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66684850274823281739299825 50013637706117461304474869)
              ·
                refine ⟨4688778534948511997294519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50013637706117461304474869 4688778534948511997294519)
                ·
                  refine ⟨7033167802422767995941779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688778534948511997294519 7033167802422767995941779)
                  ·
                    refine ⟨10549751703634151993912669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7033167802422767995941779 10549751703634151993912669)
                    ·
                      refine ⟨3956156888862806997717251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10549751703634151993912669 3956156888862806997717251)
                      ·
                        rfl

theorem cell23_7704588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_7704588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704588 prefixEnd_7704588 := by exact prefixLift 7704588
  have htrace : WordTrace (prefixWord ++ tailWord_7704588) baseStart_7704588 baseEnd_7704588 := by
    simpa [prefixWord, tailWord_7704588, baseEnd_7704588] using wordTrace_append hprefix tailTrace_7704588
  have hstable : (prefixWord ++ tailWord_7704588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704588).length < 2 ^ (prefixWord ++ tailWord_7704588).sum := by decide
  have hdescent : baseEnd_7704588 < baseStart_7704588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704605 : List Nat := [1, 4, 2, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_7704605 : Nat := 118140960795 + 7704605 * 2 ^ 59
def prefixEnd_7704605 : Nat := 4983230072969 + 3 ^ 40 * 7704605 * 2
def baseEnd_7704605 : Nat := 3956165618033933431204673

theorem tailTrace_7704605 : CollatzResearch.WordTrace tailWord_7704605 prefixEnd_7704605 3956165618033933431204673 := by
  unfold tailWord_7704605
  simp only [CollatzResearch.WordTrace]
  refine ⟨281010030252539401619595269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187340020168359601079730179 281010030252539401619595269)
  ·
    refine ⟨52689380672351137803674113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281010030252539401619595269 52689380672351137803674113)
    ·
      refine ⟨39517035504263353352755585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52689380672351137803674113 39517035504263353352755585)
      ·
        refine ⟨29637776628197515014566689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39517035504263353352755585 29637776628197515014566689)
        ·
          refine ⟨22228332471148136260925017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29637776628197515014566689 22228332471148136260925017)
          ·
            refine ⟨16671249353361102195693763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22228332471148136260925017 16671249353361102195693763)
            ·
              refine ⟨25006874030041653293540645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16671249353361102195693763 25006874030041653293540645)
              ·
                refine ⟨4688788880632809992538871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25006874030041653293540645 4688788880632809992538871)
                ·
                  refine ⟨7033183320949214988808307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688788880632809992538871 7033183320949214988808307)
                  ·
                    refine ⟨10549774981423822483212461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7033183320949214988808307 10549774981423822483212461)
                    ·
                      refine ⟨3956165618033933431204673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10549774981423822483212461 3956165618033933431204673)
                      ·
                        rfl

theorem cell23_7704605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_7704605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704605 prefixEnd_7704605 := by exact prefixLift 7704605
  have htrace : WordTrace (prefixWord ++ tailWord_7704605) baseStart_7704605 baseEnd_7704605 := by
    simpa [prefixWord, tailWord_7704605, baseEnd_7704605] using wordTrace_append hprefix tailTrace_7704605
  have hstable : (prefixWord ++ tailWord_7704605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704605).length < 2 ^ (prefixWord ++ tailWord_7704605).sum := by decide
  have hdescent : baseEnd_7704605 < baseStart_7704605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704624 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_7704624 : Nat := 118140960795 + 7704624 * 2 ^ 59
def prefixEnd_7704624 : Nat := 4983230072969 + 3 ^ 40 * 7704624 * 2
def baseEnd_7704624 : Nat := 3956175374166368856867085

theorem tailTrace_7704624 : CollatzResearch.WordTrace tailWord_7704624 prefixEnd_7704624 3956175374166368856867085 := by
  unfold tailWord_7704624
  simp only [CollatzResearch.WordTrace]
  refine ⟨140505361619735283932268463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187340482159647045243024617 140505361619735283932268463)
  ·
    refine ⟨210758042429602925898402695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140505361619735283932268463 210758042429602925898402695)
    ·
      refine ⟨316137063644404388847604043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210758042429602925898402695 316137063644404388847604043)
      ·
        refine ⟨474205595466606583271406065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316137063644404388847604043 474205595466606583271406065)
        ·
          refine ⟨355654196599954937453554549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474205595466606583271406065 355654196599954937453554549)
          ·
            refine ⟨33342580931245775386270739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355654196599954937453554549 33342580931245775386270739)
            ·
              refine ⟨50013871396868663079406109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33342580931245775386270739 50013871396868663079406109)
              ·
                refine ⟨18755201773825748654777291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50013871396868663079406109 18755201773825748654777291)
                ·
                  refine ⟨28132802660738622982165937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18755201773825748654777291 28132802660738622982165937)
                  ·
                    refine ⟨21099601995553967236624453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28132802660738622982165937 21099601995553967236624453)
                    ·
                      refine ⟨3956175374166368856867085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21099601995553967236624453 3956175374166368856867085)
                      ·
                        rfl

theorem cell23_7704624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_7704624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704624 prefixEnd_7704624 := by exact prefixLift 7704624
  have htrace : WordTrace (prefixWord ++ tailWord_7704624) baseStart_7704624 baseEnd_7704624 := by
    simpa [prefixWord, tailWord_7704624, baseEnd_7704624] using wordTrace_append hprefix tailTrace_7704624
  have hstable : (prefixWord ++ tailWord_7704624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704624).length < 2 ^ (prefixWord ++ tailWord_7704624).sum := by decide
  have hdescent : baseEnd_7704624 < baseStart_7704624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704641 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7704641 : Nat := 118140960795 + 7704641 * 2 ^ 59
def prefixEnd_7704641 : Nat := 4983230072969 + 3 ^ 40 * 7704641 * 2
def baseEnd_7704641 : Nat := 3956184103337495290354507

theorem tailTrace_7704641 : CollatzResearch.WordTrace tailWord_7704641 prefixEnd_7704641 3956184103337495290354507 := by
  unfold tailWord_7704641
  simp only [CollatzResearch.WordTrace]
  refine ⟨281011343280408979767905777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187340895520272653178603851 281011343280408979767905777)
  ·
    refine ⟨210758507460306734825929333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281011343280408979767905777 210758507460306734825929333)
    ·
      refine ⟨19758610074403756389930875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210758507460306734825929333 19758610074403756389930875)
      ·
        refine ⟨29637915111605634584896313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19758610074403756389930875 29637915111605634584896313)
        ·
          refine ⟨22228436333704225938672235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29637915111605634584896313 22228436333704225938672235)
          ·
            refine ⟨33342654500556338908008353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22228436333704225938672235 33342654500556338908008353)
            ·
              refine ⟨25006990875417254181006265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33342654500556338908008353 25006990875417254181006265)
              ·
                refine ⟨18755243156562940635754699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25006990875417254181006265 18755243156562940635754699)
                ·
                  refine ⟨28132864734844410953632049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18755243156562940635754699 28132864734844410953632049)
                  ·
                    refine ⟨21099648551133308215224037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28132864734844410953632049 21099648551133308215224037)
                    ·
                      refine ⟨3956184103337495290354507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21099648551133308215224037 3956184103337495290354507)
                      ·
                        rfl

theorem cell23_7704641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7704641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704641 prefixEnd_7704641 := by exact prefixLift 7704641
  have htrace : WordTrace (prefixWord ++ tailWord_7704641) baseStart_7704641 baseEnd_7704641 := by
    simpa [prefixWord, tailWord_7704641, baseEnd_7704641] using wordTrace_append hprefix tailTrace_7704641
  have hstable : (prefixWord ++ tailWord_7704641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704641).length < 2 ^ (prefixWord ++ tailWord_7704641).sum := by decide
  have hdescent : baseEnd_7704641 < baseStart_7704641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704662 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_7704662 : Nat := 118140960795 + 7704662 * 2 ^ 59
def prefixEnd_7704662 : Nat := 4983230072969 + 3 ^ 40 * 7704662 * 2
def baseEnd_7704662 : Nat := 3956194886431239708191911

theorem tailTrace_7704662 : CollatzResearch.WordTrace tailWord_7704662 prefixEnd_7704662 3956194886431239708191911 := by
  unfold tailWord_7704662
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563256825833306272151265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187341406142221933569613493 17563256825833306272151265)
  ·
    refine ⟨13172442619374979704113449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17563256825833306272151265 13172442619374979704113449)
    ·
      refine ⟨9879331964531234778085087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13172442619374979704113449 9879331964531234778085087)
      ·
        refine ⟨14818997946796852167127631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879331964531234778085087 14818997946796852167127631)
        ·
          refine ⟨22228496920195278250691447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14818997946796852167127631 22228496920195278250691447)
          ·
            refine ⟨33342745380292917376037171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22228496920195278250691447 33342745380292917376037171)
            ·
              refine ⟨50014118070439376064055757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33342745380292917376037171 50014118070439376064055757)
              ·
                refine ⟨18755294276414766024020909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50014118070439376064055757 18755294276414766024020909)
                ·
                  refine ⟨7033235353655537259007841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18755294276414766024020909 7033235353655537259007841)
                  ·
                    refine ⟨5274926515241652944255881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7033235353655537259007841 5274926515241652944255881)
                    ·
                      refine ⟨3956194886431239708191911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274926515241652944255881 3956194886431239708191911)
                      ·
                        rfl

theorem cell23_7704662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_7704662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704662 prefixEnd_7704662 := by exact prefixLift 7704662
  have htrace : WordTrace (prefixWord ++ tailWord_7704662) baseStart_7704662 baseEnd_7704662 := by
    simpa [prefixWord, tailWord_7704662, baseEnd_7704662] using wordTrace_append hprefix tailTrace_7704662
  have hstable : (prefixWord ++ tailWord_7704662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704662).length < 2 ^ (prefixWord ++ tailWord_7704662).sum := by decide
  have hdescent : baseEnd_7704662 < baseStart_7704662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704671 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 3, 3, 2]
def baseStart_7704671 : Nat := 118140960795 + 7704671 * 2 ^ 59
def prefixEnd_7704671 : Nat := 4983230072969 + 3 ^ 40 * 7704671 * 2
def baseEnd_7704671 : Nat := 3956199507757130172979369

theorem tailTrace_7704671 : CollatzResearch.WordTrace tailWord_7704671 prefixEnd_7704671 3956199507757130172979369 := by
  unfold tailWord_7704671
  simp only [CollatzResearch.WordTrace]
  refine ⟨281012437470300294891497867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187341624980200196594331911 281012437470300294891497867)
  ·
    refine ⟨421518656205450442337246801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281012437470300294891497867 421518656205450442337246801)
    ·
      refine ⟨316138992154087831752935101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421518656205450442337246801 316138992154087831752935101)
      ·
        refine ⟨118552122057782936907350663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316138992154087831752935101 118552122057782936907350663)
        ·
          refine ⟨177828183086674405361025995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118552122057782936907350663 177828183086674405361025995)
          ·
            refine ⟨266742274630011608041538993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177828183086674405361025995 266742274630011608041538993)
            ·
              refine ⟨200056705972508706031154245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266742274630011608041538993 200056705972508706031154245)
              ·
                refine ⟨37510632369845382380841421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200056705972508706031154245 37510632369845382380841421)
                ·
                  refine ⟨14066487138692018392815533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37510632369845382380841421 14066487138692018392815533)
                  ·
                    refine ⟨5274932677009506897305825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14066487138692018392815533 5274932677009506897305825)
                    ·
                      refine ⟨3956199507757130172979369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274932677009506897305825 3956199507757130172979369)
                      ·
                        rfl

theorem cell23_7704671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_7704671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704671 prefixEnd_7704671 := by exact prefixLift 7704671
  have htrace : WordTrace (prefixWord ++ tailWord_7704671) baseStart_7704671 baseEnd_7704671 := by
    simpa [prefixWord, tailWord_7704671, baseEnd_7704671] using wordTrace_append hprefix tailTrace_7704671
  have hstable : (prefixWord ++ tailWord_7704671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704671).length < 2 ^ (prefixWord ++ tailWord_7704671).sum := by decide
  have hdescent : baseEnd_7704671 < baseStart_7704671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704688 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 1, 3, 2]
def baseStart_7704688 : Nat := 118140960795 + 7704688 * 2 ^ 59
def prefixEnd_7704688 : Nat := 4983230072969 + 3 ^ 40 * 7704688 * 2
def baseEnd_7704688 : Nat := 3956208236928256606466791

theorem tailTrace_7704688 : CollatzResearch.WordTrace tailWord_7704688 prefixEnd_7704688 3956208236928256606466791 := by
  unfold tailWord_7704688
  simp only [CollatzResearch.WordTrace]
  refine ⟨140506528755619353397433359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187342038340825804529911145 140506528755619353397433359)
  ·
    refine ⟨210759793133429030096150039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140506528755619353397433359 210759793133429030096150039)
    ·
      refine ⟨316139689700143545144225059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210759793133429030096150039 316139689700143545144225059)
      ·
        refine ⟨474209534550215317716337589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316139689700143545144225059 474209534550215317716337589)
        ·
          refine ⟨44457143864082686035906649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 474209534550215317716337589 44457143864082686035906649)
          ·
            refine ⟨33342857898062014526929987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44457143864082686035906649 33342857898062014526929987)
            ·
              refine ⟨50014286847093021790394981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33342857898062014526929987 50014286847093021790394981)
              ·
                refine ⟨9377678783829941585699059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50014286847093021790394981 9377678783829941585699059)
                ·
                  refine ⟨14066518175744912378548589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9377678783829941585699059 14066518175744912378548589)
                  ·
                    refine ⟨5274944315904342141955721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14066518175744912378548589 5274944315904342141955721)
                    ·
                      refine ⟨3956208236928256606466791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274944315904342141955721 3956208236928256606466791)
                      ·
                        rfl

theorem cell23_7704688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 3, 2].length) (baseStart_7704688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704688 prefixEnd_7704688 := by exact prefixLift 7704688
  have htrace : WordTrace (prefixWord ++ tailWord_7704688) baseStart_7704688 baseEnd_7704688 := by
    simpa [prefixWord, tailWord_7704688, baseEnd_7704688] using wordTrace_append hprefix tailTrace_7704688
  have hstable : (prefixWord ++ tailWord_7704688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704688).length < 2 ^ (prefixWord ++ tailWord_7704688).sum := by decide
  have hdescent : baseEnd_7704688 < baseStart_7704688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704704 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 3]
def baseStart_7704704 : Nat := 118140960795 + 7704704 * 2 ^ 59
def prefixEnd_7704704 : Nat := 4983230072969 + 3 ^ 40 * 7704704 * 2
def baseEnd_7704704 : Nat := 3956216452618728543866717

theorem tailTrace_7704704 : CollatzResearch.WordTrace tailWord_7704704 prefixEnd_7704704 3956216452618728543866717 := by
  unfold tailWord_7704704
  simp only [CollatzResearch.WordTrace]
  refine ⟨140506820539590370763724583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187342427386120494351632777 140506820539590370763724583)
  ·
    refine ⟨210760230809385556145586875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140506820539590370763724583 210760230809385556145586875)
    ·
      refine ⟨316140346214078334218380313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210760230809385556145586875 316140346214078334218380313)
      ·
        refine ⟨237105259660558750663785235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316140346214078334218380313 237105259660558750663785235)
        ·
          refine ⟨355657889490838125995677853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237105259660558750663785235 355657889490838125995677853)
          ·
            refine ⟨133371708559064297248379195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355657889490838125995677853 133371708559064297248379195)
            ·
              refine ⟨200057562838596445872568793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133371708559064297248379195 200057562838596445872568793)
              ·
                refine ⟨150043172128947334404426595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200057562838596445872568793 150043172128947334404426595)
                ·
                  refine ⟨225064758193421001606639893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150043172128947334404426595 225064758193421001606639893)
                  ·
                    refine ⟨10549910540316609450311245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 225064758193421001606639893 10549910540316609450311245)
                    ·
                      refine ⟨3956216452618728543866717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10549910540316609450311245 3956216452618728543866717)
                      ·
                        rfl

theorem cell23_7704704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_7704704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704704 prefixEnd_7704704 := by exact prefixLift 7704704
  have htrace : WordTrace (prefixWord ++ tailWord_7704704) baseStart_7704704 baseEnd_7704704 := by
    simpa [prefixWord, tailWord_7704704, baseEnd_7704704] using wordTrace_append hprefix tailTrace_7704704
  have hstable : (prefixWord ++ tailWord_7704704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704704).length < 2 ^ (prefixWord ++ tailWord_7704704).sum := by decide
  have hdescent : baseEnd_7704704 < baseStart_7704704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704769 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7704769 : Nat := 118140960795 + 7704769 * 2 ^ 59
def prefixEnd_7704769 : Nat := 4983230072969 + 3 ^ 40 * 7704769 * 2
def baseEnd_7704769 : Nat := 3956249828861270789553919

theorem tailTrace_7704769 : CollatzResearch.WordTrace tailWord_7704769 prefixEnd_7704769 3956249828861270789553919 := by
  unfold tailWord_7704769
  simp only [CollatzResearch.WordTrace]
  refine ⟨281016011823945257628565361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187344007882630171752376907 281016011823945257628565361)
  ·
    refine ⟨210762008867958943221424021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281016011823945257628565361 210762008867958943221424021)
    ·
      refine ⟨9879469165685575463504251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210762008867958943221424021 9879469165685575463504251)
      ·
        refine ⟨14819203748528363195256377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9879469165685575463504251 14819203748528363195256377)
        ·
          refine ⟨11114402811396272396442283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14819203748528363195256377 11114402811396272396442283)
          ·
            refine ⟨16671604217094408594663425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11114402811396272396442283 16671604217094408594663425)
            ·
              refine ⟨12503703162820806445997569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16671604217094408594663425 12503703162820806445997569)
              ·
                refine ⟨9377777372115604834498177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12503703162820806445997569 9377777372115604834498177)
                ·
                  refine ⟨7033333029086703625873633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9377777372115604834498177 7033333029086703625873633)
                  ·
                    refine ⟨5274999771815027719405225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7033333029086703625873633 5274999771815027719405225)
                    ·
                      refine ⟨3956249828861270789553919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5274999771815027719405225 3956249828861270789553919)
                      ·
                        rfl

theorem cell23_7704769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7704769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704769 prefixEnd_7704769 := by exact prefixLift 7704769
  have htrace : WordTrace (prefixWord ++ tailWord_7704769) baseStart_7704769 baseEnd_7704769 := by
    simpa [prefixWord, tailWord_7704769, baseEnd_7704769] using wordTrace_append hprefix tailTrace_7704769
  have hstable : (prefixWord ++ tailWord_7704769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704769).length < 2 ^ (prefixWord ++ tailWord_7704769).sum := by decide
  have hdescent : baseEnd_7704769 < baseStart_7704769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704808 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_7704808 : Nat := 118140960795 + 7704808 * 2 ^ 59
def prefixEnd_7704808 : Nat := 4983230072969 + 3 ^ 40 * 7704808 * 2
def baseEnd_7704808 : Nat := 3956269854606796136966239

theorem tailTrace_7704808 : CollatzResearch.WordTrace tailWord_7704808 prefixEnd_7704808 3956269854606796136966239 := by
  unfold tailWord_7704808
  simp only [CollatzResearch.WordTrace]
  refine ⟨140508717135401983644617539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187344956180535978192823385 140508717135401983644617539)
  ·
    refine ⟨210763075703102975466926309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140508717135401983644617539 210763075703102975466926309)
    ·
      refine ⟨39518076694331807900048683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210763075703102975466926309 39518076694331807900048683)
      ·
        refine ⟨59277115041497711850073025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39518076694331807900048683 59277115041497711850073025)
        ·
          refine ⟨44457836281123283887554769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59277115041497711850073025 44457836281123283887554769)
          ·
            refine ⟨33343377210842462915666077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44457836281123283887554769 33343377210842462915666077)
            ·
              refine ⟨12503766454065923593374779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33343377210842462915666077 12503766454065923593374779)
              ·
                refine ⟨18755649681098885390062169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12503766454065923593374779 18755649681098885390062169)
                ·
                  refine ⟨14066737260824164042546627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18755649681098885390062169 14066737260824164042546627)
                  ·
                    refine ⟨21100105891236246063819941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14066737260824164042546627 21100105891236246063819941)
                    ·
                      refine ⟨3956269854606796136966239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21100105891236246063819941 3956269854606796136966239)
                      ·
                        rfl

theorem cell23_7704808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_7704808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704808 prefixEnd_7704808 := by exact prefixLift 7704808
  have htrace : WordTrace (prefixWord ++ tailWord_7704808) baseStart_7704808 baseEnd_7704808 := by
    simpa [prefixWord, tailWord_7704808, baseEnd_7704808] using wordTrace_append hprefix tailTrace_7704808
  have hstable : (prefixWord ++ tailWord_7704808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704808).length < 2 ^ (prefixWord ++ tailWord_7704808).sum := by decide
  have hdescent : baseEnd_7704808 < baseStart_7704808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704811 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 3]
def baseStart_7704811 : Nat := 118140960795 + 7704811 * 2 ^ 59
def prefixEnd_7704811 : Nat := 4983230072969 + 3 ^ 40 * 7704811 * 2
def baseEnd_7704811 : Nat := 3956271395048759625228725

theorem tailTrace_7704811 : CollatzResearch.WordTrace tailWord_7704811 prefixEnd_7704811 3956271395048759625228725 := by
  unfold tailWord_7704811
  simp only [CollatzResearch.WordTrace]
  refine ⟨281017543689793098801594287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187345029126528732534396191 281017543689793098801594287)
  ·
    refine ⟨421526315534689648202391431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281017543689793098801594287 421526315534689648202391431)
    ·
      refine ⟨632289473302034472303587147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421526315534689648202391431 632289473302034472303587147)
      ·
        refine ⟨948434209953051708455380721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632289473302034472303587147 948434209953051708455380721)
        ·
          refine ⟨711325657464788781341535541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948434209953051708455380721 711325657464788781341535541)
          ·
            refine ⟨66686780387323948250768957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 711325657464788781341535541 66686780387323948250768957)
            ·
              refine ⟨25007542645246480594038359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66686780387323948250768957 25007542645246480594038359)
              ·
                refine ⟨37511313967869720891057539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25007542645246480594038359 37511313967869720891057539)
                ·
                  refine ⟨56266970951804581336586309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37511313967869720891057539 56266970951804581336586309)
                  ·
                    refine ⟨10550057053463359000609933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56266970951804581336586309 10550057053463359000609933)
                    ·
                      refine ⟨3956271395048759625228725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550057053463359000609933 3956271395048759625228725)
                      ·
                        rfl

theorem cell23_7704811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 3].length) (baseStart_7704811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704811 prefixEnd_7704811 := by exact prefixLift 7704811
  have htrace : WordTrace (prefixWord ++ tailWord_7704811) baseStart_7704811 baseEnd_7704811 := by
    simpa [prefixWord, tailWord_7704811, baseEnd_7704811] using wordTrace_append hprefix tailTrace_7704811
  have hstable : (prefixWord ++ tailWord_7704811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704811).length < 2 ^ (prefixWord ++ tailWord_7704811).sum := by decide
  have hdescent : baseEnd_7704811 < baseStart_7704811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704869 : List Nat := [1, 3, 1, 2, 6, 1, 1, 3, 1, 4]
def baseStart_7704869 : Nat := 118140960795 + 7704869 * 2 ^ 59
def prefixEnd_7704869 : Nat := 4983230072969 + 3 ^ 40 * 7704869 * 2
def baseEnd_7704869 : Nat := 1318767058975573466101153

theorem tailTrace_7704869 : CollatzResearch.WordTrace tailWord_7704869 prefixEnd_7704869 1318767058975573466101153 := by
  unfold tailWord_7704869
  simp only [CollatzResearch.WordTrace]
  refine ⟨281019659123582974707205661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187346439415721983138137107 281019659123582974707205661)
  ·
    refine ⟨105382372171343615515202123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281019659123582974707205661 105382372171343615515202123)
    ·
      refine ⟨158073558257015423272803185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105382372171343615515202123 158073558257015423272803185)
      ·
        refine ⟨118555168692761567454602389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158073558257015423272803185 118555168692761567454602389)
        ·
          refine ⟨5557273532473198474434487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118555168692761567454602389 5557273532473198474434487)
          ·
            refine ⟨8335910298709797711651731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557273532473198474434487 8335910298709797711651731)
            ·
              refine ⟨12503865448064696567477597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335910298709797711651731 12503865448064696567477597)
              ·
                refine ⟨4688949543024261212804099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12503865448064696567477597 4688949543024261212804099)
                ·
                  refine ⟨7033424314536391819206149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4688949543024261212804099 7033424314536391819206149)
                  ·
                    refine ⟨1318767058975573466101153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7033424314536391819206149 1318767058975573466101153)
                    ·
                      rfl

theorem cell23_7704869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_7704869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704869 prefixEnd_7704869 := by exact prefixLift 7704869
  have htrace : WordTrace (prefixWord ++ tailWord_7704869) baseStart_7704869 baseEnd_7704869 := by
    simpa [prefixWord, tailWord_7704869, baseEnd_7704869] using wordTrace_append hprefix tailTrace_7704869
  have hstable : (prefixWord ++ tailWord_7704869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704869).length < 2 ^ (prefixWord ++ tailWord_7704869).sum := by decide
  have hdescent : baseEnd_7704869 < baseStart_7704869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704885 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_7704885 : Nat := 118140960795 + 7704885 * 2 ^ 59
def prefixEnd_7704885 : Nat := 4983230072969 + 3 ^ 40 * 7704885 * 2
def baseEnd_7704885 : Nat := 3956309392617192335703385

theorem tailTrace_7704885 : CollatzResearch.WordTrace tailWord_7704885 prefixEnd_7704885 3956309392617192335703385 := by
  unfold tailWord_7704885
  simp only [CollatzResearch.WordTrace]
  refine ⟨281020242691525009439788109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187346828461016672959858739 281020242691525009439788109)
  ·
    refine ⟨105382591009321878539920541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281020242691525009439788109 105382591009321878539920541)
    ·
      refine ⟨39518471628495704452470203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105382591009321878539920541 39518471628495704452470203)
      ·
        refine ⟨59277707442743556678705305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39518471628495704452470203 59277707442743556678705305)
        ·
          refine ⟨44458280582057667509028979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59277707442743556678705305 44458280582057667509028979)
          ·
            refine ⟨66687420873086501263543469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44458280582057667509028979 66687420873086501263543469)
            ·
              refine ⟨25007782827407437973828801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66687420873086501263543469 25007782827407437973828801)
              ·
                refine ⟨18755837120555578480371601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25007782827407437973828801 18755837120555578480371601)
                ·
                  refine ⟨14066877840416683860278701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18755837120555578480371601 14066877840416683860278701)
                  ·
                    refine ⟨5275079190156256447604513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14066877840416683860278701 5275079190156256447604513)
                    ·
                      refine ⟨3956309392617192335703385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5275079190156256447604513 3956309392617192335703385)
                      ·
                        rfl

theorem cell23_7704885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_7704885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704885 prefixEnd_7704885 := by exact prefixLift 7704885
  have htrace : WordTrace (prefixWord ++ tailWord_7704885) baseStart_7704885 baseEnd_7704885 := by
    simpa [prefixWord, tailWord_7704885, baseEnd_7704885] using wordTrace_append hprefix tailTrace_7704885
  have hstable : (prefixWord ++ tailWord_7704885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704885).length < 2 ^ (prefixWord ++ tailWord_7704885).sum := by decide
  have hdescent : baseEnd_7704885 < baseStart_7704885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704901 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_7704901 : Nat := 118140960795 + 7704901 * 2 ^ 59
def prefixEnd_7704901 : Nat := 4983230072969 + 3 ^ 40 * 7704901 * 2
def baseEnd_7704901 : Nat := 3956317608307664273103311

theorem tailTrace_7704901 : CollatzResearch.WordTrace tailWord_7704901 prefixEnd_7704901 3956317608307664273103311 := by
  unfold tailWord_7704901
  simp only [CollatzResearch.WordTrace]
  refine ⟨281020826259467044172370557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187347217506311362781580371 281020826259467044172370557)
  ·
    refine ⟨105382809847300141564638959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281020826259467044172370557 105382809847300141564638959)
    ·
      refine ⟨158074214770950212346958439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105382809847300141564638959 158074214770950212346958439)
      ·
        refine ⟨237111322156425318520437659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158074214770950212346958439 237111322156425318520437659)
        ·
          refine ⟨355666983234637977780656489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237111322156425318520437659 355666983234637977780656489)
          ·
            refine ⟨266750237425978483335492367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355666983234637977780656489 266750237425978483335492367)
            ·
              refine ⟨400125356138967725003238551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266750237425978483335492367 400125356138967725003238551)
              ·
                refine ⟨600188034208451587504857827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400125356138967725003238551 600188034208451587504857827)
                ·
                  refine ⟨900282051312677381257286741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600188034208451587504857827 900282051312677381257286741)
                  ·
                    refine ⟨10550180288820438061608829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 900282051312677381257286741 10550180288820438061608829)
                    ·
                      refine ⟨3956317608307664273103311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550180288820438061608829 3956317608307664273103311)
                      ·
                        rfl

theorem cell23_7704901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_7704901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704901 prefixEnd_7704901 := by exact prefixLift 7704901
  have htrace : WordTrace (prefixWord ++ tailWord_7704901) baseStart_7704901 baseEnd_7704901 := by
    simpa [prefixWord, tailWord_7704901, baseEnd_7704901] using wordTrace_append hprefix tailTrace_7704901
  have hstable : (prefixWord ++ tailWord_7704901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704901).length < 2 ^ (prefixWord ++ tailWord_7704901).sum := by decide
  have hdescent : baseEnd_7704901 < baseStart_7704901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704935 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_7704935 : Nat := 118140960795 + 7704935 * 2 ^ 59
def prefixEnd_7704935 : Nat := 4983230072969 + 3 ^ 40 * 7704935 * 2
def baseEnd_7704935 : Nat := 3956335066649917140078155

theorem tailTrace_7704935 : CollatzResearch.WordTrace tailWord_7704935 prefixEnd_7704935 3956335066649917140078155 := by
  unfold tailWord_7704935
  simp only [CollatzResearch.WordTrace]
  refine ⟨281022066341343867979108259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187348044227562578652738839 281022066341343867979108259)
  ·
    refine ⟨421533099512015801968662389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281022066341343867979108259 421533099512015801968662389)
    ·
      refine ⟨39518728079251481434562099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 421533099512015801968662389 39518728079251481434562099)
      ·
        refine ⟨59278092118877222151843149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39518728079251481434562099 59278092118877222151843149)
        ·
          refine ⟨22229284544578958306941181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59278092118877222151843149 22229284544578958306941181)
          ·
            refine ⟨8335981704217109365102943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22229284544578958306941181 8335981704217109365102943)
            ·
              refine ⟨12503972556325664047654415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8335981704217109365102943 12503972556325664047654415)
              ·
                refine ⟨18755958834488496071481623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12503972556325664047654415 18755958834488496071481623)
                ·
                  refine ⟨28133938251732744107222435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18755958834488496071481623 28133938251732744107222435)
                  ·
                    refine ⟨42200907377599116160833653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28133938251732744107222435 42200907377599116160833653)
                    ·
                      refine ⟨3956335066649917140078155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42200907377599116160833653 3956335066649917140078155)
                      ·
                        rfl

theorem cell23_7704935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_7704935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704935 prefixEnd_7704935 := by exact prefixLift 7704935
  have htrace : WordTrace (prefixWord ++ tailWord_7704935) baseStart_7704935 baseEnd_7704935 := by
    simpa [prefixWord, tailWord_7704935, baseEnd_7704935] using wordTrace_append hprefix tailTrace_7704935
  have hstable : (prefixWord ++ tailWord_7704935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704935).length < 2 ^ (prefixWord ++ tailWord_7704935).sum := by decide
  have hdescent : baseEnd_7704935 < baseStart_7704935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704981 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_7704981 : Nat := 118140960795 + 7704981 * 2 ^ 59
def prefixEnd_7704981 : Nat := 4983230072969 + 3 ^ 40 * 7704981 * 2
def baseEnd_7704981 : Nat := 1318786228920007986700981

theorem tailTrace_7704981 : CollatzResearch.WordTrace tailWord_7704981 prefixEnd_7704981 1318786228920007986700981 := by
  unfold tailWord_7704981
  simp only [CollatzResearch.WordTrace]
  refine ⟨281023744099177217835282797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187349162732784811890188531 281023744099177217835282797)
  ·
    refine ⟨105383904037191456688231049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281023744099177217835282797 105383904037191456688231049)
    ·
      refine ⟨79037928027893592516173287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105383904037191456688231049 79037928027893592516173287)
      ·
        refine ⟨118556892041840388774259931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79037928027893592516173287 118556892041840388774259931)
        ·
          refine ⟨177835338062760583161389897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118556892041840388774259931 177835338062760583161389897)
          ·
            refine ⟨133376503547070437371042423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177835338062760583161389897 133376503547070437371042423)
            ·
              refine ⟨200064755320605656056563635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133376503547070437371042423 200064755320605656056563635)
              ·
                refine ⟨300097132980908484084845453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200064755320605656056563635 300097132980908484084845453)
                ·
                  refine ⟨112536424867840681531817045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300097132980908484084845453 112536424867840681531817045)
                  ·
                    refine ⟨1318786228920007986700981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112536424867840681531817045 1318786228920007986700981)
                    ·
                      rfl

theorem cell23_7704981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_7704981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704981 prefixEnd_7704981 := by exact prefixLift 7704981
  have htrace : WordTrace (prefixWord ++ tailWord_7704981) baseStart_7704981 baseEnd_7704981 := by
    simpa [prefixWord, tailWord_7704981, baseEnd_7704981] using wordTrace_append hprefix tailTrace_7704981
  have hstable : (prefixWord ++ tailWord_7704981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704981).length < 2 ^ (prefixWord ++ tailWord_7704981).sum := by decide
  have hdescent : baseEnd_7704981 < baseStart_7704981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704992 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 1, 3, 2]
def baseStart_7704992 : Nat := 118140960795 + 7704992 * 2 ^ 59
def prefixEnd_7704992 : Nat := 4983230072969 + 3 ^ 40 * 7704992 * 2
def baseEnd_7704992 : Nat := 3956364335047223417065393

theorem tailTrace_7704992 : CollatzResearch.WordTrace tailWord_7704992 prefixEnd_7704992 3956364335047223417065393 := by
  unfold tailWord_7704992
  simp only [CollatzResearch.WordTrace]
  refine ⟨140512072651068683356966615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187349430201424911142622153 140512072651068683356966615)
  ·
    refine ⟨210768108976603025035449923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140512072651068683356966615 210768108976603025035449923)
    ·
      refine ⟨316152163464904537553174885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210768108976603025035449923 316152163464904537553174885)
      ·
        refine ⟨59278530649669600791220291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316152163464904537553174885 59278530649669600791220291)
        ·
          refine ⟨88917795974504401186830437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59278530649669600791220291 88917795974504401186830437)
          ·
            refine ⟨16672086745219575222530707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88917795974504401186830437 16672086745219575222530707)
            ·
              refine ⟨25008130117829362833796061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16672086745219575222530707 25008130117829362833796061)
              ·
                refine ⟨9378048794186011062673523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25008130117829362833796061 9378048794186011062673523)
                ·
                  refine ⟨14067073191279016594010285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9378048794186011062673523 14067073191279016594010285)
                  ·
                    refine ⟨5275152446729631222753857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14067073191279016594010285 5275152446729631222753857)
                    ·
                      refine ⟨3956364335047223417065393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5275152446729631222753857 3956364335047223417065393)
                      ·
                        rfl

theorem cell23_7704992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_7704992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704992 prefixEnd_7704992 := by exact prefixLift 7704992
  have htrace : WordTrace (prefixWord ++ tailWord_7704992) baseStart_7704992 baseEnd_7704992 := by
    simpa [prefixWord, tailWord_7704992, baseEnd_7704992] using wordTrace_append hprefix tailTrace_7704992
  have hstable : (prefixWord ++ tailWord_7704992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704992).length < 2 ^ (prefixWord ++ tailWord_7704992).sum := by decide
  have hdescent : baseEnd_7704992 < baseStart_7704992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7704999 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_7704999 : Nat := 118140960795 + 7704999 * 2 ^ 59
def prefixEnd_7704999 : Nat := 4983230072969 + 3 ^ 40 * 7704999 * 2
def baseEnd_7704999 : Nat := 3956367929411804889677861

theorem tailTrace_7704999 : CollatzResearch.WordTrace tailWord_7704999 prefixEnd_7704999 3956367929411804889677861 := by
  unfold tailWord_7704999
  simp only [CollatzResearch.WordTrace]
  refine ⟨281024400613112006909438051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187349600408741337939625367 281024400613112006909438051)
  ·
    refine ⟨421536600919668010364157077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281024400613112006909438051 421536600919668010364157077)
    ·
      refine ⟨19759528168109437985819863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 421536600919668010364157077 19759528168109437985819863)
      ·
        refine ⟨29639292252164156978729795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19759528168109437985819863 29639292252164156978729795)
        ·
          refine ⟨44458938378246235468094693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29639292252164156978729795 44458938378246235468094693)
          ·
            refine ⟨8336050945921169150267755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44458938378246235468094693 8336050945921169150267755)
            ·
              refine ⟨12504076418881753725401633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336050945921169150267755 12504076418881753725401633)
              ·
                refine ⟨9378057314161315294051225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12504076418881753725401633 9378057314161315294051225)
                ·
                  refine ⟨7033542985620986470538419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9378057314161315294051225 7033542985620986470538419)
                  ·
                    refine ⟨10550314478431479705807629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7033542985620986470538419 10550314478431479705807629)
                    ·
                      refine ⟨3956367929411804889677861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550314478431479705807629 3956367929411804889677861)
                      ·
                        rfl

theorem cell23_7704999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_7704999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7704999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7704999 prefixEnd_7704999 := by exact prefixLift 7704999
  have htrace : WordTrace (prefixWord ++ tailWord_7704999) baseStart_7704999 baseEnd_7704999 := by
    simpa [prefixWord, tailWord_7704999, baseEnd_7704999] using wordTrace_append hprefix tailTrace_7704999
  have hstable : (prefixWord ++ tailWord_7704999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7704999).length < 2 ^ (prefixWord ++ tailWord_7704999).sum := by decide
  have hdescent : baseEnd_7704999 < baseStart_7704999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7704999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
