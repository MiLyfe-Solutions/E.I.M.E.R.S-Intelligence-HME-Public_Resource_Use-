import V185TrunkScan22Chunk162

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1456428 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_1456428 : Nat := 118140960795 + 1456428 * 2 ^ 59
def prefixEnd_1456428 : Nat := 4983230072969 + 3 ^ 40 * 1456428 * 2
def baseEnd_1456428 : Nat := 498565068444355301634677

theorem tailTrace_1456428 : CollatzResearch.WordTrace tailWord_1456428 prefixEnd_1456428 498565068444355301634677 := by
  unfold tailWord_1456428
  simp only [CollatzResearch.WordTrace]
  refine ⟨26560146583808784472228969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35413528778411712629638625 26560146583808784472228969)
  ·
    refine ⟨19920109937856588354171727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26560146583808784472228969 19920109937856588354171727)
    ·
      refine ⟨29880164906784882531257591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19920109937856588354171727 29880164906784882531257591)
      ·
        refine ⟨44820247360177323796886387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29880164906784882531257591 44820247360177323796886387)
        ·
          refine ⟨67230371040265985695329581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44820247360177323796886387 67230371040265985695329581)
          ·
            refine ⟨25211389140099744635748593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67230371040265985695329581 25211389140099744635748593)
            ·
              refine ⟨18908541855074808476811445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25211389140099744635748593 18908541855074808476811445)
              ·
                refine ⟨1772675798913263294701073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18908541855074808476811445 1772675798913263294701073)
                ·
                  refine ⟨1329506849184947471025805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1772675798913263294701073 1329506849184947471025805)
                  ·
                    refine ⟨498565068444355301634677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329506849184947471025805 498565068444355301634677)
                    ·
                      rfl

theorem cell22_1456428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_1456428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456428 prefixEnd_1456428 := by exact prefixLift 1456428
  have htrace : WordTrace (prefixWord ++ tailWord_1456428) baseStart_1456428 baseEnd_1456428 := by
    simpa [prefixWord, tailWord_1456428, baseEnd_1456428] using wordTrace_append hprefix tailTrace_1456428
  have hstable : (prefixWord ++ tailWord_1456428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456428).length < 2 ^ (prefixWord ++ tailWord_1456428).sum := by decide
  have hdescent : baseEnd_1456428 < baseStart_1456428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456471 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1456471 : Nat := 118140960795 + 1456471 * 2 ^ 59
def prefixEnd_1456471 : Nat := 4983230072969 + 3 ^ 40 * 1456471 * 2
def baseEnd_1456471 : Nat := 498579788223117522809545

theorem tailTrace_1456471 : CollatzResearch.WordTrace tailWord_1456471 prefixEnd_1456471 498579788223117522809545 := by
  unfold tailWord_1456471
  simp only [CollatzResearch.WordTrace]
  refine ⟨53121861506461787288273267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35414574337641191525515511 53121861506461787288273267)
  ·
    refine ⟨79682792259692680932409901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53121861506461787288273267 79682792259692680932409901)
    ·
      refine ⟨29881047097384755349653713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79682792259692680932409901 29881047097384755349653713)
      ·
        refine ⟨22410785323038566512240285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29881047097384755349653713 22410785323038566512240285)
        ·
          refine ⟨8404044496139462442090107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22410785323038566512240285 8404044496139462442090107)
          ·
            refine ⟨12606066744209193663135161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404044496139462442090107 12606066744209193663135161)
            ·
              refine ⟨9454550058156895247351371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12606066744209193663135161 9454550058156895247351371)
              ·
                refine ⟨14181825087235342871027057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9454550058156895247351371 14181825087235342871027057)
                ·
                  refine ⟨10636368815426507153270293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14181825087235342871027057 10636368815426507153270293)
                  ·
                    refine ⟨498579788223117522809545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10636368815426507153270293 498579788223117522809545)
                    ·
                      rfl

theorem cell22_1456471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1456471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456471 prefixEnd_1456471 := by exact prefixLift 1456471
  have htrace : WordTrace (prefixWord ++ tailWord_1456471) baseStart_1456471 baseEnd_1456471 := by
    simpa [prefixWord, tailWord_1456471, baseEnd_1456471] using wordTrace_append hprefix tailTrace_1456471
  have hstable : (prefixWord ++ tailWord_1456471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456471).length < 2 ^ (prefixWord ++ tailWord_1456471).sum := by decide
  have hdescent : baseEnd_1456471 < baseStart_1456471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456524 : List Nat := [2, 2, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_1456524 : Nat := 118140960795 + 1456524 * 2 ^ 59
def prefixEnd_1456524 : Nat := 4983230072969 + 3 ^ 40 * 1456524 * 2
def baseEnd_1456524 : Nat := 498597931206243051234383

theorem tailTrace_1456524 : CollatzResearch.WordTrace tailWord_1456524 prefixEnd_1456524 498597931206243051234383 := by
  unfold tailWord_1456524
  simp only [CollatzResearch.WordTrace]
  refine ⟨26561897287634888669976313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35415863050179851559968417 26561897287634888669976313)
  ·
    refine ⟨19921422965726166502482235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26561897287634888669976313 19921422965726166502482235)
    ·
      refine ⟨29882134448589249753723353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19921422965726166502482235 29882134448589249753723353)
      ·
        refine ⟨22411600836441937315292515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29882134448589249753723353 22411600836441937315292515)
        ·
          refine ⟨33617401254662905972938773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22411600836441937315292515 33617401254662905972938773)
          ·
            refine ⟨1575815683812323717481505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33617401254662905972938773 1575815683812323717481505)
            ·
              refine ⟨1181861762859242788111129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575815683812323717481505 1181861762859242788111129)
              ·
                refine ⟨886396322144432091083347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181861762859242788111129 886396322144432091083347)
                ·
                  refine ⟨1329594483216648136625021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886396322144432091083347 1329594483216648136625021)
                  ·
                    refine ⟨498597931206243051234383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329594483216648136625021 498597931206243051234383)
                    ·
                      rfl

theorem cell22_1456524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_1456524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456524 prefixEnd_1456524 := by exact prefixLift 1456524
  have htrace : WordTrace (prefixWord ++ tailWord_1456524) baseStart_1456524 baseEnd_1456524 := by
    simpa [prefixWord, tailWord_1456524, baseEnd_1456524] using wordTrace_append hprefix tailTrace_1456524
  have hstable : (prefixWord ++ tailWord_1456524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456524).length < 2 ^ (prefixWord ++ tailWord_1456524).sum := by decide
  have hdescent : baseEnd_1456524 < baseStart_1456524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456567 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 1, 4]
def baseStart_1456567 : Nat := 118140960795 + 1456567 * 2 ^ 59
def prefixEnd_1456567 : Nat := 4983230072969 + 3 ^ 40 * 1456567 * 2
def baseEnd_1456567 : Nat := 498612650985005272409251

theorem tailTrace_1456567 : CollatzResearch.WordTrace tailWord_1456567 prefixEnd_1456567 498612650985005272409251 := by
  unfold tailWord_1456567
  simp only [CollatzResearch.WordTrace]
  refine ⟨53125362914113995683767955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35416908609409330455845303 53125362914113995683767955)
  ·
    refine ⟨79688044371170993525651933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53125362914113995683767955 79688044371170993525651933)
    ·
      refine ⟨29883016639189122572119475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79688044371170993525651933 29883016639189122572119475)
      ·
        refine ⟨44824524958783683858179213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29883016639189122572119475 44824524958783683858179213)
        ·
          refine ⟨16809196859543881446817205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44824524958783683858179213 16809196859543881446817205)
          ·
            refine ⟨1575862205582238885639113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16809196859543881446817205 1575862205582238885639113)
            ·
              refine ⟨1181896654186679164229335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575862205582238885639113 1181896654186679164229335)
              ·
                refine ⟨1772844981280018746344003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181896654186679164229335 1772844981280018746344003)
                ·
                  refine ⟨2659267471920028119516005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772844981280018746344003 2659267471920028119516005)
                  ·
                    refine ⟨498612650985005272409251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2659267471920028119516005 498612650985005272409251)
                    ·
                      rfl

theorem cell22_1456567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_1456567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456567 prefixEnd_1456567 := by exact prefixLift 1456567
  have htrace : WordTrace (prefixWord ++ tailWord_1456567) baseStart_1456567 baseEnd_1456567 := by
    simpa [prefixWord, tailWord_1456567, baseEnd_1456567] using wordTrace_append hprefix tailTrace_1456567
  have hstable : (prefixWord ++ tailWord_1456567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456567).length < 2 ^ (prefixWord ++ tailWord_1456567).sum := by decide
  have hdescent : baseEnd_1456567 < baseStart_1456567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456717 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1456717 : Nat := 118140960795 + 1456717 * 2 ^ 59
def prefixEnd_1456717 : Nat := 4983230072969 + 3 ^ 40 * 1456717 * 2
def baseEnd_1456717 : Nat := 166221333016818293719597

theorem tailTrace_1456717 : CollatzResearch.WordTrace tailWord_1456717 prefixEnd_1456717 166221333016818293719597 := by
  unfold tailWord_1456717
  simp only [CollatzResearch.WordTrace]
  refine ⟨53130833863570571301728405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35420555909047047534485603 53130833863570571301728405)
  ·
    refine ⟨2490507837354870529768519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53130833863570571301728405 2490507837354870529768519)
    ·
      refine ⟨3735761756032305794652779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2490507837354870529768519 3735761756032305794652779)
      ·
        refine ⟨5603642634048458691979169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735761756032305794652779 5603642634048458691979169)
        ·
          refine ⟨4202731975536344018984377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5603642634048458691979169 4202731975536344018984377)
          ·
            refine ⟨3152048981652258014238283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4202731975536344018984377 3152048981652258014238283)
            ·
              refine ⟨4728073472478387021357425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152048981652258014238283 4728073472478387021357425)
              ·
                refine ⟨3546055104358790266018069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4728073472478387021357425 3546055104358790266018069)
                ·
                  refine ⟨166221333016818293719597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3546055104358790266018069 166221333016818293719597)
                  ·
                    rfl

theorem cell22_1456717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1456717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456717 prefixEnd_1456717 := by exact prefixLift 1456717
  have htrace : WordTrace (prefixWord ++ tailWord_1456717) baseStart_1456717 baseEnd_1456717 := by
    simpa [prefixWord, tailWord_1456717, baseEnd_1456717] using wordTrace_append hprefix tailTrace_1456717
  have hstable : (prefixWord ++ tailWord_1456717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456717).length < 2 ^ (prefixWord ++ tailWord_1456717).sum := by decide
  have hdescent : baseEnd_1456717 < baseStart_1456717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456728 : List Nat := [2, 1, 2, 2, 1, 2, 2, 10]
def baseStart_1456728 : Nat := 118140960795 + 1456728 * 2 ^ 59
def prefixEnd_1456728 : Nat := 4983230072969 + 3 ^ 40 * 1456728 * 2
def baseEnd_1456728 : Nat := 55407529397250502125973

theorem tailTrace_1456728 : CollatzResearch.WordTrace tailWord_1456728 prefixEnd_1456728 55407529397250502125973 := by
  unfold tailWord_1456728
  simp only [CollatzResearch.WordTrace]
  refine ⟨26565617533265360090189419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35420823377687146786919225 26565617533265360090189419)
  ·
    refine ⟨39848426299898040135284129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26565617533265360090189419 39848426299898040135284129)
    ·
      refine ⟨29886319724923530101463097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39848426299898040135284129 29886319724923530101463097)
      ·
        refine ⟨22414739793692647576097323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29886319724923530101463097 22414739793692647576097323)
        ·
          refine ⟨33622109690538971364145985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22414739793692647576097323 33622109690538971364145985)
          ·
            refine ⟨25216582267904228523109489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33622109690538971364145985 25216582267904228523109489)
            ·
              refine ⟨18912436700928171392332117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25216582267904228523109489 18912436700928171392332117)
              ·
                refine ⟨55407529397250502125973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18912436700928171392332117 55407529397250502125973)
                ·
                  rfl

theorem cell22_1456728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 10].length) (baseStart_1456728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456728 prefixEnd_1456728 := by exact prefixLift 1456728
  have htrace : WordTrace (prefixWord ++ tailWord_1456728) baseStart_1456728 baseEnd_1456728 := by
    simpa [prefixWord, tailWord_1456728, baseEnd_1456728] using wordTrace_append hprefix tailTrace_1456728
  have hstable : (prefixWord ++ tailWord_1456728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456728).length < 2 ^ (prefixWord ++ tailWord_1456728).sum := by decide
  have hdescent : baseEnd_1456728 < baseStart_1456728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456749 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_1456749 : Nat := 118140960795 + 1456749 * 2 ^ 59
def prefixEnd_1456749 : Nat := 4983230072969 + 3 ^ 40 * 1456749 * 2
def baseEnd_1456749 : Nat := 498674953304417464358693

theorem tailTrace_1456749 : CollatzResearch.WordTrace tailWord_1456749 prefixEnd_1456749 498674953304417464358693 := by
  unfold tailWord_1456749
  simp only [CollatzResearch.WordTrace]
  refine ⟨53132000999454640766893301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35421333999636427177928867 53132000999454640766893301)
  ·
    refine ⟨4981125093698872571896247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53132000999454640766893301 4981125093698872571896247)
    ·
      refine ⟨7471687640548308857844371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4981125093698872571896247 7471687640548308857844371)
      ·
        refine ⟨11207531460822463286766557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7471687640548308857844371 11207531460822463286766557)
        ·
          refine ⟨4202824297808423732537459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11207531460822463286766557 4202824297808423732537459)
          ·
            refine ⟨6304236446712635598806189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202824297808423732537459 6304236446712635598806189)
            ·
              refine ⟨2364088667517238349552321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6304236446712635598806189 2364088667517238349552321)
              ·
                refine ⟨1773066500637928762164241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2364088667517238349552321 1773066500637928762164241)
                ·
                  refine ⟨1329799875478446571623181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1773066500637928762164241 1329799875478446571623181)
                  ·
                    refine ⟨498674953304417464358693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329799875478446571623181 498674953304417464358693)
                    ·
                      rfl

theorem cell22_1456749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_1456749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456749 prefixEnd_1456749 := by exact prefixLift 1456749
  have htrace : WordTrace (prefixWord ++ tailWord_1456749) baseStart_1456749 baseEnd_1456749 := by
    simpa [prefixWord, tailWord_1456749, baseEnd_1456749] using wordTrace_append hprefix tailTrace_1456749
  have hstable : (prefixWord ++ tailWord_1456749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456749).length < 2 ^ (prefixWord ++ tailWord_1456749).sum := by decide
  have hdescent : baseEnd_1456749 < baseStart_1456749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456760 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 7, 3]
def baseStart_1456760 : Nat := 118140960795 + 1456760 * 2 ^ 59
def prefixEnd_1456760 : Nat := 4983230072969 + 3 ^ 40 * 1456760 * 2
def baseEnd_1456760 : Nat := 498678718829217102333659

theorem tailTrace_1456760 : CollatzResearch.WordTrace tailWord_1456760 prefixEnd_1456760 498678718829217102333659 := by
  unfold tailWord_1456760
  simp only [CollatzResearch.WordTrace]
  refine ⟨26566201101207394822771867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35421601468276526430362489 26566201101207394822771867)
  ·
    refine ⟨39849301651811092234157801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26566201101207394822771867 39849301651811092234157801)
    ·
      refine ⟨29886976238858319175618351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39849301651811092234157801 29886976238858319175618351)
      ·
        refine ⟨44830464358287478763427527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29886976238858319175618351 44830464358287478763427527)
        ·
          refine ⟨67245696537431218145141291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44830464358287478763427527 67245696537431218145141291)
          ·
            refine ⟨100868544806146827217711937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67245696537431218145141291 100868544806146827217711937)
            ·
              refine ⟨75651408604610120413283953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100868544806146827217711937 75651408604610120413283953)
              ·
                refine ⟨56738556453457590309962965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75651408604610120413283953 56738556453457590309962965)
                ·
                  refine ⟨1329809916877912272889757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 56738556453457590309962965 1329809916877912272889757)
                  ·
                    refine ⟨498678718829217102333659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329809916877912272889757 498678718829217102333659)
                    ·
                      rfl

theorem cell22_1456760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_1456760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456760 prefixEnd_1456760 := by exact prefixLift 1456760
  have htrace : WordTrace (prefixWord ++ tailWord_1456760) baseStart_1456760 baseEnd_1456760 := by
    simpa [prefixWord, tailWord_1456760, baseEnd_1456760] using wordTrace_append hprefix tailTrace_1456760
  have hstable : (prefixWord ++ tailWord_1456760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456760).length < 2 ^ (prefixWord ++ tailWord_1456760).sum := by decide
  have hdescent : baseEnd_1456760 < baseStart_1456760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456869 : List Nat := [1, 3, 1, 4, 1, 3, 1, 4, 4]
def baseStart_1456869 : Nat := 118140960795 + 1456869 * 2 ^ 59
def prefixEnd_1456869 : Nat := 4983230072969 + 3 ^ 40 * 1456869 * 2
def baseEnd_1456869 : Nat := 166238677252259050452775

theorem tailTrace_1456869 : CollatzResearch.WordTrace tailWord_1456869 prefixEnd_1456869 166238677252259050452775 := by
  unfold tailWord_1456869
  simp only [CollatzResearch.WordTrace]
  refine ⟨53136377759019901261261661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35424251839346600840841107 53136377759019901261261661)
  ·
    refine ⟨19926141659632462972973123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53136377759019901261261661 19926141659632462972973123)
    ·
      refine ⟨29889212489448694459459685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19926141659632462972973123 29889212489448694459459685)
      ·
        refine ⟨5604227341771630211148691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29889212489448694459459685 5604227341771630211148691)
        ·
          refine ⟨8406341012657445316723037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5604227341771630211148691 8406341012657445316723037)
          ·
            refine ⟨3152377879746541993771139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8406341012657445316723037 3152377879746541993771139)
            ·
              refine ⟨4728566819619812990656709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152377879746541993771139 4728566819619812990656709)
              ·
                refine ⟨886606278678714935748133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4728566819619812990656709 886606278678714935748133)
                ·
                  refine ⟨166238677252259050452775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 886606278678714935748133 166238677252259050452775)
                  ·
                    rfl

theorem cell22_1456869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_1456869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456869 prefixEnd_1456869 := by exact prefixLift 1456869
  have htrace : WordTrace (prefixWord ++ tailWord_1456869) baseStart_1456869 baseEnd_1456869 := by
    simpa [prefixWord, tailWord_1456869, baseEnd_1456869] using wordTrace_append hprefix tailTrace_1456869
  have hstable : (prefixWord ++ tailWord_1456869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456869).length < 2 ^ (prefixWord ++ tailWord_1456869).sum := by decide
  have hdescent : baseEnd_1456869 < baseStart_1456869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456914 : List Nat := [3, 2, 4, 1, 2, 1, 9]
def baseStart_1456914 : Nat := 118140960795 + 1456914 * 2 ^ 59
def prefixEnd_1456914 : Nat := 4983230072969 + 3 ^ 40 * 1456914 * 2
def baseEnd_1456914 : Nat := 18471534673200445703081

theorem tailTrace_1456914 : CollatzResearch.WordTrace tailWord_1456914 prefixEnd_1456914 18471534673200445703081 := by
  unfold tailWord_1456914
  simp only [CollatzResearch.WordTrace]
  refine ⟨13284504760964218486662449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35425346029237915964433197 13284504760964218486662449)
  ·
    refine ⟨9963378570723163864996837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13284504760964218486662449 9963378570723163864996837)
    ·
      refine ⟨1868133482010593224686907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9963378570723163864996837 1868133482010593224686907)
      ·
        refine ⟨2802200223015889837030361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868133482010593224686907 2802200223015889837030361)
        ·
          refine ⟨2101650167261917377772771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2802200223015889837030361 2101650167261917377772771)
          ·
            refine ⟨3152475250892876066659157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101650167261917377772771 3152475250892876066659157)
            ·
              refine ⟨18471534673200445703081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3152475250892876066659157 18471534673200445703081)
              ·
                rfl

theorem cell22_1456914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 9].length) (baseStart_1456914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456914 prefixEnd_1456914 := by exact prefixLift 1456914
  have htrace : WordTrace (prefixWord ++ tailWord_1456914) baseStart_1456914 baseEnd_1456914 := by
    simpa [prefixWord, tailWord_1456914, baseEnd_1456914] using wordTrace_append hprefix tailTrace_1456914
  have hstable : (prefixWord ++ tailWord_1456914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456914).length < 2 ^ (prefixWord ++ tailWord_1456914).sum := by decide
  have hdescent : baseEnd_1456914 < baseStart_1456914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456929 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1456929 : Nat := 118140960795 + 1456929 * 2 ^ 59
def prefixEnd_1456929 : Nat := 4983230072969 + 3 ^ 40 * 1456929 * 2
def baseEnd_1456929 : Nat := 498736570982956994858141

theorem tailTrace_1456929 : CollatzResearch.WordTrace tailWord_1456929 prefixEnd_1456929 498736570982956994858141 := by
  unfold tailWord_1456929
  simp only [CollatzResearch.WordTrace]
  refine ⟨53138566138802531508445841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35425710759201687672297227 53138566138802531508445841)
  ·
    refine ⟨39853924604101898631334381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53138566138802531508445841 39853924604101898631334381)
    ·
      refine ⟨14945221726538211986750393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39853924604101898631334381 14945221726538211986750393)
      ·
        refine ⟨11208916294903658990062795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14945221726538211986750393 11208916294903658990062795)
        ·
          refine ⟨16813374442355488485094193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11208916294903658990062795 16813374442355488485094193)
          ·
            refine ⟨12610030831766616363820645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16813374442355488485094193 12610030831766616363820645)
            ·
              refine ⟨2364380780956240568216371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12610030831766616363820645 2364380780956240568216371)
              ·
                refine ⟨3546571171434360852324557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364380780956240568216371 3546571171434360852324557)
                ·
                  refine ⟨1329964189287885319621709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3546571171434360852324557 1329964189287885319621709)
                  ·
                    refine ⟨498736570982956994858141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329964189287885319621709 498736570982956994858141)
                    ·
                      rfl

theorem cell22_1456929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1456929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456929 prefixEnd_1456929 := by exact prefixLift 1456929
  have htrace : WordTrace (prefixWord ++ tailWord_1456929) baseStart_1456929 baseEnd_1456929 := by
    simpa [prefixWord, tailWord_1456929, baseEnd_1456929] using wordTrace_append hprefix tailTrace_1456929
  have hstable : (prefixWord ++ tailWord_1456929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456929).length < 2 ^ (prefixWord ++ tailWord_1456929).sum := by decide
  have hdescent : baseEnd_1456929 < baseStart_1456929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456948 : List Nat := [2, 5, 1, 1, 4, 1, 2, 6]
def baseStart_1456948 : Nat := 118140960795 + 1456948 * 2 ^ 59
def prefixEnd_1456948 : Nat := 4983230072969 + 3 ^ 40 * 1456948 * 2
def baseEnd_1456948 : Nat := 55415897230138586514787

theorem tailTrace_1456948 : CollatzResearch.WordTrace tailWord_1456948 prefixEnd_1456948 55415897230138586514787 := by
  unfold tailWord_1456948
  simp only [CollatzResearch.WordTrace]
  refine ⟨26569629562866848876693749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35426172750489131835591665 26569629562866848876693749)
  ·
    refine ⟨2490902771518767082190039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26569629562866848876693749 2490902771518767082190039)
    ·
      refine ⟨3736354157278150623285059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2490902771518767082190039 3736354157278150623285059)
      ·
        refine ⟨5604531235917225934927589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3736354157278150623285059 5604531235917225934927589)
        ·
          refine ⟨1050849606734479862798923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5604531235917225934927589 1050849606734479862798923)
          ·
            refine ⟨1576274410101719794198385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050849606734479862798923 1576274410101719794198385)
            ·
              refine ⟨1182205807576289845648789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1576274410101719794198385 1182205807576289845648789)
              ·
                refine ⟨55415897230138586514787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1182205807576289845648789 55415897230138586514787)
                ·
                  rfl

theorem cell22_1456948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 6].length) (baseStart_1456948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456948 prefixEnd_1456948 := by exact prefixLift 1456948
  have htrace : WordTrace (prefixWord ++ tailWord_1456948) baseStart_1456948 baseEnd_1456948 := by
    simpa [prefixWord, tailWord_1456948, baseEnd_1456948] using wordTrace_append hprefix tailTrace_1456948
  have hstable : (prefixWord ++ tailWord_1456948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456948).length < 2 ^ (prefixWord ++ tailWord_1456948).sum := by decide
  have hdescent : baseEnd_1456948 < baseStart_1456948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456980 : List Nat := [2, 4, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_1456980 : Nat := 118140960795 + 1456980 * 2 ^ 59
def prefixEnd_1456980 : Nat := 4983230072969 + 3 ^ 40 * 1456980 * 2
def baseEnd_1456980 : Nat := 498754029325209861832985

theorem tailTrace_1456980 : CollatzResearch.WordTrace tailWord_1456980 prefixEnd_1456980 498754029325209861832985 := by
  unfold tailWord_1456980
  simp only [CollatzResearch.WordTrace]
  refine ⟨26570213130808883609276197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35426950841078511479034929 26570213130808883609276197)
  ·
    refine ⟨4981914962026665676739287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26570213130808883609276197 4981914962026665676739287)
    ·
      refine ⟨7472872443039998515108931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4981914962026665676739287 7472872443039998515108931)
      ·
        refine ⟨11209308664559997772663397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7472872443039998515108931 11209308664559997772663397)
        ·
          refine ⟨2101745374604999582374387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11209308664559997772663397 2101745374604999582374387)
          ·
            refine ⟨3152618061907499373561581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101745374604999582374387 3152618061907499373561581)
            ·
              refine ⟨1182231773215312265085593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3152618061907499373561581 1182231773215312265085593)
              ·
                refine ⟨886673829911484198814195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1182231773215312265085593 886673829911484198814195)
                ·
                  refine ⟨1330010744867226298221293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886673829911484198814195 1330010744867226298221293)
                  ·
                    refine ⟨498754029325209861832985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1330010744867226298221293 498754029325209861832985)
                    ·
                      rfl

theorem cell22_1456980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_1456980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1456980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1456980 prefixEnd_1456980 := by exact prefixLift 1456980
  have htrace : WordTrace (prefixWord ++ tailWord_1456980) baseStart_1456980 baseEnd_1456980 := by
    simpa [prefixWord, tailWord_1456980, baseEnd_1456980] using wordTrace_append hprefix tailTrace_1456980
  have hstable : (prefixWord ++ tailWord_1456980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456980).length < 2 ^ (prefixWord ++ tailWord_1456980).sum := by decide
  have hdescent : baseEnd_1456980 < baseStart_1456980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457006 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1457006 : Nat := 118140960795 + 1457006 * 2 ^ 59
def prefixEnd_1457006 : Nat := 4983230072969 + 3 ^ 40 * 1457006 * 2
def baseEnd_1457006 : Nat := 498762929656554460682905

theorem tailTrace_1457006 : CollatzResearch.WordTrace tailWord_1457006 prefixEnd_1457006 498762929656554460682905 := by
  unfold tailWord_1457006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6642671819940446707374859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35427583039682382439332581 6642671819940446707374859)
  ·
    refine ⟨9964007729910670061062289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6642671819940446707374859 9964007729910670061062289)
    ·
      refine ⟨7473005797433002545796717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9964007729910670061062289 7473005797433002545796717)
      ·
        refine ⟨2802377174037375954673769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7473005797433002545796717 2802377174037375954673769)
        ·
          refine ⟨2101782880528031966005327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2802377174037375954673769 2101782880528031966005327)
          ·
            refine ⟨3152674320792047949007991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101782880528031966005327 3152674320792047949007991)
            ·
              refine ⟨4729011481188071923511987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152674320792047949007991 4729011481188071923511987)
              ·
                refine ⟨7093517221782107885267981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729011481188071923511987 7093517221782107885267981)
                ·
                  refine ⟨2660068958168290456975493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7093517221782107885267981 2660068958168290456975493)
                  ·
                    refine ⟨498762929656554460682905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2660068958168290456975493 498762929656554460682905)
                    ·
                      rfl

theorem cell22_1457006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1457006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457006 prefixEnd_1457006 := by exact prefixLift 1457006
  have htrace : WordTrace (prefixWord ++ tailWord_1457006) baseStart_1457006 baseEnd_1457006 := by
    simpa [prefixWord, tailWord_1457006, baseEnd_1457006] using wordTrace_append hprefix tailTrace_1457006
  have hstable : (prefixWord ++ tailWord_1457006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457006).length < 2 ^ (prefixWord ++ tailWord_1457006).sum := by decide
  have hdescent : baseEnd_1457006 < baseStart_1457006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457032 : List Nat := [2, 1, 3, 3, 2, 11]
def baseStart_1457032 : Nat := 118140960795 + 1457032 * 2 ^ 59
def prefixEnd_1457032 : Nat := 4983230072969 + 3 ^ 40 * 1457032 * 2
def baseEnd_1457032 : Nat := 6157676913430852586825

theorem tailTrace_1457032 : CollatzResearch.WordTrace tailWord_1457032 prefixEnd_1457032 6157676913430852586825 := by
  unfold tailWord_1457032
  simp only [CollatzResearch.WordTrace]
  refine ⟨26571161428714690049722675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35428215238286253399630233 26571161428714690049722675)
  ·
    refine ⟨39856742143072035074584013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26571161428714690049722675 39856742143072035074584013)
    ·
      refine ⟨14946278303652013152969005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39856742143072035074584013 14946278303652013152969005)
      ·
        refine ⟨5604854363869504932363377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14946278303652013152969005 5604854363869504932363377)
        ·
          refine ⟨4203640772902128699272533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5604854363869504932363377 4203640772902128699272533)
          ·
            refine ⟨6157676913430852586825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4203640772902128699272533 6157676913430852586825)
            ·
              rfl

theorem cell22_1457032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 11].length) (baseStart_1457032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457032 prefixEnd_1457032 := by exact prefixLift 1457032
  have htrace : WordTrace (prefixWord ++ tailWord_1457032) baseStart_1457032 baseEnd_1457032 := by
    simpa [prefixWord, tailWord_1457032, baseEnd_1457032] using wordTrace_append hprefix tailTrace_1457032
  have hstable : (prefixWord ++ tailWord_1457032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457032).length < 2 ^ (prefixWord ++ tailWord_1457032).sum := by decide
  have hdescent : baseEnd_1457032 < baseStart_1457032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457186 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1457186 : Nat := 118140960795 + 1457186 * 2 ^ 59
def prefixEnd_1457186 : Nat := 4983230072969 + 3 ^ 40 * 1457186 * 2
def baseEnd_1457186 : Nat := 498824547335093991182353

theorem tailTrace_1457186 : CollatzResearch.WordTrace tailWord_1457186 prefixEnd_1457186 498824547335093991182353 := by
  unfold tailWord_1457186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13286984924717866100137853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35431959799247642933700941 13286984924717866100137853)
  ·
    refine ⟨4982619346769199787551695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13286984924717866100137853 4982619346769199787551695)
    ·
      refine ⟨7473929020153799681327543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4982619346769199787551695 7473929020153799681327543)
      ·
        refine ⟨11210893530230699521991315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7473929020153799681327543 11210893530230699521991315)
        ·
          refine ⟨16816340295346049282986973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11210893530230699521991315 16816340295346049282986973)
          ·
            refine ⟨6306127610754768481120115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16816340295346049282986973 6306127610754768481120115)
            ·
              refine ⟨9459191416132152721680173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306127610754768481120115 9459191416132152721680173)
              ·
                refine ⟨3547196781049557270630065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9459191416132152721680173 3547196781049557270630065)
                ·
                  refine ⟨2660397585787167952972549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3547196781049557270630065 2660397585787167952972549)
                  ·
                    refine ⟨498824547335093991182353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2660397585787167952972549 498824547335093991182353)
                    ·
                      rfl

theorem cell22_1457186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1457186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457186 prefixEnd_1457186 := by exact prefixLift 1457186
  have htrace : WordTrace (prefixWord ++ tailWord_1457186) baseStart_1457186 baseEnd_1457186 := by
    simpa [prefixWord, tailWord_1457186, baseEnd_1457186] using wordTrace_append hprefix tailTrace_1457186
  have hstable : (prefixWord ++ tailWord_1457186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457186).length < 2 ^ (prefixWord ++ tailWord_1457186).sum := by decide
  have hdescent : baseEnd_1457186 < baseStart_1457186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457216 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 3, 3]
def baseStart_1457216 : Nat := 118140960795 + 1457216 * 2 ^ 59
def prefixEnd_1457216 : Nat := 4983230072969 + 3 ^ 40 * 1457216 * 2
def baseEnd_1457216 : Nat := 498834816948183912932261

theorem tailTrace_1457216 : CollatzResearch.WordTrace tailWord_1457216 prefixEnd_1457216 498834816948183912932261 := by
  unfold tailWord_1457216
  simp only [CollatzResearch.WordTrace]
  refine ⟨26574516944381389762071751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35432689259175186349429001 26574516944381389762071751)
  ·
    refine ⟨39861775416572084643107627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26574516944381389762071751 39861775416572084643107627)
    ·
      refine ⟨59792663124858126964661441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39861775416572084643107627 59792663124858126964661441)
      ·
        refine ⟨44844497343643595223496081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59792663124858126964661441 44844497343643595223496081)
        ·
          refine ⟨33633373007732696417622061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44844497343643595223496081 33633373007732696417622061)
          ·
            refine ⟨12612514877899761156608273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33633373007732696417622061 12612514877899761156608273)
            ·
              refine ⟨9459386158424820867456205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12612514877899761156608273 9459386158424820867456205)
              ·
                refine ⟨3547269809409307825296077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9459386158424820867456205 3547269809409307825296077)
                ·
                  refine ⟨1330226178528490434486029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3547269809409307825296077 1330226178528490434486029)
                  ·
                    refine ⟨498834816948183912932261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1330226178528490434486029 498834816948183912932261)
                    ·
                      rfl

theorem cell22_1457216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_1457216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457216 prefixEnd_1457216 := by exact prefixLift 1457216
  have htrace : WordTrace (prefixWord ++ tailWord_1457216) baseStart_1457216 baseEnd_1457216 := by
    simpa [prefixWord, tailWord_1457216, baseEnd_1457216] using wordTrace_append hprefix tailTrace_1457216
  have hstable : (prefixWord ++ tailWord_1457216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457216).length < 2 ^ (prefixWord ++ tailWord_1457216).sum := by decide
  have hdescent : baseEnd_1457216 < baseStart_1457216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457261 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1457261 : Nat := 118140960795 + 1457261 * 2 ^ 59
def prefixEnd_1457261 : Nat := 4983230072969 + 3 ^ 40 * 1457261 * 2
def baseEnd_1457261 : Nat := 498850221367818795557123

theorem tailTrace_1457261 : CollatzResearch.WordTrace tailWord_1457261 prefixEnd_1457261 498850221367818795557123 := by
  unfold tailWord_1457261
  simp only [CollatzResearch.WordTrace]
  refine ⟨53150675173599752209531637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35433783449066501473021091 53150675173599752209531637)
  ·
    refine ⟨4982875797524976769643591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53150675173599752209531637 4982875797524976769643591)
    ·
      refine ⟨7474313696287465154465387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4982875797524976769643591 7474313696287465154465387)
      ·
        refine ⟨11211470544431197731698081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7474313696287465154465387 11211470544431197731698081)
        ·
          refine ⟨8408602908323398298773561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11211470544431197731698081 8408602908323398298773561)
          ·
            refine ⟨6306452181242548724080171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8408602908323398298773561 6306452181242548724080171)
            ·
              refine ⟨9459678271863823086120257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306452181242548724080171 9459678271863823086120257)
              ·
                refine ⟨7094758703897867314590193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9459678271863823086120257 7094758703897867314590193)
                ·
                  refine ⟨5321069027923400485942645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7094758703897867314590193 5321069027923400485942645)
                  ·
                    refine ⟨498850221367818795557123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5321069027923400485942645 498850221367818795557123)
                    ·
                      rfl

theorem cell22_1457261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1457261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457261 prefixEnd_1457261 := by exact prefixLift 1457261
  have htrace : WordTrace (prefixWord ++ tailWord_1457261) baseStart_1457261 baseEnd_1457261 := by
    simpa [prefixWord, tailWord_1457261, baseEnd_1457261] using wordTrace_append hprefix tailTrace_1457261
  have hstable : (prefixWord ++ tailWord_1457261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457261).length < 2 ^ (prefixWord ++ tailWord_1457261).sum := by decide
  have hdescent : baseEnd_1457261 < baseStart_1457261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457310 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1457310 : Nat := 118140960795 + 1457310 * 2 ^ 59
def prefixEnd_1457310 : Nat := 4983230072969 + 3 ^ 40 * 1457310 * 2
def baseEnd_1457310 : Nat := 498866995069199001081973

theorem tailTrace_1457310 : CollatzResearch.WordTrace tailWord_1457310 prefixEnd_1457310 498866995069199001081973 := by
  unfold tailWord_1457310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644057793802779197258173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35434974900281489052043589 6644057793802779197258173)
  ·
    refine ⟨2491521672676042198971815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6644057793802779197258173 2491521672676042198971815)
    ·
      refine ⟨3737282509014063298457723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491521672676042198971815 3737282509014063298457723)
      ·
        refine ⟨5605923763521094947686585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737282509014063298457723 5605923763521094947686585)
        ·
          refine ⟨4204442822640821210764939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605923763521094947686585 4204442822640821210764939)
          ·
            refine ⟨6306664233961231816147409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204442822640821210764939 6306664233961231816147409)
            ·
              refine ⟨4729998175470923862110557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6306664233961231816147409 4729998175470923862110557)
              ·
                refine ⟨1773749315801596448291459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4729998175470923862110557 1773749315801596448291459)
                ·
                  refine ⟨2660623973702394672437189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773749315801596448291459 2660623973702394672437189)
                  ·
                    refine ⟨498866995069199001081973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2660623973702394672437189 498866995069199001081973)
                    ·
                      rfl

theorem cell22_1457310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1457310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457310 prefixEnd_1457310 := by exact prefixLift 1457310
  have htrace : WordTrace (prefixWord ++ tailWord_1457310) baseStart_1457310 baseEnd_1457310 := by
    simpa [prefixWord, tailWord_1457310, baseEnd_1457310] using wordTrace_append hprefix tailTrace_1457310
  have hstable : (prefixWord ++ tailWord_1457310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457310).length < 2 ^ (prefixWord ++ tailWord_1457310).sum := by decide
  have hdescent : baseEnd_1457310 < baseStart_1457310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457325 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1457325 : Nat := 118140960795 + 1457325 * 2 ^ 59
def prefixEnd_1457325 : Nat := 4983230072969 + 3 ^ 40 * 1457325 * 2
def baseEnd_1457325 : Nat := 166290709958581320652309

theorem tailTrace_1457325 : CollatzResearch.WordTrace tailWord_1457325 prefixEnd_1457325 166290709958581320652309 := by
  unfold tailWord_1457325
  simp only [CollatzResearch.WordTrace]
  refine ⟨53153009445367891139861429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35435339630245260759907619 53153009445367891139861429)
  ·
    refine ⟨4983094635503239794362009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53153009445367891139861429 4983094635503239794362009)
    ·
      refine ⟨3737320976627429845771507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4983094635503239794362009 3737320976627429845771507)
      ·
        refine ⟨5605981464941144768657261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737320976627429845771507 5605981464941144768657261)
        ·
          refine ⟨2102243049352929288246473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5605981464941144768657261 2102243049352929288246473)
          ·
            refine ⟨1576682287014696966184855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2102243049352929288246473 1576682287014696966184855)
            ·
              refine ⟨2365023430522045449277283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576682287014696966184855 2365023430522045449277283)
              ·
                refine ⟨3547535145783068173915925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365023430522045449277283 3547535145783068173915925)
                ·
                  refine ⟨166290709958581320652309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3547535145783068173915925 166290709958581320652309)
                  ·
                    rfl

theorem cell22_1457325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1457325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457325 prefixEnd_1457325 := by exact prefixLift 1457325
  have htrace : WordTrace (prefixWord ++ tailWord_1457325) baseStart_1457325 baseEnd_1457325 := by
    simpa [prefixWord, tailWord_1457325, baseEnd_1457325] using wordTrace_append hprefix tailTrace_1457325
  have hstable : (prefixWord ++ tailWord_1457325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457325).length < 2 ^ (prefixWord ++ tailWord_1457325).sum := by decide
  have hdescent : baseEnd_1457325 < baseStart_1457325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457340 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1457340 : Nat := 118140960795 + 1457340 * 2 ^ 59
def prefixEnd_1457340 : Nat := 4983230072969 + 3 ^ 40 * 1457340 * 2
def baseEnd_1457340 : Nat := 498877264682288922831881

theorem tailTrace_1457340 : CollatzResearch.WordTrace tailWord_1457340 prefixEnd_1457340 498877264682288922831881 := by
  unfold tailWord_1457340
  simp only [CollatzResearch.WordTrace]
  refine ⟨26576778270156774350828737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35435704360209032467771649 26576778270156774350828737)
  ·
    refine ⟨19932583702617580763121553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26576778270156774350828737 19932583702617580763121553)
    ·
      refine ⟨14949437776963185572341165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19932583702617580763121553 14949437776963185572341165)
      ·
        refine ⟨5606039166361194589627937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14949437776963185572341165 5606039166361194589627937)
        ·
          refine ⟨4204529374770895942220953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5606039166361194589627937 4204529374770895942220953)
          ·
            refine ⟨3153397031078171956665715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204529374770895942220953 3153397031078171956665715)
            ·
              refine ⟨4730095546617257934998573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153397031078171956665715 4730095546617257934998573)
              ·
                refine ⟨1773785829981471725624465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4730095546617257934998573 1773785829981471725624465)
                ·
                  refine ⟨1330339372486103794218349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1773785829981471725624465 1330339372486103794218349)
                  ·
                    refine ⟨498877264682288922831881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1330339372486103794218349 498877264682288922831881)
                    ·
                      rfl

theorem cell22_1457340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1457340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457340 prefixEnd_1457340 := by exact prefixLift 1457340
  have htrace : WordTrace (prefixWord ++ tailWord_1457340) baseStart_1457340 baseEnd_1457340 := by
    simpa [prefixWord, tailWord_1457340, baseEnd_1457340] using wordTrace_append hprefix tailTrace_1457340
  have hstable : (prefixWord ++ tailWord_1457340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457340).length < 2 ^ (prefixWord ++ tailWord_1457340).sum := by decide
  have hdescent : baseEnd_1457340 < baseStart_1457340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457357 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1457357 : Nat := 118140960795 + 1457357 * 2 ^ 59
def prefixEnd_1457357 : Nat := 4983230072969 + 3 ^ 40 * 1457357 * 2
def baseEnd_1457357 : Nat := 498883084129706545156829

theorem tailTrace_1457357 : CollatzResearch.WordTrace tailWord_1457357 prefixEnd_1457357 498883084129706545156829 := by
  unfold tailWord_1457357
  simp only [CollatzResearch.WordTrace]
  refine ⟨53154176581251960605026325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35436117720834640403350883 53154176581251960605026325)
  ·
    refine ⟨2491602027246185653360609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53154176581251960605026325 2491602027246185653360609)
    ·
      refine ⟨1868701520434639240020457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2491602027246185653360609 1868701520434639240020457)
      ·
        refine ⟨1401526140325979430015343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1868701520434639240020457 1401526140325979430015343)
        ·
          refine ⟨2102289210488969145023015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401526140325979430015343 2102289210488969145023015)
          ·
            refine ⟨3153433815733453717534523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102289210488969145023015 3153433815733453717534523)
            ·
              refine ⟨4730150723600180576301785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153433815733453717534523 4730150723600180576301785)
              ·
                refine ⟨3547613042700135432226339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4730150723600180576301785 3547613042700135432226339)
                ·
                  refine ⟨5321419564050203148339509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547613042700135432226339 5321419564050203148339509)
                  ·
                    refine ⟨498883084129706545156829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5321419564050203148339509 498883084129706545156829)
                    ·
                      rfl

theorem cell22_1457357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1457357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457357 prefixEnd_1457357 := by exact prefixLift 1457357
  have htrace : WordTrace (prefixWord ++ tailWord_1457357) baseStart_1457357 baseEnd_1457357 := by
    simpa [prefixWord, tailWord_1457357, baseEnd_1457357] using wordTrace_append hprefix tailTrace_1457357
  have hstable : (prefixWord ++ tailWord_1457357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457357).length < 2 ^ (prefixWord ++ tailWord_1457357).sum := by decide
  have hdescent : baseEnd_1457357 < baseStart_1457357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457443 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 6]
def baseStart_1457443 : Nat := 118140960795 + 1457443 * 2 ^ 59
def prefixEnd_1457443 : Nat := 4983230072969 + 3 ^ 40 * 1457443 * 2
def baseEnd_1457443 : Nat := 166304174562410329168855

theorem tailTrace_1457443 : CollatzResearch.WordTrace tailWord_1457443 prefixEnd_1457443 166304174562410329168855 := by
  unfold tailWord_1457443
  simp only [CollatzResearch.WordTrace]
  refine ⟨53157313258940397292656983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35438208839293598195104655 53157313258940397292656983)
  ·
    refine ⟨79735969888410595938985475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53157313258940397292656983 79735969888410595938985475)
    ·
      refine ⟨119603954832615893908478213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79735969888410595938985475 119603954832615893908478213)
      ·
        refine ⟨22425741531115480107839665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119603954832615893908478213 22425741531115480107839665)
        ·
          refine ⟨16819306148336610080879749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22425741531115480107839665 16819306148336610080879749)
          ·
            refine ⟨3153619902813114390164953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16819306148336610080879749 3153619902813114390164953)
            ·
              refine ⟨2365214927109835792623715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153619902813114390164953 2365214927109835792623715)
              ·
                refine ⟨3547822390664753688935573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365214927109835792623715 3547822390664753688935573)
                ·
                  refine ⟨166304174562410329168855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3547822390664753688935573 166304174562410329168855)
                  ·
                    rfl

theorem cell22_1457443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 6].length) (baseStart_1457443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457443 prefixEnd_1457443 := by exact prefixLift 1457443
  have htrace : WordTrace (prefixWord ++ tailWord_1457443) baseStart_1457443 baseEnd_1457443 := by
    simpa [prefixWord, tailWord_1457443, baseEnd_1457443] using wordTrace_append hprefix tailTrace_1457443
  have hstable : (prefixWord ++ tailWord_1457443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457443).length < 2 ^ (prefixWord ++ tailWord_1457443).sum := by decide
  have hdescent : baseEnd_1457443 < baseStart_1457443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457456 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_1457456 : Nat := 118140960795 + 1457456 * 2 ^ 59
def prefixEnd_1457456 : Nat := 4983230072969 + 3 ^ 40 * 1457456 * 2
def baseEnd_1457456 : Nat := 498916973852903286931525

theorem tailTrace_1457456 : CollatzResearch.WordTrace tailWord_1457456 prefixEnd_1457456 498916973852903286931525 := by
  unfold tailWord_1457456
  simp only [CollatzResearch.WordTrace]
  refine ⟨26578893703946650256440111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35438524938595533675253481 26578893703946650256440111)
  ·
    refine ⟨39868340555919975384660167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26578893703946650256440111 39868340555919975384660167)
    ·
      refine ⟨59802510833879963076990251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39868340555919975384660167 59802510833879963076990251)
      ·
        refine ⟨89703766250819944615485377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59802510833879963076990251 89703766250819944615485377)
        ·
          refine ⟨67277824688114958461614033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89703766250819944615485377 67277824688114958461614033)
          ·
            refine ⟨50458368516086218846210525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67277824688114958461614033 50458368516086218846210525)
            ·
              refine ⟨18921888193532332067328947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50458368516086218846210525 18921888193532332067328947)
              ·
                refine ⟨28382832290298498100993421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18921888193532332067328947 28382832290298498100993421)
                ·
                  refine ⟨10643562108861936787872533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28382832290298498100993421 10643562108861936787872533)
                  ·
                    refine ⟨498916973852903286931525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10643562108861936787872533 498916973852903286931525)
                    ·
                      rfl

theorem cell22_1457456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_1457456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457456 prefixEnd_1457456 := by exact prefixLift 1457456
  have htrace : WordTrace (prefixWord ++ tailWord_1457456) baseStart_1457456 baseEnd_1457456 := by
    simpa [prefixWord, tailWord_1457456, baseEnd_1457456] using wordTrace_append hprefix tailTrace_1457456
  have hstable : (prefixWord ++ tailWord_1457456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457456).length < 2 ^ (prefixWord ++ tailWord_1457456).sum := by decide
  have hdescent : baseEnd_1457456 < baseStart_1457456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457548 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1457548 : Nat := 118140960795 + 1457548 * 2 ^ 59
def prefixEnd_1457548 : Nat := 4983230072969 + 3 ^ 40 * 1457548 * 2
def baseEnd_1457548 : Nat := 498948467333045713631243

theorem tailTrace_1457548 : CollatzResearch.WordTrace tailWord_1457548 prefixEnd_1457548 498948467333045713631243 := by
  unfold tailWord_1457548
  simp only [CollatzResearch.WordTrace]
  refine ⟨26580571461780000112614649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35440761949040000150152865 26580571461780000112614649)
  ·
    refine ⟨19935428596335000084460987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26580571461780000112614649 19935428596335000084460987)
    ·
      refine ⟨29903142894502500126691481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19935428596335000084460987 29903142894502500126691481)
      ·
        refine ⟨22427357170876875095018611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29903142894502500126691481 22427357170876875095018611)
        ·
          refine ⟨33641035756315312642527917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22427357170876875095018611 33641035756315312642527917)
          ·
            refine ⟨12615388408618242240947969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33641035756315312642527917 12615388408618242240947969)
            ·
              refine ⟨9461541306463681680710977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12615388408618242240947969 9461541306463681680710977)
              ·
                refine ⟨7096155979847761260533233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9461541306463681680710977 7096155979847761260533233)
                ·
                  refine ⟨5322116984885820945399925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7096155979847761260533233 5322116984885820945399925)
                  ·
                    refine ⟨498948467333045713631243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5322116984885820945399925 498948467333045713631243)
                    ·
                      rfl

theorem cell22_1457548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1457548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457548 prefixEnd_1457548 := by exact prefixLift 1457548
  have htrace : WordTrace (prefixWord ++ tailWord_1457548) baseStart_1457548 baseEnd_1457548 := by
    simpa [prefixWord, tailWord_1457548, baseEnd_1457548] using wordTrace_append hprefix tailTrace_1457548
  have hstable : (prefixWord ++ tailWord_1457548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457548).length < 2 ^ (prefixWord ++ tailWord_1457548).sum := by decide
  have hdescent : baseEnd_1457548 < baseStart_1457548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457565 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1457565 : Nat := 118140960795 + 1457565 * 2 ^ 59
def prefixEnd_1457565 : Nat := 4983230072969 + 3 ^ 40 * 1457565 * 2
def baseEnd_1457565 : Nat := 498954286780463335956191

theorem tailTrace_1457565 : CollatzResearch.WordTrace tailWord_1457565 prefixEnd_1457565 498954286780463335956191 := by
  unfold tailWord_1457565
  simp only [CollatzResearch.WordTrace]
  refine ⟨53161762964498412128598149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35441175309665608085732099 53161762964498412128598149)
  ·
    refine ⟨9967830555843452274112153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53161762964498412128598149 9967830555843452274112153)
    ·
      refine ⟨7475872916882589205584115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9967830555843452274112153 7475872916882589205584115)
      ·
        refine ⟨11213809375323883808376173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475872916882589205584115 11213809375323883808376173)
        ·
          refine ⟨4205178515746456428141065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11213809375323883808376173 4205178515746456428141065)
          ·
            refine ⟨3153883886809842321105799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4205178515746456428141065 3153883886809842321105799)
            ·
              refine ⟨4730825830214763481658699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153883886809842321105799 4730825830214763481658699)
              ·
                refine ⟨7096238745322145222488049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4730825830214763481658699 7096238745322145222488049)
                ·
                  refine ⟨5322179058991608916866037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7096238745322145222488049 5322179058991608916866037)
                  ·
                    refine ⟨498954286780463335956191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5322179058991608916866037 498954286780463335956191)
                    ·
                      rfl

theorem cell22_1457565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1457565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457565 prefixEnd_1457565 := by exact prefixLift 1457565
  have htrace : WordTrace (prefixWord ++ tailWord_1457565) baseStart_1457565 baseEnd_1457565 := by
    simpa [prefixWord, tailWord_1457565, baseEnd_1457565] using wordTrace_append hprefix tailTrace_1457565
  have hstable : (prefixWord ++ tailWord_1457565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457565).length < 2 ^ (prefixWord ++ tailWord_1457565).sum := by decide
  have hdescent : baseEnd_1457565 < baseStart_1457565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457612 : List Nat := [2, 2, 1, 4, 2, 1, 2, 4, 4]
def baseStart_1457612 : Nat := 118140960795 + 1457612 * 2 ^ 59
def prefixEnd_1457612 : Nat := 4983230072969 + 3 ^ 40 * 1457612 * 2
def baseEnd_1457612 : Nat := 166323458613656960010349

theorem tailTrace_1457612 : CollatzResearch.WordTrace tailWord_1457612 prefixEnd_1457612 166323458613656960010349 := by
  unfold tailWord_1457612
  simp only [CollatzResearch.WordTrace]
  refine ⟨26581738597664069577779545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35442318130218759437039393 26581738597664069577779545)
  ·
    refine ⟨19936303948248052183334659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26581738597664069577779545 19936303948248052183334659)
    ·
      refine ⟨29904455922372078275001989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19936303948248052183334659 29904455922372078275001989)
      ·
        refine ⟨5607085485444764676562873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29904455922372078275001989 5607085485444764676562873)
        ·
          refine ⟨4205314114083573507422155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5607085485444764676562873 4205314114083573507422155)
          ·
            refine ⟨6307971171125360261133233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205314114083573507422155 6307971171125360261133233)
            ·
              refine ⟨4730978378344020195849925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6307971171125360261133233 4730978378344020195849925)
              ·
                refine ⟨887058445939503786721861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4730978378344020195849925 887058445939503786721861)
                ·
                  refine ⟨166323458613656960010349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 887058445939503786721861 166323458613656960010349)
                  ·
                    rfl

theorem cell22_1457612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_1457612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457612 prefixEnd_1457612 := by exact prefixLift 1457612
  have htrace : WordTrace (prefixWord ++ tailWord_1457612) baseStart_1457612 baseEnd_1457612 := by
    simpa [prefixWord, tailWord_1457612, baseEnd_1457612] using wordTrace_append hprefix tailTrace_1457612
  have hstable : (prefixWord ++ tailWord_1457612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457612).length < 2 ^ (prefixWord ++ tailWord_1457612).sum := by decide
  have hdescent : baseEnd_1457612 < baseStart_1457612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457672 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 3, 3]
def baseStart_1457672 : Nat := 118140960795 + 1457672 * 2 ^ 59
def prefixEnd_1457672 : Nat := 4983230072969 + 3 ^ 40 * 1457672 * 2
def baseEnd_1457672 : Nat := 498990915067150723530863

theorem tailTrace_1457672 : CollatzResearch.WordTrace tailWord_1457672 prefixEnd_1457672 498990915067150723530863 := by
  unfold tailWord_1457672
  simp only [CollatzResearch.WordTrace]
  refine ⟨26582832787555384701371635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35443777050073846268495513 26582832787555384701371635)
  ·
    refine ⟨39874249181333077052057453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26582832787555384701371635 39874249181333077052057453)
    ·
      refine ⟨14952843442999903894521545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39874249181333077052057453 14952843442999903894521545)
      ·
        refine ⟨11214632582249927920891159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14952843442999903894521545 11214632582249927920891159)
        ·
          refine ⟨16821948873374891881336739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11214632582249927920891159 16821948873374891881336739)
          ·
            refine ⟨25232923310062337822005109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16821948873374891881336739 25232923310062337822005109)
            ·
              refine ⟨2365586560318344170812979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25232923310062337822005109 2365586560318344170812979)
              ·
                refine ⟨3548379840477516256219469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365586560318344170812979 3548379840477516256219469)
                ·
                  refine ⟨1330642440179068596082301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3548379840477516256219469 1330642440179068596082301)
                  ·
                    refine ⟨498990915067150723530863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1330642440179068596082301 498990915067150723530863)
                    ·
                      rfl

theorem cell22_1457672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_1457672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457672 prefixEnd_1457672 := by exact prefixLift 1457672
  have htrace : WordTrace (prefixWord ++ tailWord_1457672) baseStart_1457672 baseEnd_1457672 := by
    simpa [prefixWord, tailWord_1457672, baseEnd_1457672] using wordTrace_append hprefix tailTrace_1457672
  have hstable : (prefixWord ++ tailWord_1457672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457672).length < 2 ^ (prefixWord ++ tailWord_1457672).sum := by decide
  have hdescent : baseEnd_1457672 < baseStart_1457672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457678 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_1457678 : Nat := 118140960795 + 1457678 * 2 ^ 59
def prefixEnd_1457678 : Nat := 4983230072969 + 3 ^ 40 * 1457678 * 2
def baseEnd_1457678 : Nat := 498992968989768707880845

theorem tailTrace_1457678 : CollatzResearch.WordTrace tailWord_1457678 prefixEnd_1457678 498992968989768707880845 := by
  unfold tailWord_1457678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6645735551636129053432711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35443922942059354951641125 6645735551636129053432711)
  ·
    refine ⟨9968603327454193580149067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6645735551636129053432711 9968603327454193580149067)
    ·
      refine ⟨14952904991181290370223601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9968603327454193580149067 14952904991181290370223601)
      ·
        refine ⟨11214678743385967777667701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14952904991181290370223601 11214678743385967777667701)
        ·
          refine ⟨1051376132192434479156347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11214678743385967777667701 1051376132192434479156347)
          ·
            refine ⟨1577064198288651718734521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051376132192434479156347 1577064198288651718734521)
            ·
              refine ⟨1182798148716488789050891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577064198288651718734521 1182798148716488789050891)
              ·
                refine ⟨1774197223074733183576337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182798148716488789050891 1774197223074733183576337)
                ·
                  refine ⟨1330647917306049887682253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1774197223074733183576337 1330647917306049887682253)
                  ·
                    refine ⟨498992968989768707880845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1330647917306049887682253 498992968989768707880845)
                    ·
                      rfl

theorem cell22_1457678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_1457678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457678 prefixEnd_1457678 := by exact prefixLift 1457678
  have htrace : WordTrace (prefixWord ++ tailWord_1457678) baseStart_1457678 baseEnd_1457678 := by
    simpa [prefixWord, tailWord_1457678, baseEnd_1457678] using wordTrace_append hprefix tailTrace_1457678
  have hstable : (prefixWord ++ tailWord_1457678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457678).length < 2 ^ (prefixWord ++ tailWord_1457678).sum := by decide
  have hdescent : baseEnd_1457678 < baseStart_1457678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457764 : List Nat := [2, 3, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1457764 : Nat := 118140960795 + 1457764 * 2 ^ 59
def prefixEnd_1457764 : Nat := 4983230072969 + 3 ^ 40 * 1457764 * 2
def baseEnd_1457764 : Nat := 166340802849097716743527

theorem tailTrace_1457764 : CollatzResearch.WordTrace tailWord_1457764 prefixEnd_1457764 166340802849097716743527 := by
  unfold tailWord_1457764
  simp only [CollatzResearch.WordTrace]
  refine ⟨26584510545388734557546173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35446014060518312743394897 26584510545388734557546173)
  ·
    refine ⟨9969191454520775459079815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26584510545388734557546173 9969191454520775459079815)
    ·
      refine ⟨14953787181781163188619723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9969191454520775459079815 14953787181781163188619723)
      ·
        refine ⟨22430680772671744782929585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14953787181781163188619723 22430680772671744782929585)
        ·
          refine ⟨16823010579503808587197189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22430680772671744782929585 16823010579503808587197189)
          ·
            refine ⟨3154314483656964110099473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16823010579503808587197189 3154314483656964110099473)
            ·
              refine ⟨2365735862742723082574605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3154314483656964110099473 2365735862742723082574605)
              ·
                refine ⟨887150948528521155965477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365735862742723082574605 887150948528521155965477)
                ·
                  refine ⟨166340802849097716743527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 887150948528521155965477 166340802849097716743527)
                  ·
                    rfl

theorem cell22_1457764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1457764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457764 prefixEnd_1457764 := by exact prefixLift 1457764
  have htrace : WordTrace (prefixWord ++ tailWord_1457764) baseStart_1457764 baseEnd_1457764 := by
    simpa [prefixWord, tailWord_1457764, baseEnd_1457764] using wordTrace_append hprefix tailTrace_1457764
  have hstable : (prefixWord ++ tailWord_1457764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457764).length < 2 ^ (prefixWord ++ tailWord_1457764).sum := by decide
  have hdescent : baseEnd_1457764 < baseStart_1457764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457796 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_1457796 : Nat := 118140960795 + 1457796 * 2 ^ 59
def prefixEnd_1457796 : Nat := 4983230072969 + 3 ^ 40 * 1457796 * 2
def baseEnd_1457796 : Nat := 499033362801255733430483

theorem tailTrace_1457796 : CollatzResearch.WordTrace tailWord_1457796 prefixEnd_1457796 499033362801255733430483 := by
  unfold tailWord_1457796
  simp only [CollatzResearch.WordTrace]
  refine ⟨26585094113330769290128621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35446792151107692386838161 26585094113330769290128621)
  ·
    refine ⟨9969410292499038483798233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26585094113330769290128621 9969410292499038483798233)
    ·
      refine ⟨7477057719374278862848675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9969410292499038483798233 7477057719374278862848675)
      ·
        refine ⟨11215586579061418294273013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477057719374278862848675 11215586579061418294273013)
        ·
          refine ⟨1051461241787007965088095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11215586579061418294273013 1051461241787007965088095)
          ·
            refine ⟨1577191862680511947632143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051461241787007965088095 1577191862680511947632143)
            ·
              refine ⟨2365787794020767921448215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577191862680511947632143 2365787794020767921448215)
              ·
                refine ⟨3548681691031151882172323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365787794020767921448215 3548681691031151882172323)
                ·
                  refine ⟨5323022536546727823258485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548681691031151882172323 5323022536546727823258485)
                  ·
                    refine ⟨499033362801255733430483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5323022536546727823258485 499033362801255733430483)
                    ·
                      rfl

theorem cell22_1457796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_1457796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457796 prefixEnd_1457796 := by exact prefixLift 1457796
  have htrace : WordTrace (prefixWord ++ tailWord_1457796) baseStart_1457796 baseEnd_1457796 := by
    simpa [prefixWord, tailWord_1457796, baseEnd_1457796] using wordTrace_append hprefix tailTrace_1457796
  have hstable : (prefixWord ++ tailWord_1457796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457796).length < 2 ^ (prefixWord ++ tailWord_1457796).sum := by decide
  have hdescent : baseEnd_1457796 < baseStart_1457796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457826 : List Nat := [3, 3, 1, 4, 2, 1, 8]
def baseStart_1457826 : Nat := 118140960795 + 1457826 * 2 ^ 59
def prefixEnd_1457826 : Nat := 4983230072969 + 3 ^ 40 * 1457826 * 2
def baseEnd_1457826 : Nat := 18483097496827616858533

theorem tailTrace_1457826 : CollatzResearch.WordTrace tailWord_1457826 prefixEnd_1457826 18483097496827616858533 := by
  unfold tailWord_1457826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13292820604138213425962333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35447521611035235802566221 13292820604138213425962333)
  ·
    refine ⟨4984807726551830034735875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13292820604138213425962333 4984807726551830034735875)
    ·
      refine ⟨7477211589827745052103813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4984807726551830034735875 7477211589827745052103813)
      ·
        refine ⟨1401977173092702197269465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7477211589827745052103813 1401977173092702197269465)
        ·
          refine ⟨1051482879819526647952099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1401977173092702197269465 1051482879819526647952099)
          ·
            refine ⟨1577224319729289971928149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051482879819526647952099 1577224319729289971928149)
            ·
              refine ⟨18483097496827616858533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1577224319729289971928149 18483097496827616858533)
              ·
                rfl

theorem cell22_1457826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 8].length) (baseStart_1457826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457826 prefixEnd_1457826 := by exact prefixLift 1457826
  have htrace : WordTrace (prefixWord ++ tailWord_1457826) baseStart_1457826 baseEnd_1457826 := by
    simpa [prefixWord, tailWord_1457826, baseEnd_1457826] using wordTrace_append hprefix tailTrace_1457826
  have hstable : (prefixWord ++ tailWord_1457826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457826).length < 2 ^ (prefixWord ++ tailWord_1457826).sum := by decide
  have hdescent : baseEnd_1457826 < baseStart_1457826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457837 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 7]
def baseStart_1457837 : Nat := 118140960795 + 1457837 * 2 ^ 59
def prefixEnd_1457837 : Nat := 4983230072969 + 3 ^ 40 * 1457837 * 2
def baseEnd_1457837 : Nat := 166349132646381764385119

theorem tailTrace_1457837 : CollatzResearch.WordTrace tailWord_1457837 prefixEnd_1457837 166349132646381764385119 := by
  unfold tailWord_1457837
  simp only [CollatzResearch.WordTrace]
  refine ⟨53171683619513002582499765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35447789079675335054999843 53171683619513002582499765)
  ·
    refine ⟨4984845339329343992109353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53171683619513002582499765 4984845339329343992109353)
    ·
      refine ⟨3738634004497007994082015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4984845339329343992109353 3738634004497007994082015)
      ·
        refine ⟨5607951006745511991123023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3738634004497007994082015 5607951006745511991123023)
        ·
          refine ⟨8411926510118267986684535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607951006745511991123023 8411926510118267986684535)
          ·
            refine ⟨12617889765177401980026803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411926510118267986684535 12617889765177401980026803)
            ·
              refine ⟨18926834647766102970040205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12617889765177401980026803 18926834647766102970040205)
              ·
                refine ⟨7097562992912288613765077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18926834647766102970040205 7097562992912288613765077)
                ·
                  refine ⟨166349132646381764385119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7097562992912288613765077 166349132646381764385119)
                  ·
                    rfl

theorem cell22_1457837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_1457837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457837 prefixEnd_1457837 := by exact prefixLift 1457837
  have htrace : WordTrace (prefixWord ++ tailWord_1457837) baseStart_1457837 baseEnd_1457837 := by
    simpa [prefixWord, tailWord_1457837, baseEnd_1457837] using wordTrace_append hprefix tailTrace_1457837
  have hstable : (prefixWord ++ tailWord_1457837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457837).length < 2 ^ (prefixWord ++ tailWord_1457837).sum := by decide
  have hdescent : baseEnd_1457837 < baseStart_1457837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457854 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1457854 : Nat := 118140960795 + 1457854 * 2 ^ 59
def prefixEnd_1457854 : Nat := 4983230072969 + 3 ^ 40 * 1457854 * 2
def baseEnd_1457854 : Nat := 166351072462187638493435

theorem tailTrace_1457854 : CollatzResearch.WordTrace tailWord_1457854 prefixEnd_1457854 166351072462187638493435 := by
  unfold tailWord_1457854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6646537957556426810733577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35448202440300942990579077 6646537957556426810733577)
  ·
    refine ⟨4984903468167320108050183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6646537957556426810733577 4984903468167320108050183)
    ·
      refine ⟨7477355202250980162075275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4984903468167320108050183 7477355202250980162075275)
      ·
        refine ⟨11216032803376470243112913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477355202250980162075275 11216032803376470243112913)
        ·
          refine ⟨8412024602532352682334685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11216032803376470243112913 8412024602532352682334685)
          ·
            refine ⟨3154509225949632255875507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8412024602532352682334685 3154509225949632255875507)
            ·
              refine ⟨4731763838924448383813261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154509225949632255875507 4731763838924448383813261)
              ·
                refine ⟨1774411439596668143929973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4731763838924448383813261 1774411439596668143929973)
                ·
                  refine ⟨166351072462187638493435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1774411439596668143929973 166351072462187638493435)
                  ·
                    rfl

theorem cell22_1457854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1457854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457854 prefixEnd_1457854 := by exact prefixLift 1457854
  have htrace : WordTrace (prefixWord ++ tailWord_1457854) baseStart_1457854 baseEnd_1457854 := by
    simpa [prefixWord, tailWord_1457854, baseEnd_1457854] using wordTrace_append hprefix tailTrace_1457854
  have hstable : (prefixWord ++ tailWord_1457854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457854).length < 2 ^ (prefixWord ++ tailWord_1457854).sum := by decide
  have hdescent : baseEnd_1457854 < baseStart_1457854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457926 : List Nat := [6, 2, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1457926 : Nat := 118140960795 + 1457926 * 2 ^ 59
def prefixEnd_1457926 : Nat := 4983230072969 + 3 ^ 40 * 1457926 * 2
def baseEnd_1457926 : Nat := 499077864457978727680085

theorem tailTrace_1457926 : CollatzResearch.WordTrace tailWord_1457926 prefixEnd_1457926 499077864457978727680085 := by
  unfold tailWord_1457926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661716553630955336952801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35449953144127047188326421 1661716553630955336952801)
  ·
    refine ⟨1246287415223216502714601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1661716553630955336952801 1246287415223216502714601)
    ·
      refine ⟨934715561417412377035951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1246287415223216502714601 934715561417412377035951)
      ·
        refine ⟨1402073342126118565553927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934715561417412377035951 1402073342126118565553927)
        ·
          refine ⟨2103110013189177848330891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402073342126118565553927 2103110013189177848330891)
          ·
            refine ⟨3154665019783766772496337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103110013189177848330891 3154665019783766772496337)
            ·
              refine ⟨2365998764837825079372253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3154665019783766772496337 2365998764837825079372253)
              ·
                refine ⟨887249536814184404764595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365998764837825079372253 887249536814184404764595)
                ·
                  refine ⟨1330874305221276607146893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887249536814184404764595 1330874305221276607146893)
                  ·
                    refine ⟨499077864457978727680085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1330874305221276607146893 499077864457978727680085)
                    ·
                      rfl

theorem cell22_1457926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1457926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1457926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1457926 prefixEnd_1457926 := by exact prefixLift 1457926
  have htrace : WordTrace (prefixWord ++ tailWord_1457926) baseStart_1457926 baseEnd_1457926 := by
    simpa [prefixWord, tailWord_1457926, baseEnd_1457926] using wordTrace_append hprefix tailTrace_1457926
  have hstable : (prefixWord ++ tailWord_1457926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457926).length < 2 ^ (prefixWord ++ tailWord_1457926).sum := by decide
  have hdescent : baseEnd_1457926 < baseStart_1457926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458068 : List Nat := [2, 4, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1458068 : Nat := 118140960795 + 1458068 * 2 ^ 59
def prefixEnd_1458068 : Nat := 4983230072969 + 3 ^ 40 * 1458068 * 2
def baseEnd_1458068 : Nat := 166375491319979230209883

theorem tailTrace_1458068 : CollatzResearch.WordTrace tailWord_1458068 prefixEnd_1458068 166375491319979230209883 := by
  unfold tailWord_1458068
  simp only [CollatzResearch.WordTrace]
  refine ⟨26590054440838064517079429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35453405921117419356105905 26590054440838064517079429)
  ·
    refine ⟨4985635207657137096952393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26590054440838064517079429 4985635207657137096952393)
    ·
      refine ⟨3739226405742852822714295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4985635207657137096952393 3739226405742852822714295)
      ·
        refine ⟨5608839608614279234071443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739226405742852822714295 5608839608614279234071443)
        ·
          refine ⟨8413259412921418851107165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608839608614279234071443 8413259412921418851107165)
          ·
            refine ⟨3154972279845532069165187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8413259412921418851107165 3154972279845532069165187)
            ·
              refine ⟨4732458419768298103747781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154972279845532069165187 4732458419768298103747781)
              ·
                refine ⟨887335953706555894452709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4732458419768298103747781 887335953706555894452709)
                ·
                  refine ⟨166375491319979230209883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 887335953706555894452709 166375491319979230209883)
                  ·
                    rfl

theorem cell22_1458068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1458068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458068 prefixEnd_1458068 := by exact prefixLift 1458068
  have htrace : WordTrace (prefixWord ++ tailWord_1458068) baseStart_1458068 baseEnd_1458068 := by
    simpa [prefixWord, tailWord_1458068, baseEnd_1458068] using wordTrace_append hprefix tailTrace_1458068
  have hstable : (prefixWord ++ tailWord_1458068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458068).length < 2 ^ (prefixWord ++ tailWord_1458068).sum := by decide
  have hdescent : baseEnd_1458068 < baseStart_1458068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458128 : List Nat := [2, 1, 1, 1, 1, 2, 6, 4, 1, 3]
def baseStart_1458128 : Nat := 118140960795 + 1458128 * 2 ^ 59
def prefixEnd_1458128 : Nat := 4983230072969 + 3 ^ 40 * 1458128 * 2
def baseEnd_1458128 : Nat := 499147013186117534129465

theorem tailTrace_1458128 : CollatzResearch.WordTrace tailWord_1458128 prefixEnd_1458128 499147013186117534129465 := by
  unfold tailWord_1458128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26591148630729379640671519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35454864840972506187562025 26591148630729379640671519)
  ·
    refine ⟨39886722946094069461007279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26591148630729379640671519 39886722946094069461007279)
    ·
      refine ⟨59830084419141104191510919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39886722946094069461007279 59830084419141104191510919)
      ·
        refine ⟨89745126628711656287266379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59830084419141104191510919 89745126628711656287266379)
        ·
          refine ⟨134617689943067484430899569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89745126628711656287266379 134617689943067484430899569)
          ·
            refine ⟨100963267457300613323174677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134617689943067484430899569 100963267457300613323174677)
            ·
              refine ⟨4732653162060966249523813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100963267457300613323174677 4732653162060966249523813)
              ·
                refine ⟨887372467886431171785715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4732653162060966249523813 887372467886431171785715)
                ·
                  refine ⟨1331058701829646757678573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887372467886431171785715 1331058701829646757678573)
                  ·
                    refine ⟨499147013186117534129465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1331058701829646757678573 499147013186117534129465)
                    ·
                      rfl

theorem cell22_1458128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 3].length) (baseStart_1458128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458128 prefixEnd_1458128 := by exact prefixLift 1458128
  have htrace : WordTrace (prefixWord ++ tailWord_1458128) baseStart_1458128 baseEnd_1458128 := by
    simpa [prefixWord, tailWord_1458128, baseEnd_1458128] using wordTrace_append hprefix tailTrace_1458128
  have hstable : (prefixWord ++ tailWord_1458128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458128).length < 2 ^ (prefixWord ++ tailWord_1458128).sum := by decide
  have hdescent : baseEnd_1458128 < baseStart_1458128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458171 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 1, 4]
def baseStart_1458171 : Nat := 118140960795 + 1458171 * 2 ^ 59
def prefixEnd_1458171 : Nat := 4983230072969 + 3 ^ 40 * 1458171 * 2
def baseEnd_1458171 : Nat := 499161732964879755304333

theorem tailTrace_1458171 : CollatzResearch.WordTrace tailWord_1458171 prefixEnd_1458171 499161732964879755304333 := by
  unfold tailWord_1458171
  simp only [CollatzResearch.WordTrace]
  refine ⟨53183865600302977625158367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35455910400201985083438911 53183865600302977625158367)
  ·
    refine ⟨79775798400454466437737551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53183865600302977625158367 79775798400454466437737551)
    ·
      refine ⟨119663697600681699656606327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79775798400454466437737551 119663697600681699656606327)
      ·
        refine ⟨179495546401022549484909491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119663697600681699656606327 179495546401022549484909491)
        ·
          refine ⟨269243319601533824227364237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179495546401022549484909491 269243319601533824227364237)
          ·
            refine ⟨100966244850575184085261589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269243319601533824227364237 100966244850575184085261589)
            ·
              refine ⟨4732792727370711753996637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100966244850575184085261589 4732792727370711753996637)
              ·
                refine ⟨1774797272764016907748739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4732792727370711753996637 1774797272764016907748739)
                ·
                  refine ⟨2662195909146025361623109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774797272764016907748739 2662195909146025361623109)
                  ·
                    refine ⟨499161732964879755304333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662195909146025361623109 499161732964879755304333)
                    ·
                      rfl

theorem cell22_1458171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 4].length) (baseStart_1458171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458171 prefixEnd_1458171 := by exact prefixLift 1458171
  have htrace : WordTrace (prefixWord ++ tailWord_1458171) baseStart_1458171 baseEnd_1458171 := by
    simpa [prefixWord, tailWord_1458171, baseEnd_1458171] using wordTrace_append hprefix tailTrace_1458171
  have hstable : (prefixWord ++ tailWord_1458171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458171).length < 2 ^ (prefixWord ++ tailWord_1458171).sum := by decide
  have hdescent : baseEnd_1458171 < baseStart_1458171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458205 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_1458205 : Nat := 118140960795 + 1458205 * 2 ^ 59
def prefixEnd_1458205 : Nat := 4983230072969 + 3 ^ 40 * 1458205 * 2
def baseEnd_1458205 : Nat := 499173371859714999954229

theorem tailTrace_1458205 : CollatzResearch.WordTrace tailWord_1458205 prefixEnd_1458205 499173371859714999954229 := by
  unfold tailWord_1458205
  simp only [CollatzResearch.WordTrace]
  refine ⟨53185105682179801431896069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35456737121453200954597379 53185105682179801431896069)
  ·
    refine ⟨9972207315408712768480513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53185105682179801431896069 9972207315408712768480513)
    ·
      refine ⟨7479155486556534576360385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9972207315408712768480513 7479155486556534576360385)
      ·
        refine ⟨5609366614917400932270289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7479155486556534576360385 5609366614917400932270289)
        ·
          refine ⟨4207024961188050699202717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5609366614917400932270289 4207024961188050699202717)
          ·
            refine ⟨1577634360445519012201019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4207024961188050699202717 1577634360445519012201019)
            ·
              refine ⟨2366451540668278518301529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577634360445519012201019 2366451540668278518301529)
              ·
                refine ⟨1774838655501208888726147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2366451540668278518301529 1774838655501208888726147)
                ·
                  refine ⟨2662257983251813333089221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774838655501208888726147 2662257983251813333089221)
                  ·
                    refine ⟨499173371859714999954229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662257983251813333089221 499173371859714999954229)
                    ·
                      rfl

theorem cell22_1458205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_1458205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458205 prefixEnd_1458205 := by exact prefixLift 1458205
  have htrace : WordTrace (prefixWord ++ tailWord_1458205) baseStart_1458205 baseEnd_1458205 := by
    simpa [prefixWord, tailWord_1458205, baseEnd_1458205] using wordTrace_append hprefix tailTrace_1458205
  have hstable : (prefixWord ++ tailWord_1458205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458205).length < 2 ^ (prefixWord ++ tailWord_1458205).sum := by decide
  have hdescent : baseEnd_1458205 < baseStart_1458205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458218 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1458218 : Nat := 118140960795 + 1458218 * 2 ^ 59
def prefixEnd_1458218 : Nat := 4983230072969 + 3 ^ 40 * 1458218 * 2
def baseEnd_1458218 : Nat := 499177822025387299379189

theorem tailTrace_1458218 : CollatzResearch.WordTrace tailWord_1458218 prefixEnd_1458218 499177822025387299379189 := by
  unfold tailWord_1458218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13296394957783176163029827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35457053220755136434746205 13296394957783176163029827)
  ·
    refine ⟨19944592436674764244544741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13296394957783176163029827 19944592436674764244544741)
    ·
      refine ⟨3739611081876518295852139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19944592436674764244544741 3739611081876518295852139)
      ·
        refine ⟨5609416622814777443778209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739611081876518295852139 5609416622814777443778209)
        ·
          refine ⟨4207062467111083082833657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5609416622814777443778209 4207062467111083082833657)
          ·
            refine ⟨3155296850333312312125243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4207062467111083082833657 3155296850333312312125243)
            ·
              refine ⟨4732945275499968468187865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155296850333312312125243 4732945275499968468187865)
              ·
                refine ⟨3549708956624976351140899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732945275499968468187865 3549708956624976351140899)
                ·
                  refine ⟨5324563434937464526711349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549708956624976351140899 5324563434937464526711349)
                  ·
                    refine ⟨499177822025387299379189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5324563434937464526711349 499177822025387299379189)
                    ·
                      rfl

theorem cell22_1458218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1458218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458218 prefixEnd_1458218 := by exact prefixLift 1458218
  have htrace : WordTrace (prefixWord ++ tailWord_1458218) baseStart_1458218 baseEnd_1458218 := by
    simpa [prefixWord, tailWord_1458218, baseEnd_1458218] using wordTrace_append hprefix tailTrace_1458218
  have hstable : (prefixWord ++ tailWord_1458218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458218).length < 2 ^ (prefixWord ++ tailWord_1458218).sum := by decide
  have hdescent : baseEnd_1458218 < baseStart_1458218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458462 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_1458462 : Nat := 118140960795 + 1458462 * 2 ^ 59
def prefixEnd_1458462 : Nat := 4983230072969 + 3 ^ 40 * 1458462 * 2
def baseEnd_1458462 : Nat := 166420449403950665426147

theorem tailTrace_1458462 : CollatzResearch.WordTrace tailWord_1458462 prefixEnd_1458462 166420449403950665426147 := by
  unfold tailWord_1458462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649309905281091790500205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35462986161499156216001093 6649309905281091790500205)
  ·
    refine ⟨2493491214480409421437577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6649309905281091790500205 2493491214480409421437577)
    ·
      refine ⟨1870118410860307066078183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2493491214480409421437577 1870118410860307066078183)
      ·
        refine ⟨2805177616290460599117275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1870118410860307066078183 2805177616290460599117275)
        ·
          refine ⟨4207766424435690898675913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805177616290460599117275 4207766424435690898675913)
          ·
            refine ⟨3155824818326768174006935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4207766424435690898675913 3155824818326768174006935)
            ·
              refine ⟨4733737227490152261010403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155824818326768174006935 4733737227490152261010403)
              ·
                refine ⟨7100605841235228391515605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4733737227490152261010403 7100605841235228391515605)
                ·
                  refine ⟨166420449403950665426147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7100605841235228391515605 166420449403950665426147)
                  ·
                    rfl

theorem cell22_1458462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_1458462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458462 prefixEnd_1458462 := by exact prefixLift 1458462
  have htrace : WordTrace (prefixWord ++ tailWord_1458462) baseStart_1458462 baseEnd_1458462 := by
    simpa [prefixWord, tailWord_1458462, baseEnd_1458462] using wordTrace_append hprefix tailTrace_1458462
  have hstable : (prefixWord ++ tailWord_1458462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458462).length < 2 ^ (prefixWord ++ tailWord_1458462).sum := by decide
  have hdescent : baseEnd_1458462 < baseStart_1458462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458503 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1458503 : Nat := 118140960795 + 1458503 * 2 ^ 59
def prefixEnd_1458503 : Nat := 4983230072969 + 3 ^ 40 * 1458503 * 2
def baseEnd_1458503 : Nat := 499275383349741556003315

theorem tailTrace_1458503 : CollatzResearch.WordTrace tailWord_1458503 prefixEnd_1458503 499275383349741556003315 := by
  unfold tailWord_1458503
  simp only [CollatzResearch.WordTrace]
  refine ⟨53195974635100198326244163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35463983090066798884162775 53195974635100198326244163)
  ·
    refine ⟨79793961952650297489366245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53195974635100198326244163 79793961952650297489366245)
    ·
      refine ⟨14961367866121930779256171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79793961952650297489366245 14961367866121930779256171)
      ·
        refine ⟨22442051799182896168884257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14961367866121930779256171 22442051799182896168884257)
        ·
          refine ⟨16831538849387172126663193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22442051799182896168884257 16831538849387172126663193)
          ·
            refine ⟨12623654137040379094997395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16831538849387172126663193 12623654137040379094997395)
            ·
              refine ⟨18935481205560568642496093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12623654137040379094997395 18935481205560568642496093)
              ·
                refine ⟨7100805452085213240936035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18935481205560568642496093 7100805452085213240936035)
                ·
                  refine ⟨10651208178127819861404053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100805452085213240936035 10651208178127819861404053)
                  ·
                    refine ⟨499275383349741556003315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10651208178127819861404053 499275383349741556003315)
                    ·
                      rfl

theorem cell22_1458503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1458503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458503 prefixEnd_1458503 := by exact prefixLift 1458503
  have htrace : WordTrace (prefixWord ++ tailWord_1458503) baseStart_1458503 baseEnd_1458503 := by
    simpa [prefixWord, tailWord_1458503, baseEnd_1458503] using wordTrace_append hprefix tailTrace_1458503
  have hstable : (prefixWord ++ tailWord_1458503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458503).length < 2 ^ (prefixWord ++ tailWord_1458503).sum := by decide
  have hdescent : baseEnd_1458503 < baseStart_1458503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458524 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 6]
def baseStart_1458524 : Nat := 118140960795 + 1458524 * 2 ^ 59
def prefixEnd_1458524 : Nat := 4983230072969 + 3 ^ 40 * 1458524 * 2
def baseEnd_1458524 : Nat := 166427524026301500409417

theorem tailTrace_1458524 : CollatzResearch.WordTrace tailWord_1458524 prefixEnd_1458524 166427524026301500409417 := by
  unfold tailWord_1458524
  simp only [CollatzResearch.WordTrace]
  refine ⟨26598370284012059456379313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35464493712016079275172417 26598370284012059456379313)
  ·
    refine ⟨19948777713009044592284485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26598370284012059456379313 19948777713009044592284485)
    ·
      refine ⟨3740395821189195861053341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19948777713009044592284485 3740395821189195861053341)
      ·
        refine ⟨1402648432945948447895003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3740395821189195861053341 1402648432945948447895003)
        ·
          refine ⟨2103972649418922671842505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402648432945948447895003 2103972649418922671842505)
          ·
            refine ⟨1577979487064192003881879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2103972649418922671842505 1577979487064192003881879)
            ·
              refine ⟨2366969230596288005822819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577979487064192003881879 2366969230596288005822819)
              ·
                refine ⟨3550453845894432008734229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366969230596288005822819 3550453845894432008734229)
                ·
                  refine ⟨166427524026301500409417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3550453845894432008734229 166427524026301500409417)
                  ·
                    rfl

theorem cell22_1458524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_1458524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458524 prefixEnd_1458524 := by exact prefixLift 1458524
  have htrace : WordTrace (prefixWord ++ tailWord_1458524) baseStart_1458524 baseEnd_1458524 := by
    simpa [prefixWord, tailWord_1458524, baseEnd_1458524] using wordTrace_append hprefix tailTrace_1458524
  have hstable : (prefixWord ++ tailWord_1458524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458524).length < 2 ^ (prefixWord ++ tailWord_1458524).sum := by decide
  have hdescent : baseEnd_1458524 < baseStart_1458524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458535 : List Nat := [1, 1, 5, 1, 3, 2, 2, 7]
def baseStart_1458535 : Nat := 118140960795 + 1458535 * 2 ^ 59
def prefixEnd_1458535 : Nat := 4983230072969 + 3 ^ 40 * 1458535 * 2
def baseEnd_1458535 : Nat := 55476259733744904355913

theorem tailTrace_1458535 : CollatzResearch.WordTrace tailWord_1458535 prefixEnd_1458535 55476259733744904355913 := by
  unfold tailWord_1458535
  simp only [CollatzResearch.WordTrace]
  refine ⟨53197141770984267791409059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35464761180656178527606039 53197141770984267791409059)
  ·
    refine ⟨79795712656476401687113589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53197141770984267791409059 79795712656476401687113589)
    ·
      refine ⟨7480848061544662658166899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79795712656476401687113589 7480848061544662658166899)
      ·
        refine ⟨11221272092316993987250349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480848061544662658166899 11221272092316993987250349)
        ·
          refine ⟨4207977034618872745218881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11221272092316993987250349 4207977034618872745218881)
          ·
            refine ⟨3155982775964154558914161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4207977034618872745218881 3155982775964154558914161)
            ·
              refine ⟨2366987081973115919185621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155982775964154558914161 2366987081973115919185621)
              ·
                refine ⟨55476259733744904355913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2366987081973115919185621 55476259733744904355913)
                ·
                  rfl

theorem cell22_1458535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 7].length) (baseStart_1458535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458535 prefixEnd_1458535 := by exact prefixLift 1458535
  have htrace : WordTrace (prefixWord ++ tailWord_1458535) baseStart_1458535 baseEnd_1458535 := by
    simpa [prefixWord, tailWord_1458535, baseEnd_1458535] using wordTrace_append hprefix tailTrace_1458535
  have hstable : (prefixWord ++ tailWord_1458535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458535).length < 2 ^ (prefixWord ++ tailWord_1458535).sum := by decide
  have hdescent : baseEnd_1458535 < baseStart_1458535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458595 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 2, 5]
def baseStart_1458595 : Nat := 118140960795 + 1458595 * 2 ^ 59
def prefixEnd_1458595 : Nat := 4983230072969 + 3 ^ 40 * 1458595 * 2
def baseEnd_1458595 : Nat := 499306876829883982703033

theorem tailTrace_1458595 : CollatzResearch.WordTrace tailWord_1458595 prefixEnd_1458595 499306876829883982703033 := by
  unfold tailWord_1458595
  simp only [CollatzResearch.WordTrace]
  refine ⟨53199330150766898038593239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35466220100511265359062159 53199330150766898038593239)
  ·
    refine ⟨79798995226150347057889859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53199330150766898038593239 79798995226150347057889859)
    ·
      refine ⟨119698492839225520586834789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79798995226150347057889859 119698492839225520586834789)
      ·
        refine ⟨22443467407354785110031523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119698492839225520586834789 22443467407354785110031523)
        ·
          refine ⟨33665201111032177665047285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22443467407354785110031523 33665201111032177665047285)
          ·
            refine ⟨3156112604159266656098183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33665201111032177665047285 3156112604159266656098183)
            ·
              refine ⟨4734168906238899984147275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156112604159266656098183 4734168906238899984147275)
              ·
                refine ⟨7101253359358349976220913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734168906238899984147275 7101253359358349976220913)
                ·
                  refine ⟨5325940019518762482165685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7101253359358349976220913 5325940019518762482165685)
                  ·
                    refine ⟨499306876829883982703033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5325940019518762482165685 499306876829883982703033)
                    ·
                      rfl

theorem cell22_1458595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_1458595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458595 prefixEnd_1458595 := by exact prefixLift 1458595
  have htrace : WordTrace (prefixWord ++ tailWord_1458595) baseStart_1458595 baseEnd_1458595 := by
    simpa [prefixWord, tailWord_1458595, baseEnd_1458595] using wordTrace_append hprefix tailTrace_1458595
  have hstable : (prefixWord ++ tailWord_1458595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458595).length < 2 ^ (prefixWord ++ tailWord_1458595).sum := by decide
  have hdescent : baseEnd_1458595 < baseStart_1458595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458610 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1458610 : Nat := 118140960795 + 1458610 * 2 ^ 59
def prefixEnd_1458610 : Nat := 4983230072969 + 3 ^ 40 * 1458610 * 2
def baseEnd_1458610 : Nat := 499312011636428943577987

theorem tailTrace_1458610 : CollatzResearch.WordTrace tailWord_1458610 prefixEnd_1458610 499312011636428943577987 := by
  unfold tailWord_1458610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13299969311428138900097321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35466584830475037066926189 13299969311428138900097321)
  ·
    refine ⟨9974976983571104175072991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13299969311428138900097321 9974976983571104175072991)
    ·
      refine ⟨14962465475356656262609487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9974976983571104175072991 14962465475356656262609487)
      ·
        refine ⟨22443698213034984393914231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14962465475356656262609487 22443698213034984393914231)
        ·
          refine ⟨33665547319552476590871347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22443698213034984393914231 33665547319552476590871347)
          ·
            refine ⟨50498320979328714886307021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33665547319552476590871347 50498320979328714886307021)
            ·
              refine ⟨18936870367248268082365133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50498320979328714886307021 18936870367248268082365133)
              ·
                refine ⟨7101326387718100530886925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18936870367248268082365133 7101326387718100530886925)
                ·
                  refine ⟨2662997395394287699082597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7101326387718100530886925 2662997395394287699082597)
                  ·
                    refine ⟨499312011636428943577987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2662997395394287699082597 499312011636428943577987)
                    ·
                      rfl

theorem cell22_1458610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1458610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458610 prefixEnd_1458610 := by exact prefixLift 1458610
  have htrace : WordTrace (prefixWord ++ tailWord_1458610) baseStart_1458610 baseEnd_1458610 := by
    simpa [prefixWord, tailWord_1458610, baseEnd_1458610] using wordTrace_append hprefix tailTrace_1458610
  have hstable : (prefixWord ++ tailWord_1458610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458610).length < 2 ^ (prefixWord ++ tailWord_1458610).sum := by decide
  have hdescent : baseEnd_1458610 < baseStart_1458610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458655 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 1, 6]
def baseStart_1458655 : Nat := 118140960795 + 1458655 * 2 ^ 59
def prefixEnd_1458655 : Nat := 4983230072969 + 3 ^ 40 * 1458655 * 2
def baseEnd_1458655 : Nat := 499327416056063826202849

theorem tailTrace_1458655 : CollatzResearch.WordTrace tailWord_1458655 prefixEnd_1458655 499327416056063826202849 := by
  unfold tailWord_1458655
  simp only [CollatzResearch.WordTrace]
  refine ⟨53201518530549528285777419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35467679020366352190518279 53201518530549528285777419)
  ·
    refine ⟨79802277795824292428666129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53201518530549528285777419 79802277795824292428666129)
    ·
      refine ⟨59851708346868219321499597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79802277795824292428666129 59851708346868219321499597)
      ·
        refine ⟨22444390630075582245562349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59851708346868219321499597 22444390630075582245562349)
        ·
          refine ⟨8416646486278343342085881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22444390630075582245562349 8416646486278343342085881)
          ·
            refine ⟨6312484864708757506564411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8416646486278343342085881 6312484864708757506564411)
            ·
              refine ⟨9468727297063136259846617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312484864708757506564411 9468727297063136259846617)
              ·
                refine ⟨7101545472797352194884963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9468727297063136259846617 7101545472797352194884963)
                ·
                  refine ⟨10652318209196028292327445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7101545472797352194884963 10652318209196028292327445)
                  ·
                    refine ⟨499327416056063826202849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10652318209196028292327445 499327416056063826202849)
                    ·
                      rfl

theorem cell22_1458655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_1458655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458655 prefixEnd_1458655 := by exact prefixLift 1458655
  have htrace : WordTrace (prefixWord ++ tailWord_1458655) baseStart_1458655 baseEnd_1458655 := by
    simpa [prefixWord, tailWord_1458655, baseEnd_1458655] using wordTrace_append hprefix tailTrace_1458655
  have hstable : (prefixWord ++ tailWord_1458655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458655).length < 2 ^ (prefixWord ++ tailWord_1458655).sum := by decide
  have hdescent : baseEnd_1458655 < baseStart_1458655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458708 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1458708 : Nat := 118140960795 + 1458708 * 2 ^ 59
def prefixEnd_1458708 : Nat := 4983230072969 + 3 ^ 40 * 1458708 * 2
def baseEnd_1458708 : Nat := 499345559039189354627687

theorem tailTrace_1458708 : CollatzResearch.WordTrace tailWord_1458708 prefixEnd_1458708 499345559039189354627687 := by
  unfold tailWord_1458708
  simp only [CollatzResearch.WordTrace]
  refine ⟨26601725799678759168728389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35468967732905012224971185 26601725799678759168728389)
  ·
    refine ⟨4987823587439767344136573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26601725799678759168728389 4987823587439767344136573)
    ·
      refine ⟨1870433845289912754051215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4987823587439767344136573 1870433845289912754051215)
      ·
        refine ⟨2805650767934869131076823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1870433845289912754051215 2805650767934869131076823)
        ·
          refine ⟨4208476151902303696615235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805650767934869131076823 4208476151902303696615235)
          ·
            refine ⟨6312714227853455544922853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208476151902303696615235 6312714227853455544922853)
            ·
              refine ⟨1183633917722522914673035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6312714227853455544922853 1183633917722522914673035)
              ·
                refine ⟨1775450876583784372009553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183633917722522914673035 1775450876583784372009553)
                ·
                  refine ⟨1331588157437838279007165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1775450876583784372009553 1331588157437838279007165)
                  ·
                    refine ⟨499345559039189354627687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1331588157437838279007165 499345559039189354627687)
                    ·
                      rfl

theorem cell22_1458708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1458708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458708 prefixEnd_1458708 := by exact prefixLift 1458708
  have htrace : WordTrace (prefixWord ++ tailWord_1458708) baseStart_1458708 baseEnd_1458708 := by
    simpa [prefixWord, tailWord_1458708, baseEnd_1458708] using wordTrace_append hprefix tailTrace_1458708
  have hstable : (prefixWord ++ tailWord_1458708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458708).length < 2 ^ (prefixWord ++ tailWord_1458708).sum := by decide
  have hdescent : baseEnd_1458708 < baseStart_1458708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458749 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 5]
def baseStart_1458749 : Nat := 118140960795 + 1458749 * 2 ^ 59
def prefixEnd_1458749 : Nat := 4983230072969 + 3 ^ 40 * 1458749 * 2
def baseEnd_1458749 : Nat := 166453198059026304784187

theorem tailTrace_1458749 : CollatzResearch.WordTrace tailWord_1458749 prefixEnd_1458749 166453198059026304784187 := by
  unfold tailWord_1458749
  simp only [CollatzResearch.WordTrace]
  refine ⟨53204946992208982339699301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35469964661472654893132867 53204946992208982339699301)
  ·
    refine ⟨9975927561039184188693619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53204946992208982339699301 9975927561039184188693619)
    ·
      refine ⟨14963891341558776283040429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9975927561039184188693619 14963891341558776283040429)
      ·
        refine ⟨5611459253084541106140161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14963891341558776283040429 5611459253084541106140161)
        ·
          refine ⟨4208594439813405829605121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5611459253084541106140161 4208594439813405829605121)
          ·
            refine ⟨3156445829860054372203841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4208594439813405829605121 3156445829860054372203841)
            ·
              refine ⟨2367334372395040779152881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3156445829860054372203841 2367334372395040779152881)
              ·
                refine ⟨1775500779296280584364661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367334372395040779152881 1775500779296280584364661)
                ·
                  refine ⟨166453198059026304784187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1775500779296280584364661 166453198059026304784187)
                  ·
                    rfl

theorem cell22_1458749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_1458749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458749 prefixEnd_1458749 := by exact prefixLift 1458749
  have htrace : WordTrace (prefixWord ++ tailWord_1458749) baseStart_1458749 baseEnd_1458749 := by
    simpa [prefixWord, tailWord_1458749, baseEnd_1458749] using wordTrace_append hprefix tailTrace_1458749
  have hstable : (prefixWord ++ tailWord_1458749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458749).length < 2 ^ (prefixWord ++ tailWord_1458749).sum := by decide
  have hdescent : baseEnd_1458749 < baseStart_1458749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458753 : List Nat := [1, 2, 5, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1458753 : Nat := 118140960795 + 1458753 * 2 ^ 59
def prefixEnd_1458753 : Nat := 4983230072969 + 3 ^ 40 * 1458753 * 2
def baseEnd_1458753 : Nat := 499360963458824237252549

theorem tailTrace_1458753 : CollatzResearch.WordTrace tailWord_1458753 prefixEnd_1458753 499360963458824237252549 := by
  unfold tailWord_1458753
  simp only [CollatzResearch.WordTrace]
  refine ⟨53205092884194491022844913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35470061922796327348563275 53205092884194491022844913)
  ·
    refine ⟨39903819663145868267133685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53205092884194491022844913 39903819663145868267133685)
    ·
      refine ⟨3740983093419925150043783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39903819663145868267133685 3740983093419925150043783)
      ·
        refine ⟨5611474640129887725065675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3740983093419925150043783 5611474640129887725065675)
        ·
          refine ⟨8417211960194831587598513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611474640129887725065675 8417211960194831587598513)
          ·
            refine ⟨6312908970146123690698885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8417211960194831587598513 6312908970146123690698885)
            ·
              refine ⟨1183670431902398192006041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6312908970146123690698885 1183670431902398192006041)
              ·
                refine ⟨887752823926798644004531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183670431902398192006041 887752823926798644004531)
                ·
                  refine ⟨1331629235890197966006797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887752823926798644004531 1331629235890197966006797)
                  ·
                    refine ⟨499360963458824237252549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1331629235890197966006797 499360963458824237252549)
                    ·
                      rfl

theorem cell22_1458753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1458753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458753 prefixEnd_1458753 := by exact prefixLift 1458753
  have htrace : WordTrace (prefixWord ++ tailWord_1458753) baseStart_1458753 baseEnd_1458753 := by
    simpa [prefixWord, tailWord_1458753, baseEnd_1458753] using wordTrace_append hprefix tailTrace_1458753
  have hstable : (prefixWord ++ tailWord_1458753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458753).length < 2 ^ (prefixWord ++ tailWord_1458753).sum := by decide
  have hdescent : baseEnd_1458753 < baseStart_1458753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458760 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 10]
def baseStart_1458760 : Nat := 118140960795 + 1458760 * 2 ^ 59
def prefixEnd_1458760 : Nat := 4983230072969 + 3 ^ 40 * 1458760 * 2
def baseEnd_1458760 : Nat := 166454453233959517442509

theorem tailTrace_1458760 : CollatzResearch.WordTrace tailWord_1458760 prefixEnd_1458760 166454453233959517442509 := by
  unfold tailWord_1458760
  simp only [CollatzResearch.WordTrace]
  refine ⟨26602674097584565609174867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35470232130112754145566489 26602674097584565609174867)
  ·
    refine ⟨39904011146376848413762301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26602674097584565609174867 39904011146376848413762301)
    ·
      refine ⟨14964004179891318155160863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39904011146376848413762301 14964004179891318155160863)
      ·
        refine ⟨22446006269836977232741295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14964004179891318155160863 22446006269836977232741295)
        ·
          refine ⟨33669009404755465849111943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22446006269836977232741295 33669009404755465849111943)
          ·
            refine ⟨50503514107133198773667915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33669009404755465849111943 50503514107133198773667915)
            ·
              refine ⟨75755271160699798160501873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50503514107133198773667915 75755271160699798160501873)
              ·
                refine ⟨56816453370524848620376405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75755271160699798160501873 56816453370524848620376405)
                ·
                  refine ⟨166454453233959517442509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56816453370524848620376405 166454453233959517442509)
                  ·
                    rfl

theorem cell22_1458760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_1458760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458760 prefixEnd_1458760 := by exact prefixLift 1458760
  have htrace : WordTrace (prefixWord ++ tailWord_1458760) baseStart_1458760 baseEnd_1458760 := by
    simpa [prefixWord, tailWord_1458760, baseEnd_1458760] using wordTrace_append hprefix tailTrace_1458760
  have hstable : (prefixWord ++ tailWord_1458760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458760).length < 2 ^ (prefixWord ++ tailWord_1458760).sum := by decide
  have hdescent : baseEnd_1458760 < baseStart_1458760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458762 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1458762 : Nat := 118140960795 + 1458762 * 2 ^ 59
def prefixEnd_1458762 : Nat := 4983230072969 + 3 ^ 40 * 1458762 * 2
def baseEnd_1458762 : Nat := 499364044342751213777521

theorem tailTrace_1458762 : CollatzResearch.WordTrace tailWord_1458762 prefixEnd_1458762 499364044342751213777521 := by
  unfold tailWord_1458762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13301355285290471389980635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35470280760774590373281693 13301355285290471389980635)
  ·
    refine ⟨19952032927935707084970953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13301355285290471389980635 19952032927935707084970953)
    ·
      refine ⟨14964024695951780313728215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19952032927935707084970953 14964024695951780313728215)
      ·
        refine ⟨22446037043927670470592323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14964024695951780313728215 22446037043927670470592323)
        ·
          refine ⟨33669055565891505705888485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22446037043927670470592323 33669055565891505705888485)
          ·
            refine ⟨6312947918604657319854091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33669055565891505705888485 6312947918604657319854091)
            ·
              refine ⟨9469421877906985979781137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6312947918604657319854091 9469421877906985979781137)
              ·
                refine ⟨7102066408430239484835853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9469421877906985979781137 7102066408430239484835853)
                ·
                  refine ⟨2663274903161339806813445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7102066408430239484835853 2663274903161339806813445)
                  ·
                    refine ⟨499364044342751213777521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2663274903161339806813445 499364044342751213777521)
                    ·
                      rfl

theorem cell22_1458762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1458762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458762 prefixEnd_1458762 := by exact prefixLift 1458762
  have htrace : WordTrace (prefixWord ++ tailWord_1458762) baseStart_1458762 baseEnd_1458762 := by
    simpa [prefixWord, tailWord_1458762, baseEnd_1458762] using wordTrace_append hprefix tailTrace_1458762
  have hstable : (prefixWord ++ tailWord_1458762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458762).length < 2 ^ (prefixWord ++ tailWord_1458762).sum := by decide
  have hdescent : baseEnd_1458762 < baseStart_1458762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458807 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 2, 4]
def baseStart_1458807 : Nat := 118140960795 + 1458807 * 2 ^ 59
def prefixEnd_1458807 : Nat := 4983230072969 + 3 ^ 40 * 1458807 * 2
def baseEnd_1458807 : Nat := 499379448762386096402383

theorem tailTrace_1458807 : CollatzResearch.WordTrace tailWord_1458807 prefixEnd_1458807 499379448762386096402383 := by
  unfold tailWord_1458807
  simp only [CollatzResearch.WordTrace]
  refine ⟨53207062425998858245310675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35471374950665905496873783 53207062425998858245310675)
  ·
    refine ⟨79810593638998287367966013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53207062425998858245310675 79810593638998287367966013)
    ·
      refine ⟨29928972614624357762987255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79810593638998287367966013 29928972614624357762987255)
      ·
        refine ⟨44893458921936536644480883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29928972614624357762987255 44893458921936536644480883)
        ·
          refine ⟨67340188382904804966721325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44893458921936536644480883 67340188382904804966721325)
          ·
            refine ⟨25252570643589301862520497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67340188382904804966721325 25252570643589301862520497)
            ·
              refine ⟨18939427982691976396890373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25252570643589301862520497 18939427982691976396890373)
              ·
                refine ⟨3551142746754745574416945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18939427982691976396890373 3551142746754745574416945)
                ·
                  refine ⟨2663357060066059180812709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3551142746754745574416945 2663357060066059180812709)
                  ·
                    refine ⟨499379448762386096402383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2663357060066059180812709 499379448762386096402383)
                    ·
                      rfl

theorem cell22_1458807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_1458807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458807 prefixEnd_1458807 := by exact prefixLift 1458807
  have htrace : WordTrace (prefixWord ++ tailWord_1458807) baseStart_1458807 baseEnd_1458807 := by
    simpa [prefixWord, tailWord_1458807, baseEnd_1458807] using wordTrace_append hprefix tailTrace_1458807
  have hstable : (prefixWord ++ tailWord_1458807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458807).length < 2 ^ (prefixWord ++ tailWord_1458807).sum := by decide
  have hdescent : baseEnd_1458807 < baseStart_1458807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458809 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 4, 3]
def baseStart_1458809 : Nat := 118140960795 + 1458809 * 2 ^ 59
def prefixEnd_1458809 : Nat := 4983230072969 + 3 ^ 40 * 1458809 * 2
def baseEnd_1458809 : Nat := 499380133403258757852377

theorem tailTrace_1458809 : CollatzResearch.WordTrace tailWord_1458809 prefixEnd_1458809 499380133403258757852377 := by
  unfold tailWord_1458809
  simp only [CollatzResearch.WordTrace]
  refine ⟨53207135371991612586883481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35471423581327741724588987 53207135371991612586883481)
  ·
    refine ⟨39905351528993709440162611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53207135371991612586883481 39905351528993709440162611)
    ·
      refine ⟨59858027293490564160243917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39905351528993709440162611 59858027293490564160243917)
      ·
        refine ⟨22446760235058961560091469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59858027293490564160243917 22446760235058961560091469)
        ·
          refine ⟨8417535088147110585034301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22446760235058961560091469 8417535088147110585034301)
          ·
            refine ⟨3156575658055166469387863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8417535088147110585034301 3156575658055166469387863)
            ·
              refine ⟨4734863487082749704081795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156575658055166469387863 4734863487082749704081795)
              ·
                refine ⟨7102295230624124556122693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734863487082749704081795 7102295230624124556122693)
                ·
                  refine ⟨1331680355742023354273005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7102295230624124556122693 1331680355742023354273005)
                  ·
                    refine ⟨499380133403258757852377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1331680355742023354273005 499380133403258757852377)
                    ·
                      rfl

theorem cell22_1458809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_1458809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458809 prefixEnd_1458809 := by exact prefixLift 1458809
  have htrace : WordTrace (prefixWord ++ tailWord_1458809) baseStart_1458809 baseEnd_1458809 := by
    simpa [prefixWord, tailWord_1458809, baseEnd_1458809] using wordTrace_append hprefix tailTrace_1458809
  have hstable : (prefixWord ++ tailWord_1458809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458809).length < 2 ^ (prefixWord ++ tailWord_1458809).sum := by decide
  have hdescent : baseEnd_1458809 < baseStart_1458809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458826 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1458826 : Nat := 118140960795 + 1458826 * 2 ^ 59
def prefixEnd_1458826 : Nat := 4983230072969 + 3 ^ 40 * 1458826 * 2
def baseEnd_1458826 : Nat := 499385952850676380177325

theorem tailTrace_1458826 : CollatzResearch.WordTrace tailWord_1458826 prefixEnd_1458826 499385952850676380177325 := by
  unfold tailWord_1458826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13301938853232506122563083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35471836941953349660168221 13301938853232506122563083)
  ·
    refine ⟨19952908279848759183844625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13301938853232506122563083 19952908279848759183844625)
    ·
      refine ⟨14964681209886569387883469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19952908279848759183844625 14964681209886569387883469)
      ·
        refine ⟨5611755453707463520456301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14964681209886569387883469 5611755453707463520456301)
        ·
          refine ⟨2104408295140298820171113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5611755453707463520456301 2104408295140298820171113)
          ·
            refine ⟨1578306221355224115128335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2104408295140298820171113 1578306221355224115128335)
            ·
              refine ⟨2367459332032836172692503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578306221355224115128335 2367459332032836172692503)
              ·
                refine ⟨3551188998049254259038755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367459332032836172692503 3551188998049254259038755)
                ·
                  refine ⟨5326783497073881388558133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551188998049254259038755 5326783497073881388558133)
                  ·
                    refine ⟨499385952850676380177325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5326783497073881388558133 499385952850676380177325)
                    ·
                      rfl

theorem cell22_1458826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1458826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458826 prefixEnd_1458826 := by exact prefixLift 1458826
  have htrace : WordTrace (prefixWord ++ tailWord_1458826) baseStart_1458826 baseEnd_1458826 := by
    simpa [prefixWord, tailWord_1458826, baseEnd_1458826] using wordTrace_append hprefix tailTrace_1458826
  have hstable : (prefixWord ++ tailWord_1458826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458826).length < 2 ^ (prefixWord ++ tailWord_1458826).sum := by decide
  have hdescent : baseEnd_1458826 < baseStart_1458826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458858 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1458858 : Nat := 118140960795 + 1458858 * 2 ^ 59
def prefixEnd_1458858 : Nat := 4983230072969 + 3 ^ 40 * 1458858 * 2
def baseEnd_1458858 : Nat := 499396907104638963377227

theorem tailTrace_1458858 : CollatzResearch.WordTrace tailWord_1458858 prefixEnd_1458858 499396907104638963377227 := by
  unfold tailWord_1458858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13302230637203523488854307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35472615032542729303611485 13302230637203523488854307)
  ·
    refine ⟨19953345955805285233281461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13302230637203523488854307 19953345955805285233281461)
    ·
      refine ⟨1870626183356745490620137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19953345955805285233281461 1870626183356745490620137)
      ·
        refine ⟨1402969637517559117965103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1870626183356745490620137 1402969637517559117965103)
        ·
          refine ⟨2104454456276338676947655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402969637517559117965103 2104454456276338676947655)
          ·
            refine ⟨3156681684414508015421483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104454456276338676947655 3156681684414508015421483)
            ·
              refine ⟨4735022526621762023132225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156681684414508015421483 4735022526621762023132225)
              ·
                refine ⟨3551266894966321517349169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735022526621762023132225 3551266894966321517349169)
                ·
                  refine ⟨2663450171224741138011877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3551266894966321517349169 2663450171224741138011877)
                  ·
                    refine ⟨499396907104638963377227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2663450171224741138011877 499396907104638963377227)
                    ·
                      rfl

theorem cell22_1458858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1458858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458858 prefixEnd_1458858 := by exact prefixLift 1458858
  have htrace : WordTrace (prefixWord ++ tailWord_1458858) baseStart_1458858 baseEnd_1458858 := by
    simpa [prefixWord, tailWord_1458858, baseEnd_1458858] using wordTrace_append hprefix tailTrace_1458858
  have hstable : (prefixWord ++ tailWord_1458858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458858).length < 2 ^ (prefixWord ++ tailWord_1458858).sum := by decide
  have hdescent : baseEnd_1458858 < baseStart_1458858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458867 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 7]
def baseStart_1458867 : Nat := 118140960795 + 1458867 * 2 ^ 59
def prefixEnd_1458867 : Nat := 4983230072969 + 3 ^ 40 * 1458867 * 2
def baseEnd_1458867 : Nat := 166466662662855313300733

theorem tailTrace_1458867 : CollatzResearch.WordTrace tailWord_1458867 prefixEnd_1458867 166466662662855313300733 := by
  unfold tailWord_1458867
  simp only [CollatzResearch.WordTrace]
  refine ⟨53209250805781488492494855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35472833870520992328329903 53209250805781488492494855)
  ·
    refine ⟨79813876208672232738742283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53209250805781488492494855 79813876208672232738742283)
    ·
      refine ⟨119720814313008349108113425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79813876208672232738742283 119720814313008349108113425)
      ·
        refine ⟨89790610734756261831085069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119720814313008349108113425 89790610734756261831085069)
        ·
          refine ⟨33671479025533598186656901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89790610734756261831085069 33671479025533598186656901)
          ·
            refine ⟨6313402317287549659998169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33671479025533598186656901 6313402317287549659998169)
            ·
              refine ⟨4735051737965662244998627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6313402317287549659998169 4735051737965662244998627)
              ·
                refine ⟨7102577606948493367497941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4735051737965662244998627 7102577606948493367497941)
                ·
                  refine ⟨166466662662855313300733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7102577606948493367497941 166466662662855313300733)
                  ·
                    rfl

theorem cell22_1458867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 7].length) (baseStart_1458867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458867 prefixEnd_1458867 := by exact prefixLift 1458867
  have htrace : WordTrace (prefixWord ++ tailWord_1458867) baseStart_1458867 baseEnd_1458867 := by
    simpa [prefixWord, tailWord_1458867, baseEnd_1458867] using wordTrace_append hprefix tailTrace_1458867
  have hstable : (prefixWord ++ tailWord_1458867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458867).length < 2 ^ (prefixWord ++ tailWord_1458867).sum := by decide
  have hdescent : baseEnd_1458867 < baseStart_1458867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458946 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1458946 : Nat := 118140960795 + 1458946 * 2 ^ 59
def prefixEnd_1458946 : Nat := 4983230072969 + 3 ^ 40 * 1458946 * 2
def baseEnd_1458946 : Nat := 166475677101012022392319

theorem tailTrace_1458946 : CollatzResearch.WordTrace tailWord_1458946 prefixEnd_1458946 166475677101012022392319 := by
  unfold tailWord_1458946
  simp only [CollatzResearch.WordTrace]
  refine ⟨13303033043123821246155173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35474754781663523323080461 13303033043123821246155173)
  ·
    refine ⟨2494318695585716483654095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13303033043123821246155173 2494318695585716483654095)
    ·
      refine ⟨3741478043378574725481143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494318695585716483654095 3741478043378574725481143)
      ·
        refine ⟨5612217065067862088221715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3741478043378574725481143 5612217065067862088221715)
        ·
          refine ⟨8418325597601793132332573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5612217065067862088221715 8418325597601793132332573)
          ·
            refine ⟨3156872099100672424624715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8418325597601793132332573 3156872099100672424624715)
            ·
              refine ⟨4735308148651008636937073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156872099100672424624715 4735308148651008636937073)
              ·
                refine ⟨3551481111488256477702805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735308148651008636937073 3551481111488256477702805)
                ·
                  refine ⟨166475677101012022392319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3551481111488256477702805 166475677101012022392319)
                  ·
                    rfl

theorem cell22_1458946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1458946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458946 prefixEnd_1458946 := by exact prefixLift 1458946
  have htrace : WordTrace (prefixWord ++ tailWord_1458946) baseStart_1458946 baseEnd_1458946 := by
    simpa [prefixWord, tailWord_1458946, baseEnd_1458946] using wordTrace_append hprefix tailTrace_1458946
  have hstable : (prefixWord ++ tailWord_1458946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458946).length < 2 ^ (prefixWord ++ tailWord_1458946).sum := by decide
  have hdescent : baseEnd_1458946 < baseStart_1458946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458978 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1458978 : Nat := 118140960795 + 1458978 * 2 ^ 59
def prefixEnd_1458978 : Nat := 4983230072969 + 3 ^ 40 * 1458978 * 2
def baseEnd_1458978 : Nat := 499437985556998650376859

theorem tailTrace_1458978 : CollatzResearch.WordTrace tailWord_1458978 prefixEnd_1458978 499437985556998650376859 := by
  unfold tailWord_1458978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13303324827094838612446397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35475532872252902966523725 13303324827094838612446397)
  ·
    refine ⟨4988746810160564479667399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13303324827094838612446397 4988746810160564479667399)
    ·
      refine ⟨7483120215240846719501099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4988746810160564479667399 7483120215240846719501099)
      ·
        refine ⟨11224680322861270079251649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7483120215240846719501099 11224680322861270079251649)
        ·
          refine ⟨8418510242145952559438737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11224680322861270079251649 8418510242145952559438737)
          ·
            refine ⟨6313882681609464419579053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8418510242145952559438737 6313882681609464419579053)
            ·
              refine ⟨2367706005603549157342145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6313882681609464419579053 2367706005603549157342145)
              ·
                refine ⟨1775779504202661868006609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367706005603549157342145 1775779504202661868006609)
                ·
                  refine ⟨1331834628151996401004957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1775779504202661868006609 1331834628151996401004957)
                  ·
                    refine ⟨499437985556998650376859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1331834628151996401004957 499437985556998650376859)
                    ·
                      rfl

theorem cell22_1458978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1458978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1458978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1458978 prefixEnd_1458978 := by exact prefixLift 1458978
  have htrace : WordTrace (prefixWord ++ tailWord_1458978) baseStart_1458978 baseEnd_1458978 := by
    simpa [prefixWord, tailWord_1458978, baseEnd_1458978] using wordTrace_append hprefix tailTrace_1458978
  have hstable : (prefixWord ++ tailWord_1458978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458978).length < 2 ^ (prefixWord ++ tailWord_1458978).sum := by decide
  have hdescent : baseEnd_1458978 < baseStart_1458978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459014 : List Nat := [6, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1459014 : Nat := 118140960795 + 1459014 * 2 ^ 59
def prefixEnd_1459014 : Nat := 4983230072969 + 3 ^ 40 * 1459014 * 2
def baseEnd_1459014 : Nat := 166483436364235518825583

theorem tailTrace_1459014 : CollatzResearch.WordTrace tailWord_1459014 prefixEnd_1459014 166483436364235518825583 := by
  unfold tailWord_1459014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662956635507779143690503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35476408224165955065397397 1662956635507779143690503)
  ·
    refine ⟨2494434953261668715535755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1662956635507779143690503 2494434953261668715535755)
    ·
      refine ⟨3741652429892503073303633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494434953261668715535755 3741652429892503073303633)
      ·
        refine ⟨2806239322419377304977725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3741652429892503073303633 2806239322419377304977725)
        ·
          refine ⟨1052339745907266489366647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2806239322419377304977725 1052339745907266489366647)
          ·
            refine ⟨1578509618860899734049971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052339745907266489366647 1578509618860899734049971)
            ·
              refine ⟨2367764428291349601074957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578509618860899734049971 2367764428291349601074957)
              ·
                refine ⟨887911660609256100403109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2367764428291349601074957 887911660609256100403109)
                ·
                  refine ⟨166483436364235518825583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 887911660609256100403109 166483436364235518825583)
                  ·
                    rfl

theorem cell22_1459014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1459014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459014 prefixEnd_1459014 := by exact prefixLift 1459014
  have htrace : WordTrace (prefixWord ++ tailWord_1459014) baseStart_1459014 baseEnd_1459014 := by
    simpa [prefixWord, tailWord_1459014, baseEnd_1459014] using wordTrace_append hprefix tailTrace_1459014
  have hstable : (prefixWord ++ tailWord_1459014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459014).length < 2 ^ (prefixWord ++ tailWord_1459014).sum := by decide
  have hdescent : baseEnd_1459014 < baseStart_1459014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459036 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 7]
def baseStart_1459036 : Nat := 118140960795 + 1459036 * 2 ^ 59
def prefixEnd_1459036 : Nat := 4983230072969 + 3 ^ 40 * 1459036 * 2
def baseEnd_1459036 : Nat := 166485946714101944142227

theorem tailTrace_1459036 : CollatzResearch.WordTrace tailWord_1459036 prefixEnd_1459036 166485946714101944142227 := by
  unfold tailWord_1459036
  simp only [CollatzResearch.WordTrace]
  refine ⟨26607707371084615177698481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35476943161446153570264641 26607707371084615177698481)
  ·
    refine ⟨19955780528313461383273861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26607707371084615177698481 19955780528313461383273861)
    ·
      refine ⟨3741708849058774009363849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19955780528313461383273861 3741708849058774009363849)
      ·
        refine ⟨2806281636794080507022887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3741708849058774009363849 2806281636794080507022887)
        ·
          refine ⟨4209422455191120760534331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2806281636794080507022887 4209422455191120760534331)
          ·
            refine ⟨6314133682786681140801497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209422455191120760534331 6314133682786681140801497)
            ·
              refine ⟨4735600262090010855601123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6314133682786681140801497 4735600262090010855601123)
              ·
                refine ⟨7103400393135016283401685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4735600262090010855601123 7103400393135016283401685)
                ·
                  refine ⟨166485946714101944142227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7103400393135016283401685 166485946714101944142227)
                  ·
                    rfl

theorem cell22_1459036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_1459036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459036 prefixEnd_1459036 := by exact prefixLift 1459036
  have htrace : WordTrace (prefixWord ++ tailWord_1459036) baseStart_1459036 baseEnd_1459036 := by
    simpa [prefixWord, tailWord_1459036, baseEnd_1459036] using wordTrace_append hprefix tailTrace_1459036
  have hstable : (prefixWord ++ tailWord_1459036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459036).length < 2 ^ (prefixWord ++ tailWord_1459036).sum := by decide
  have hdescent : baseEnd_1459036 < baseStart_1459036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459040 : List Nat := [2, 1, 1, 3, 3, 1, 5, 2, 1, 3]
def baseStart_1459040 : Nat := 118140960795 + 1459040 * 2 ^ 59
def prefixEnd_1459040 : Nat := 4983230072969 + 3 ^ 40 * 1459040 * 2
def baseEnd_1459040 : Nat := 499459209424051155326669

theorem tailTrace_1459040 : CollatzResearch.WordTrace tailWord_1459040 prefixEnd_1459040 499459209424051155326669 := by
  unfold tailWord_1459040
  simp only [CollatzResearch.WordTrace]
  refine ⟨26607780317077369519271287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35477040422769826025695049 26607780317077369519271287)
  ·
    refine ⟨39911670475616054278906931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26607780317077369519271287 39911670475616054278906931)
    ·
      refine ⟨59867505713424081418360397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39911670475616054278906931 59867505713424081418360397)
      ·
        refine ⟨22450314642534030531885149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59867505713424081418360397 22450314642534030531885149)
        ·
          refine ⟨8418867990950261449456931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22450314642534030531885149 8418867990950261449456931)
          ·
            refine ⟨12628301986425392174185397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418867990950261449456931 12628301986425392174185397)
            ·
              refine ⟨1183903311227380516329881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12628301986425392174185397 1183903311227380516329881)
              ·
                refine ⟨887927483420535387247411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183903311227380516329881 887927483420535387247411)
                ·
                  refine ⟨1331891225130803080871117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887927483420535387247411 1331891225130803080871117)
                  ·
                    refine ⟨499459209424051155326669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1331891225130803080871117 499459209424051155326669)
                    ·
                      rfl

theorem cell22_1459040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 3].length) (baseStart_1459040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459040 prefixEnd_1459040 := by exact prefixLift 1459040
  have htrace : WordTrace (prefixWord ++ tailWord_1459040) baseStart_1459040 baseEnd_1459040 := by
    simpa [prefixWord, tailWord_1459040, baseEnd_1459040] using wordTrace_append hprefix tailTrace_1459040
  have hstable : (prefixWord ++ tailWord_1459040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459040).length < 2 ^ (prefixWord ++ tailWord_1459040).sum := by decide
  have hdescent : baseEnd_1459040 < baseStart_1459040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459128 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 2, 4]
def baseStart_1459128 : Nat := 118140960795 + 1459128 * 2 ^ 59
def prefixEnd_1459128 : Nat := 4983230072969 + 3 ^ 40 * 1459128 * 2
def baseEnd_1459128 : Nat := 499489333622448259126399

theorem tailTrace_1459128 : CollatzResearch.WordTrace tailWord_1459128 prefixEnd_1459128 499489333622448259126399 := by
  unfold tailWord_1459128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26609385128917965033873019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35479180171890620045164025 26609385128917965033873019)
  ·
    refine ⟨39914077693376947550809529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26609385128917965033873019 39914077693376947550809529)
    ·
      refine ⟨29935558270032710663107147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39914077693376947550809529 29935558270032710663107147)
      ·
        refine ⟨44903337405049065994660721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29935558270032710663107147 44903337405049065994660721)
        ·
          refine ⟨33677503053786799495995541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44903337405049065994660721 33677503053786799495995541)
          ·
            refine ⟨1578632955646256226374791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33677503053786799495995541 1578632955646256226374791)
            ·
              refine ⟨2367949433469384339562187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578632955646256226374791 2367949433469384339562187)
              ·
                refine ⟨3551924150204076509343281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367949433469384339562187 3551924150204076509343281)
                ·
                  refine ⟨2663943112653057382007461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3551924150204076509343281 2663943112653057382007461)
                  ·
                    refine ⟨499489333622448259126399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2663943112653057382007461 499489333622448259126399)
                    ·
                      rfl

theorem cell22_1459128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_1459128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459128 prefixEnd_1459128 := by exact prefixLift 1459128
  have htrace : WordTrace (prefixWord ++ tailWord_1459128) baseStart_1459128 baseEnd_1459128 := by
    simpa [prefixWord, tailWord_1459128, baseEnd_1459128] using wordTrace_append hprefix tailTrace_1459128
  have hstable : (prefixWord ++ tailWord_1459128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459128).length < 2 ^ (prefixWord ++ tailWord_1459128).sum := by decide
  have hdescent : baseEnd_1459128 < baseStart_1459128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459139 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 4, 6]
def baseStart_1459139 : Nat := 118140960795 + 1459139 * 2 ^ 59
def prefixEnd_1459139 : Nat := 4983230072969 + 3 ^ 40 * 1459139 * 2
def baseEnd_1459139 : Nat := 499493099147247897101365

theorem tailTrace_1459139 : CollatzResearch.WordTrace tailWord_1459139 prefixEnd_1459139 499493099147247897101365 := by
  unfold tailWord_1459139
  simp only [CollatzResearch.WordTrace]
  refine ⟨53219171460796078946396471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35479447640530719297597647 53219171460796078946396471)
  ·
    refine ⟨79828757191194118419594707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53219171460796078946396471 79828757191194118419594707)
    ·
      refine ⟨119743135786791177629392061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79828757191194118419594707 119743135786791177629392061)
      ·
        refine ⟨44903675920046691611022023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119743135786791177629392061 44903675920046691611022023)
        ·
          refine ⟨67355513880070037416533035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44903675920046691611022023 67355513880070037416533035)
          ·
            refine ⟨101033270820105056124799553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67355513880070037416533035 101033270820105056124799553)
            ·
              refine ⟨75774953115078792093599665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101033270820105056124799553 75774953115078792093599665)
              ·
                refine ⟨56831214836309094070199749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75774953115078792093599665 56831214836309094070199749)
                ·
                  refine ⟨10655852781807955138162453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56831214836309094070199749 10655852781807955138162453)
                  ·
                    refine ⟨499493099147247897101365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10655852781807955138162453 499493099147247897101365)
                    ·
                      rfl

theorem cell22_1459139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_1459139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459139 prefixEnd_1459139 := by exact prefixLift 1459139
  have htrace : WordTrace (prefixWord ++ tailWord_1459139) baseStart_1459139 baseEnd_1459139 := by
    simpa [prefixWord, tailWord_1459139, baseEnd_1459139] using wordTrace_append hprefix tailTrace_1459139
  have hstable : (prefixWord ++ tailWord_1459139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459139).length < 2 ^ (prefixWord ++ tailWord_1459139).sum := by decide
  have hdescent : baseEnd_1459139 < baseStart_1459139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459235 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 1, 4]
def baseStart_1459235 : Nat := 118140960795 + 1459235 * 2 ^ 59
def prefixEnd_1459235 : Nat := 4983230072969 + 3 ^ 40 * 1459235 * 2
def baseEnd_1459235 : Nat := 499525961909135646701071

theorem tailTrace_1459235 : CollatzResearch.WordTrace tailWord_1459235 prefixEnd_1459235 499525961909135646701071 := by
  unfold tailWord_1459235
  simp only [CollatzResearch.WordTrace]
  refine ⟨53222672868448287341891159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35481781912298858227927439 53222672868448287341891159)
  ·
    refine ⟨79834009302672431012836739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53222672868448287341891159 79834009302672431012836739)
    ·
      refine ⟨119751013954008646519255109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79834009302672431012836739 119751013954008646519255109)
      ·
        refine ⟨22453315116376621222360333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119751013954008646519255109 22453315116376621222360333)
        ·
          refine ⟨8419993168641232958385125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22453315116376621222360333 8419993168641232958385125)
          ·
            refine ⟨1578748719120231179697211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8419993168641232958385125 1578748719120231179697211)
            ·
              refine ⟨2368123078680346769545817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578748719120231179697211 2368123078680346769545817)
              ·
                refine ⟨1776092309010260077159363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2368123078680346769545817 1776092309010260077159363)
                ·
                  refine ⟨2664138463515390115739045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776092309010260077159363 2664138463515390115739045)
                  ·
                    refine ⟨499525961909135646701071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2664138463515390115739045 499525961909135646701071)
                    ·
                      rfl

theorem cell22_1459235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 4].length) (baseStart_1459235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459235 prefixEnd_1459235 := by exact prefixLift 1459235
  have htrace : WordTrace (prefixWord ++ tailWord_1459235) baseStart_1459235 baseEnd_1459235 := by
    simpa [prefixWord, tailWord_1459235, baseEnd_1459235] using wordTrace_append hprefix tailTrace_1459235
  have hstable : (prefixWord ++ tailWord_1459235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459235).length < 2 ^ (prefixWord ++ tailWord_1459235).sum := by decide
  have hdescent : baseEnd_1459235 < baseStart_1459235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459261 : List Nat := [1, 4, 1, 3, 1, 12]
def baseStart_1459261 : Nat := 118140960795 + 1459261 * 2 ^ 59
def prefixEnd_1459261 : Nat := 4983230072969 + 3 ^ 40 * 1459261 * 2
def baseEnd_1459261 : Nat := 6167097064697286982111

theorem tailTrace_1459261 : CollatzResearch.WordTrace tailWord_1459261 prefixEnd_1459261 6167097064697286982111 := by
  unfold tailWord_1459261
  simp only [CollatzResearch.WordTrace]
  refine ⟨53223621166354093782337637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35482414110902729188225091 53223621166354093782337637)
  ·
    refine ⟨9979428968691392584188307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53223621166354093782337637 9979428968691392584188307)
    ·
      refine ⟨14969143453037088876282461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9979428968691392584188307 14969143453037088876282461)
      ·
        refine ⟨5613428794888908328605923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14969143453037088876282461 5613428794888908328605923)
        ·
          refine ⟨8420143192333362492908885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5613428794888908328605923 8420143192333362492908885)
          ·
            refine ⟨6167097064697286982111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8420143192333362492908885 6167097064697286982111)
            ·
              rfl

theorem cell22_1459261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 12].length) (baseStart_1459261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459261 prefixEnd_1459261 := by exact prefixLift 1459261
  have htrace : WordTrace (prefixWord ++ tailWord_1459261) baseStart_1459261 baseEnd_1459261 := by
    simpa [prefixWord, tailWord_1459261, baseEnd_1459261] using wordTrace_append hprefix tailTrace_1459261
  have hstable : (prefixWord ++ tailWord_1459261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459261).length < 2 ^ (prefixWord ++ tailWord_1459261).sum := by decide
  have hdescent : baseEnd_1459261 < baseStart_1459261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459276 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1459276 : Nat := 118140960795 + 1459276 * 2 ^ 59
def prefixEnd_1459276 : Nat := 4983230072969 + 3 ^ 40 * 1459276 * 2
def baseEnd_1459276 : Nat := 499539997047025206425945

theorem tailTrace_1459276 : CollatzResearch.WordTrace tailWord_1459276 prefixEnd_1459276 499539997047025206425945 := by
  unfold tailWord_1459276
  simp only [CollatzResearch.WordTrace]
  refine ⟨26612084130649875672066841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35482778840866500896089121 26612084130649875672066841)
  ·
    refine ⟨19959063097987406754050131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26612084130649875672066841 19959063097987406754050131)
    ·
      refine ⟨29938594646981110131075197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19959063097987406754050131 29938594646981110131075197)
      ·
        refine ⟨11226972992617916299153199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29938594646981110131075197 11226972992617916299153199)
        ·
          refine ⟨16840459488926874448729799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11226972992617916299153199 16840459488926874448729799)
          ·
            refine ⟨25260689233390311673094699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16840459488926874448729799 25260689233390311673094699)
            ·
              refine ⟨37891033850085467509642049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25260689233390311673094699 37891033850085467509642049)
              ·
                refine ⟨28418275387564100632231537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37891033850085467509642049 28418275387564100632231537)
                ·
                  refine ⟨21313706540673075474173653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28418275387564100632231537 21313706540673075474173653)
                  ·
                    refine ⟨499539997047025206425945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21313706540673075474173653 499539997047025206425945)
                    ·
                      rfl

theorem cell22_1459276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1459276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459276 prefixEnd_1459276 := by exact prefixLift 1459276
  have htrace : WordTrace (prefixWord ++ tailWord_1459276) baseStart_1459276 baseEnd_1459276 := by
    simpa [prefixWord, tailWord_1459276, baseEnd_1459276] using wordTrace_append hprefix tailTrace_1459276
  have hstable : (prefixWord ++ tailWord_1459276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459276).length < 2 ^ (prefixWord ++ tailWord_1459276).sum := by decide
  have hdescent : baseEnd_1459276 < baseStart_1459276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459338 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1459338 : Nat := 118140960795 + 1459338 * 2 ^ 59
def prefixEnd_1459338 : Nat := 4983230072969 + 3 ^ 40 * 1459338 * 2
def baseEnd_1459338 : Nat := 499561220914077711375755

theorem tailTrace_1459338 : CollatzResearch.WordTrace tailWord_1459338 prefixEnd_1459338 499561220914077711375755 := by
  unfold tailWord_1459338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13306607396768783983222667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35484286391383423955260445 13306607396768783983222667)
  ·
    refine ⟨19959911095153175974834001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13306607396768783983222667 19959911095153175974834001)
    ·
      refine ⟨14969933321364881981125501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19959911095153175974834001 14969933321364881981125501)
      ·
        refine ⟨5613724995511830742922063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14969933321364881981125501 5613724995511830742922063)
        ·
          refine ⟨8420587493267746114383095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5613724995511830742922063 8420587493267746114383095)
          ·
            refine ⟨12630881239901619171574643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8420587493267746114383095 12630881239901619171574643)
            ·
              refine ⟨18946321859852428757361965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12630881239901619171574643 18946321859852428757361965)
              ·
                refine ⟨7104870697444660784010737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18946321859852428757361965 7104870697444660784010737)
                ·
                  refine ⟨5328653023083495588008053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7104870697444660784010737 5328653023083495588008053)
                  ·
                    refine ⟨499561220914077711375755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5328653023083495588008053 499561220914077711375755)
                    ·
                      rfl

theorem cell22_1459338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1459338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459338 prefixEnd_1459338 := by exact prefixLift 1459338
  have htrace : WordTrace (prefixWord ++ tailWord_1459338) baseStart_1459338 baseEnd_1459338 := by
    simpa [prefixWord, tailWord_1459338, baseEnd_1459338] using wordTrace_append hprefix tailTrace_1459338
  have hstable : (prefixWord ++ tailWord_1459338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459338).length < 2 ^ (prefixWord ++ tailWord_1459338).sum := by decide
  have hdescent : baseEnd_1459338 < baseStart_1459338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459385 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 6]
def baseStart_1459385 : Nat := 118140960795 + 1459385 * 2 ^ 59
def prefixEnd_1459385 : Nat := 4983230072969 + 3 ^ 40 * 1459385 * 2
def baseEnd_1459385 : Nat := 166525769991528418483537

theorem tailTrace_1459385 : CollatzResearch.WordTrace tailWord_1459385 prefixEnd_1459385 166525769991528418483537 := by
  unfold tailWord_1459385
  simp only [CollatzResearch.WordTrace]
  refine ⟨53228143817904862959851609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35485429211936575306567739 53228143817904862959851609)
  ·
    refine ⟨39921107863428647219888707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53228143817904862959851609 39921107863428647219888707)
    ·
      refine ⟨59881661795142970829833061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39921107863428647219888707 59881661795142970829833061)
      ·
        refine ⟨11227811586589307030593699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59881661795142970829833061 11227811586589307030593699)
        ·
          refine ⟨16841717379883960545890549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11227811586589307030593699 16841717379883960545890549)
          ·
            refine ⟨1578911004364121301177239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16841717379883960545890549 1578911004364121301177239)
            ·
              refine ⟨2368366506546181951765859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578911004364121301177239 2368366506546181951765859)
              ·
                refine ⟨3552549759819272927648789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368366506546181951765859 3552549759819272927648789)
                ·
                  refine ⟨166525769991528418483537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3552549759819272927648789 166525769991528418483537)
                  ·
                    rfl

theorem cell22_1459385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_1459385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459385 prefixEnd_1459385 := by exact prefixLift 1459385
  have htrace : WordTrace (prefixWord ++ tailWord_1459385) baseStart_1459385 baseEnd_1459385 := by
    simpa [prefixWord, tailWord_1459385, baseEnd_1459385] using wordTrace_append hprefix tailTrace_1459385
  have hstable : (prefixWord ++ tailWord_1459385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459385).length < 2 ^ (prefixWord ++ tailWord_1459385).sum := by decide
  have hdescent : baseEnd_1459385 < baseStart_1459385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459443 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 2, 6]
def baseStart_1459443 : Nat := 118140960795 + 1459443 * 2 ^ 59
def prefixEnd_1459443 : Nat := 4983230072969 + 3 ^ 40 * 1459443 * 2
def baseEnd_1459443 : Nat := 499597164559892437500433

theorem tailTrace_1459443 : CollatzResearch.WordTrace tailWord_1459443 prefixEnd_1459443 499597164559892437500433 := by
  unfold tailWord_1459443
  simp only [CollatzResearch.WordTrace]
  refine ⟨53230259251694738865462983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35486839501129825910308655 53230259251694738865462983)
  ·
    refine ⟨79845388877542108298194475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53230259251694738865462983 79845388877542108298194475)
    ·
      refine ⟨119768083316313162447291713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79845388877542108298194475 119768083316313162447291713)
      ·
        refine ⟨89826062487234871835468785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119768083316313162447291713 89826062487234871835468785)
        ·
          refine ⟨67369546865426153876601589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89826062487234871835468785 67369546865426153876601589)
          ·
            refine ⟨6315895018633701925931399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67369546865426153876601589 6315895018633701925931399)
            ·
              refine ⟨9473842527950552888897099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315895018633701925931399 9473842527950552888897099)
              ·
                refine ⟨14210763791925829333345649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9473842527950552888897099 14210763791925829333345649)
                ·
                  refine ⟨10658072843944372000009237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14210763791925829333345649 10658072843944372000009237)
                  ·
                    refine ⟨499597164559892437500433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10658072843944372000009237 499597164559892437500433)
                    ·
                      rfl

theorem cell22_1459443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_1459443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459443 prefixEnd_1459443 := by exact prefixLift 1459443
  have htrace : WordTrace (prefixWord ++ tailWord_1459443) baseStart_1459443 baseEnd_1459443 := by
    simpa [prefixWord, tailWord_1459443, baseEnd_1459443] using wordTrace_append hprefix tailTrace_1459443
  have hstable : (prefixWord ++ tailWord_1459443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459443).length < 2 ^ (prefixWord ++ tailWord_1459443).sum := by decide
  have hdescent : baseEnd_1459443 < baseStart_1459443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459473 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1459473 : Nat := 118140960795 + 1459473 * 2 ^ 59
def prefixEnd_1459473 : Nat := 4983230072969 + 3 ^ 40 * 1459473 * 2
def baseEnd_1459473 : Nat := 499607434172982359250341

theorem tailTrace_1459473 : CollatzResearch.WordTrace tailWord_1459473 prefixEnd_1459473 499607434172982359250341 := by
  unfold tailWord_1459473
  simp only [CollatzResearch.WordTrace]
  refine ⟨53231353441586053989055073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35487568961057369326036715 53231353441586053989055073)
  ·
    refine ⟨39923515081189540491791305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53231353441586053989055073 39923515081189540491791305)
    ·
      refine ⟨29942636310892155368843479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39923515081189540491791305 29942636310892155368843479)
      ·
        refine ⟨44913954466338233053265219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29942636310892155368843479 44913954466338233053265219)
        ·
          refine ⟨67370931699507349579897829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44913954466338233053265219 67370931699507349579897829)
          ·
            refine ⟨12632049693657628046230843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67370931699507349579897829 12632049693657628046230843)
            ·
              refine ⟨18948074540486442069346265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12632049693657628046230843 18948074540486442069346265)
              ·
                refine ⟨14211055905364831552009699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18948074540486442069346265 14211055905364831552009699)
                ·
                  refine ⟨21316583858047247328014549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14211055905364831552009699 21316583858047247328014549)
                  ·
                    refine ⟨499607434172982359250341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21316583858047247328014549 499607434172982359250341)
                    ·
                      rfl

theorem cell22_1459473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1459473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459473 prefixEnd_1459473 := by exact prefixLift 1459473
  have htrace : WordTrace (prefixWord ++ tailWord_1459473) baseStart_1459473 baseEnd_1459473 := by
    simpa [prefixWord, tailWord_1459473, baseEnd_1459473] using wordTrace_append hprefix tailTrace_1459473
  have hstable : (prefixWord ++ tailWord_1459473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459473).length < 2 ^ (prefixWord ++ tailWord_1459473).sum := by decide
  have hdescent : baseEnd_1459473 < baseStart_1459473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459479 : List Nat := [1, 1, 3, 4, 1, 1, 4, 3, 1, 3]
def baseStart_1459479 : Nat := 118140960795 + 1459479 * 2 ^ 59
def prefixEnd_1459479 : Nat := 4983230072969 + 3 ^ 40 * 1459479 * 2
def baseEnd_1459479 : Nat := 499609488095600343600323

theorem tailTrace_1459479 : CollatzResearch.WordTrace tailWord_1459479 prefixEnd_1459479 499609488095600343600323 := by
  unfold tailWord_1459479
  simp only [CollatzResearch.WordTrace]
  refine ⟨53231572279564317013773491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35487714853042878009182327 53231572279564317013773491)
  ·
    refine ⟨79847358419346475520660237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53231572279564317013773491 79847358419346475520660237)
    ·
      refine ⟨29942759407254928320247589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79847358419346475520660237 29942759407254928320247589)
      ·
        refine ⟨5614267388860299060046423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29942759407254928320247589 5614267388860299060046423)
        ·
          refine ⟨8421401083290448590069635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5614267388860299060046423 8421401083290448590069635)
          ·
            refine ⟨12632101624935672885104453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8421401083290448590069635 12632101624935672885104453)
            ·
              refine ⟨2368519054675438665957085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12632101624935672885104453 2368519054675438665957085)
              ·
                refine ⟨888194645503289499733907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2368519054675438665957085 888194645503289499733907)
                ·
                  refine ⟨1332291968254934249600861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888194645503289499733907 1332291968254934249600861)
                  ·
                    refine ⟨499609488095600343600323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1332291968254934249600861 499609488095600343600323)
                    ·
                      rfl

theorem cell22_1459479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_1459479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459479 prefixEnd_1459479 := by exact prefixLift 1459479
  have htrace : WordTrace (prefixWord ++ tailWord_1459479) baseStart_1459479 baseEnd_1459479 := by
    simpa [prefixWord, tailWord_1459479, baseEnd_1459479] using wordTrace_append hprefix tailTrace_1459479
  have hstable : (prefixWord ++ tailWord_1459479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459479).length < 2 ^ (prefixWord ++ tailWord_1459479).sum := by decide
  have hdescent : baseEnd_1459479 < baseStart_1459479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459552 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 4, 3]
def baseStart_1459552 : Nat := 118140960795 + 1459552 * 2 ^ 59
def prefixEnd_1459552 : Nat := 4983230072969 + 3 ^ 40 * 1459552 * 2
def baseEnd_1459552 : Nat := 499634477487452486525099

theorem tailTrace_1459552 : CollatzResearch.WordTrace tailWord_1459552 prefixEnd_1459552 499634477487452486525099 := by
  unfold tailWord_1459552
  simp only [CollatzResearch.WordTrace]
  refine ⟨26617117404149925240590455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35489489872199900320787273 26617117404149925240590455)
  ·
    refine ⟨39925676106224887860885683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26617117404149925240590455 39925676106224887860885683)
    ·
      refine ⟨59888514159337331791328525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39925676106224887860885683 59888514159337331791328525)
      ·
        refine ⟨22458192809751499421748197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59888514159337331791328525 22458192809751499421748197)
        ·
          refine ⟨4210911151828406141577787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22458192809751499421748197 4210911151828406141577787)
          ·
            refine ⟨6316366727742609212366681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210911151828406141577787 6316366727742609212366681)
            ·
              refine ⟨4737275045806956909275011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6316366727742609212366681 4737275045806956909275011)
              ·
                refine ⟨7105912568710435363912517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737275045806956909275011 7105912568710435363912517)
                ·
                  refine ⟨1332358606633206630733597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7105912568710435363912517 1332358606633206630733597)
                  ·
                    refine ⟨499634477487452486525099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1332358606633206630733597 499634477487452486525099)
                    ·
                      rfl

theorem cell22_1459552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_1459552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459552 prefixEnd_1459552 := by exact prefixLift 1459552
  have htrace : WordTrace (prefixWord ++ tailWord_1459552) baseStart_1459552 baseEnd_1459552 := by
    simpa [prefixWord, tailWord_1459552, baseEnd_1459552] using wordTrace_append hprefix tailTrace_1459552
  have hstable : (prefixWord ++ tailWord_1459552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459552).length < 2 ^ (prefixWord ++ tailWord_1459552).sum := by decide
  have hdescent : baseEnd_1459552 < baseStart_1459552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459565 : List Nat := [1, 5, 1, 1, 1, 3, 1, 9]
def baseStart_1459565 : Nat := 118140960795 + 1459565 * 2 ^ 59
def prefixEnd_1459565 : Nat := 4983230072969 + 3 ^ 40 * 1459565 * 2
def baseEnd_1459565 : Nat := 55515436405902753994451

theorem tailTrace_1459565 : CollatzResearch.WordTrace tailWord_1459565 prefixEnd_1459565 55515436405902753994451 := by
  unfold tailWord_1459565
  simp only [CollatzResearch.WordTrace]
  refine ⟨53234708957252753701404149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35489805971501835800936099 53234708957252753701404149)
  ·
    refine ⟨4990753964742445659506639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53234708957252753701404149 4990753964742445659506639)
    ·
      refine ⟨7486130947113668489259959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4990753964742445659506639 7486130947113668489259959)
      ·
        refine ⟨11229196420670502733889939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7486130947113668489259959 11229196420670502733889939)
        ·
          refine ⟨16843794631005754100834909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11229196420670502733889939 16843794631005754100834909)
          ·
            refine ⟨6316422986627157787813091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16843794631005754100834909 6316422986627157787813091)
            ·
              refine ⟨9474634479940736681719637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316422986627157787813091 9474634479940736681719637)
              ·
                refine ⟨55515436405902753994451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9474634479940736681719637 55515436405902753994451)
                ·
                  rfl

theorem cell22_1459565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 9].length) (baseStart_1459565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459565 prefixEnd_1459565 := by exact prefixLift 1459565
  have htrace : WordTrace (prefixWord ++ tailWord_1459565) baseStart_1459565 baseEnd_1459565 := by
    simpa [prefixWord, tailWord_1459565, baseEnd_1459565] using wordTrace_append hprefix tailTrace_1459565
  have hstable : (prefixWord ++ tailWord_1459565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459565).length < 2 ^ (prefixWord ++ tailWord_1459565).sum := by decide
  have hdescent : baseEnd_1459565 < baseStart_1459565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459569 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 2, 3]
def baseStart_1459569 : Nat := 118140960795 + 1459569 * 2 ^ 59
def prefixEnd_1459569 : Nat := 4983230072969 + 3 ^ 40 * 1459569 * 2
def baseEnd_1459569 : Nat := 499640296934870108850047

theorem tailTrace_1459569 : CollatzResearch.WordTrace tailWord_1459569 prefixEnd_1459569 499640296934870108850047 := by
  unfold tailWord_1459569
  simp only [CollatzResearch.WordTrace]
  refine ⟨53234854849238262384549761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35489903232825508256366507 53234854849238262384549761)
  ·
    refine ⟨39926141136928696788412321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53234854849238262384549761 39926141136928696788412321)
    ·
      refine ⟨29944605852696522591309241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39926141136928696788412321 29944605852696522591309241)
      ·
        refine ⟨22458454389522391943481931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29944605852696522591309241 22458454389522391943481931)
        ·
          refine ⟨33687681584283587915222897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22458454389522391943481931 33687681584283587915222897)
          ·
            refine ⟨25265761188212690936417173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33687681584283587915222897 25265761188212690936417173)
            ·
              refine ⟨1184332555697469887644555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25265761188212690936417173 1184332555697469887644555)
              ·
                refine ⟨1776498833546204831466833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184332555697469887644555 1776498833546204831466833)
                ·
                  refine ⟨1332374125159653623600125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1776498833546204831466833 1332374125159653623600125)
                  ·
                    refine ⟨499640296934870108850047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1332374125159653623600125 499640296934870108850047)
                    ·
                      rfl

theorem cell22_1459569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_1459569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459569 prefixEnd_1459569 := by exact prefixLift 1459569
  have htrace : WordTrace (prefixWord ++ tailWord_1459569) baseStart_1459569 baseEnd_1459569 := by
    simpa [prefixWord, tailWord_1459569, baseEnd_1459569] using wordTrace_append hprefix tailTrace_1459569
  have hstable : (prefixWord ++ tailWord_1459569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459569).length < 2 ^ (prefixWord ++ tailWord_1459569).sum := by decide
  have hdescent : baseEnd_1459569 < baseStart_1459569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459655 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 8]
def baseStart_1459655 : Nat := 118140960795 + 1459655 * 2 ^ 59
def prefixEnd_1459655 : Nat := 4983230072969 + 3 ^ 40 * 1459655 * 2
def baseEnd_1459655 : Nat := 166556578830798183733261

theorem tailTrace_1459655 : CollatzResearch.WordTrace tailWord_1459655 prefixEnd_1459655 166556578830798183733261 := by
  unfold tailWord_1459655
  simp only [CollatzResearch.WordTrace]
  refine ⟨53237991526926699072180419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35491994351284466048120279 53237991526926699072180419)
  ·
    refine ⟨79856987290390048608270629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53237991526926699072180419 79856987290390048608270629)
    ·
      refine ⟨14973185116948134114050743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79856987290390048608270629 14973185116948134114050743)
      ·
        refine ⟨22459777675422201171076115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14973185116948134114050743 22459777675422201171076115)
        ·
          refine ⟨33689666513133301756614173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22459777675422201171076115 33689666513133301756614173)
          ·
            refine ⟨12633624942424988158730315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33689666513133301756614173 12633624942424988158730315)
            ·
              refine ⟨18950437413637482238095473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12633624942424988158730315 18950437413637482238095473)
              ·
                refine ⟨14212828060228111678571605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18950437413637482238095473 14212828060228111678571605)
                ·
                  refine ⟨166556578830798183733261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14212828060228111678571605 166556578830798183733261)
                  ·
                    rfl

theorem cell22_1459655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 8].length) (baseStart_1459655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459655 prefixEnd_1459655 := by exact prefixLift 1459655
  have htrace : WordTrace (prefixWord ++ tailWord_1459655) baseStart_1459655 baseEnd_1459655 := by
    simpa [prefixWord, tailWord_1459655, baseEnd_1459655] using wordTrace_append hprefix tailTrace_1459655
  have hstable : (prefixWord ++ tailWord_1459655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459655).length < 2 ^ (prefixWord ++ tailWord_1459655).sum := by decide
  have hdescent : baseEnd_1459655 < baseStart_1459655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459719 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1459719 : Nat := 118140960795 + 1459719 * 2 ^ 59
def prefixEnd_1459719 : Nat := 4983230072969 + 3 ^ 40 * 1459719 * 2
def baseEnd_1459719 : Nat := 499691645000319717599587

theorem tailTrace_1459719 : CollatzResearch.WordTrace tailWord_1459719 prefixEnd_1459719 499691645000319717599587 := by
  unfold tailWord_1459719
  simp only [CollatzResearch.WordTrace]
  refine ⟨53240325798694838002510211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35493550532463225335006807 53240325798694838002510211)
  ·
    refine ⟨79860488698042257003765317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53240325798694838002510211 79860488698042257003765317)
    ·
      refine ⟨14973841630882923188205997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79860488698042257003765317 14973841630882923188205997)
      ·
        refine ⟨5615190611581096195577249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14973841630882923188205997 5615190611581096195577249)
        ·
          refine ⟨4211392958685822146682937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5615190611581096195577249 4211392958685822146682937)
          ·
            refine ⟨3158544719014366610012203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4211392958685822146682937 3158544719014366610012203)
            ·
              refine ⟨4737817078521549915018305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158544719014366610012203 4737817078521549915018305)
              ·
                refine ⟨3553362808891162436263729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4737817078521549915018305 3553362808891162436263729)
                ·
                  refine ⟨2665022106668371827197797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553362808891162436263729 2665022106668371827197797)
                  ·
                    refine ⟨499691645000319717599587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665022106668371827197797 499691645000319717599587)
                    ·
                      rfl

theorem cell22_1459719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1459719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459719 prefixEnd_1459719 := by exact prefixLift 1459719
  have htrace : WordTrace (prefixWord ++ tailWord_1459719) baseStart_1459719 baseEnd_1459719 := by
    simpa [prefixWord, tailWord_1459719, baseEnd_1459719] using wordTrace_append hprefix tailTrace_1459719
  have hstable : (prefixWord ++ tailWord_1459719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459719).length < 2 ^ (prefixWord ++ tailWord_1459719).sum := by decide
  have hdescent : baseEnd_1459719 < baseStart_1459719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459742 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1459742 : Nat := 118140960795 + 1459742 * 2 ^ 59
def prefixEnd_1459742 : Nat := 4983230072969 + 3 ^ 40 * 1459742 * 2
def baseEnd_1459742 : Nat := 499699518370355324274517

theorem tailTrace_1459742 : CollatzResearch.WordTrace tailWord_1459742 prefixEnd_1459742 499699518370355324274517 := by
  unfold tailWord_1459742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6655145584701439116324685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35494109785074341953731653 6655145584701439116324685)
  ·
    refine ⟨2495679594263039668621757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6655145584701439116324685 2495679594263039668621757)
    ·
      refine ⟨935879847848639875733159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2495679594263039668621757 935879847848639875733159)
      ·
        refine ⟨1403819771772959813599739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935879847848639875733159 1403819771772959813599739)
        ·
          refine ⟨2105729657659439720399609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403819771772959813599739 2105729657659439720399609)
          ·
            refine ⟨1579297243244579790299707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2105729657659439720399609 1579297243244579790299707)
            ·
              refine ⟨2368945864866869685449561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579297243244579790299707 2368945864866869685449561)
              ·
                refine ⟨1776709398650152264087171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2368945864866869685449561 1776709398650152264087171)
                ·
                  refine ⟨2665064097975228396130757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776709398650152264087171 2665064097975228396130757)
                  ·
                    refine ⟨499699518370355324274517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665064097975228396130757 499699518370355324274517)
                    ·
                      rfl

theorem cell22_1459742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1459742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459742 prefixEnd_1459742 := by exact prefixLift 1459742
  have htrace : WordTrace (prefixWord ++ tailWord_1459742) baseStart_1459742 baseEnd_1459742 := by
    simpa [prefixWord, tailWord_1459742, baseEnd_1459742] using wordTrace_append hprefix tailTrace_1459742
  have hstable : (prefixWord ++ tailWord_1459742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459742).length < 2 ^ (prefixWord ++ tailWord_1459742).sum := by decide
  have hdescent : baseEnd_1459742 < baseStart_1459742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459783 : List Nat := [1, 1, 4, 1, 5, 1, 1, 4, 1, 3]
def baseStart_1459783 : Nat := 118140960795 + 1459783 * 2 ^ 59
def prefixEnd_1459783 : Nat := 4983230072969 + 3 ^ 40 * 1459783 * 2
def baseEnd_1459783 : Nat := 499713553508244883999391

theorem tailTrace_1459783 : CollatzResearch.WordTrace tailWord_1459783 prefixEnd_1459783 499713553508244883999391 := by
  unfold tailWord_1459783
  simp only [CollatzResearch.WordTrace]
  refine ⟨53242660070462976932840003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35495106713641984621893335 53242660070462976932840003)
  ·
    refine ⟨79863990105694465399260005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53242660070462976932840003 79863990105694465399260005)
    ·
      refine ⟨14974498144817712262361251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79863990105694465399260005 14974498144817712262361251)
      ·
        refine ⟨22461747217226568393541877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14974498144817712262361251 22461747217226568393541877)
        ·
          refine ⟨2105788801614990786894551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22461747217226568393541877 2105788801614990786894551)
          ·
            refine ⟨3158683202422486180341827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105788801614990786894551 3158683202422486180341827)
            ·
              refine ⟨4738024803633729270512741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158683202422486180341827 4738024803633729270512741)
              ·
                refine ⟨888379650681324238221139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4738024803633729270512741 888379650681324238221139)
                ·
                  refine ⟨1332569476021986357331709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888379650681324238221139 1332569476021986357331709)
                  ·
                    refine ⟨499713553508244883999391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1332569476021986357331709 499713553508244883999391)
                    ·
                      rfl

theorem cell22_1459783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_1459783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459783 prefixEnd_1459783 := by exact prefixLift 1459783
  have htrace : WordTrace (prefixWord ++ tailWord_1459783) baseStart_1459783 baseEnd_1459783 := by
    simpa [prefixWord, tailWord_1459783, baseEnd_1459783] using wordTrace_append hprefix tailTrace_1459783
  have hstable : (prefixWord ++ tailWord_1459783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459783).length < 2 ^ (prefixWord ++ tailWord_1459783).sum := by decide
  have hdescent : baseEnd_1459783 < baseStart_1459783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459792 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_1459792 : Nat := 118140960795 + 1459792 * 2 ^ 59
def prefixEnd_1459792 : Nat := 4983230072969 + 3 ^ 40 * 1459792 * 2
def baseEnd_1459792 : Nat := 499716634392171860524363

theorem tailTrace_1459792 : CollatzResearch.WordTrace tailWord_1459792 prefixEnd_1459792 499716634392171860524363 := by
  unfold tailWord_1459792
  simp only [CollatzResearch.WordTrace]
  refine ⟨26621494163715185734958815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35495325551620247646611753 26621494163715185734958815)
  ·
    refine ⟨39932241245572778602438223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26621494163715185734958815 39932241245572778602438223)
    ·
      refine ⟨59898361868359167903657335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39932241245572778602438223 59898361868359167903657335)
      ·
        refine ⟨89847542802538751855486003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59898361868359167903657335 89847542802538751855486003)
        ·
          refine ⟨134771314203808127783229005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89847542802538751855486003 134771314203808127783229005)
          ·
            refine ⟨50539242826428047918710877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134771314203808127783229005 50539242826428047918710877)
            ·
              refine ⟨18952216059910517969516579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50539242826428047918710877 18952216059910517969516579)
              ·
                refine ⟨28428324089865776954274869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18952216059910517969516579 28428324089865776954274869)
                ·
                  refine ⟨2665155383424916589463269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28428324089865776954274869 2665155383424916589463269)
                  ·
                    refine ⟨499716634392171860524363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665155383424916589463269 499716634392171860524363)
                    ·
                      rfl

theorem cell22_1459792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_1459792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459792 prefixEnd_1459792 := by exact prefixLift 1459792
  have htrace : WordTrace (prefixWord ++ tailWord_1459792) baseStart_1459792 baseEnd_1459792 := by
    simpa [prefixWord, tailWord_1459792, baseEnd_1459792] using wordTrace_append hprefix tailTrace_1459792
  have hstable : (prefixWord ++ tailWord_1459792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459792).length < 2 ^ (prefixWord ++ tailWord_1459792).sum := by decide
  have hdescent : baseEnd_1459792 < baseStart_1459792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459794 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1459794 : Nat := 118140960795 + 1459794 * 2 ^ 59
def prefixEnd_1459794 : Nat := 4983230072969 + 3 ^ 40 * 1459794 * 2
def baseEnd_1459794 : Nat := 499717319033044521974357

theorem tailTrace_1459794 : CollatzResearch.WordTrace tailWord_1459794 prefixEnd_1459794 499717319033044521974357 := by
  unfold tailWord_1459794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13310765318355781452872609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35495374182282083874326957 13310765318355781452872609)
  ·
    refine ⟨9983073988766836089654457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13310765318355781452872609 9983073988766836089654457)
    ·
      refine ⟨7487305491575127067240843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9983073988766836089654457 7487305491575127067240843)
      ·
        refine ⟨11230958237362690600861265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7487305491575127067240843 11230958237362690600861265)
        ·
          refine ⟨8423218678022017950645949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11230958237362690600861265 8423218678022017950645949)
          ·
            refine ⟨3158707004258256731492231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8423218678022017950645949 3158707004258256731492231)
            ·
              refine ⟨4738060506387385097238347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158707004258256731492231 4738060506387385097238347)
              ·
                refine ⟨7107090759581077645857521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738060506387385097238347 7107090759581077645857521)
                ·
                  refine ⟨5330318069685808234393141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7107090759581077645857521 5330318069685808234393141)
                  ·
                    refine ⟨499717319033044521974357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5330318069685808234393141 499717319033044521974357)
                    ·
                      rfl

theorem cell22_1459794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1459794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459794 prefixEnd_1459794 := by exact prefixLift 1459794
  have htrace : WordTrace (prefixWord ++ tailWord_1459794) baseStart_1459794 baseEnd_1459794 := by
    simpa [prefixWord, tailWord_1459794, baseEnd_1459794] using wordTrace_append hprefix tailTrace_1459794
  have hstable : (prefixWord ++ tailWord_1459794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459794).length < 2 ^ (prefixWord ++ tailWord_1459794).sum := by decide
  have hdescent : baseEnd_1459794 < baseStart_1459794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459809 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1459809 : Nat := 118140960795 + 1459809 * 2 ^ 59
def prefixEnd_1459809 : Nat := 4983230072969 + 3 ^ 40 * 1459809 * 2
def baseEnd_1459809 : Nat := 499722453839589482849311

theorem tailTrace_1459809 : CollatzResearch.WordTrace tailWord_1459809 prefixEnd_1459809 499722453839589482849311 := by
  unfold tailWord_1459809
  simp only [CollatzResearch.WordTrace]
  refine ⟨53243608368368783373286481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35495738912245855582190987 53243608368368783373286481)
  ·
    refine ⟨39932706276276587529964861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53243608368368783373286481 39932706276276587529964861)
    ·
      refine ⟨14974764853603720323736823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39932706276276587529964861 14974764853603720323736823)
      ·
        refine ⟨22462147280405580485605235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14974764853603720323736823 22462147280405580485605235)
        ·
          refine ⟨33693220920608370728407853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22462147280405580485605235 33693220920608370728407853)
          ·
            refine ⟨12634957845228139023152945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33693220920608370728407853 12634957845228139023152945)
            ·
              refine ⟨9476218383921104267364709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12634957845228139023152945 9476218383921104267364709)
              ·
                refine ⟨1776790946985207050130883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9476218383921104267364709 1776790946985207050130883)
                ·
                  refine ⟨2665186420477810575196325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776790946985207050130883 2665186420477810575196325)
                  ·
                    refine ⟨499722453839589482849311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665186420477810575196325 499722453839589482849311)
                    ·
                      rfl

theorem cell22_1459809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1459809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459809 prefixEnd_1459809 := by exact prefixLift 1459809
  have htrace : WordTrace (prefixWord ++ tailWord_1459809) baseStart_1459809 baseEnd_1459809 := by
    simpa [prefixWord, tailWord_1459809, baseEnd_1459809] using wordTrace_append hprefix tailTrace_1459809
  have hstable : (prefixWord ++ tailWord_1459809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459809).length < 2 ^ (prefixWord ++ tailWord_1459809).sum := by decide
  have hdescent : baseEnd_1459809 < baseStart_1459809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459826 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1459826 : Nat := 118140960795 + 1459826 * 2 ^ 59
def prefixEnd_1459826 : Nat := 4983230072969 + 3 ^ 40 * 1459826 * 2
def baseEnd_1459826 : Nat := 499728273287007105174259

theorem tailTrace_1459826 : CollatzResearch.WordTrace tailWord_1459826 prefixEnd_1459826 499728273287007105174259 := by
  unfold tailWord_1459826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311057102326798819163833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35496152272871463517770221 13311057102326798819163833)
  ·
    refine ⟨9983292826745099114372875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13311057102326798819163833 9983292826745099114372875)
    ·
      refine ⟨14974939240117648671559313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9983292826745099114372875 14974939240117648671559313)
      ·
        refine ⟨11231204430088236503669485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14974939240117648671559313 11231204430088236503669485)
        ·
          refine ⟨4211701661283088688876057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11231204430088236503669485 4211701661283088688876057)
          ·
            refine ⟨3158776245962316516657043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4211701661283088688876057 3158776245962316516657043)
            ·
              refine ⟨4738164368943474774985565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158776245962316516657043 4738164368943474774985565)
              ·
                refine ⟨1776811638353803040619587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4738164368943474774985565 1776811638353803040619587)
                ·
                  refine ⟨2665217457530704560929381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776811638353803040619587 2665217457530704560929381)
                  ·
                    refine ⟨499728273287007105174259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665217457530704560929381 499728273287007105174259)
                    ·
                      rfl

theorem cell22_1459826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1459826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459826 prefixEnd_1459826 := by exact prefixLift 1459826
  have htrace : WordTrace (prefixWord ++ tailWord_1459826) baseStart_1459826 baseEnd_1459826 := by
    simpa [prefixWord, tailWord_1459826, baseEnd_1459826] using wordTrace_append hprefix tailTrace_1459826
  have hstable : (prefixWord ++ tailWord_1459826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459826).length < 2 ^ (prefixWord ++ tailWord_1459826).sum := by decide
  have hdescent : baseEnd_1459826 < baseStart_1459826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459841 : List Nat := [1, 2, 4, 2, 1, 2, 2, 4, 4]
def baseStart_1459841 : Nat := 118140960795 + 1459841 * 2 ^ 59
def prefixEnd_1459841 : Nat := 4983230072969 + 3 ^ 40 * 1459841 * 2
def baseEnd_1459841 : Nat := 166577802697850688683071

theorem tailTrace_1459841 : CollatzResearch.WordTrace tailWord_1459841 prefixEnd_1459841 166577802697850688683071 := by
  unfold tailWord_1459841
  simp only [CollatzResearch.WordTrace]
  refine ⟨53244775504252852838451377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35496517002835235225634251 53244775504252852838451377)
  ·
    refine ⟨39933581628189639628838533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53244775504252852838451377 39933581628189639628838533)
    ·
      refine ⟨7487546555285557430407225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39933581628189639628838533 7487546555285557430407225)
      ·
        refine ⟨5615659916464168072805419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7487546555285557430407225 5615659916464168072805419)
        ·
          refine ⟨8423489874696252109208129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615659916464168072805419 8423489874696252109208129)
          ·
            refine ⟨6317617406022189081906097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8423489874696252109208129 6317617406022189081906097)
            ·
              refine ⟨4738213054516641811429573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6317617406022189081906097 4738213054516641811429573)
              ·
                refine ⟨888414947721870339643045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4738213054516641811429573 888414947721870339643045)
                ·
                  refine ⟨166577802697850688683071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 888414947721870339643045 166577802697850688683071)
                  ·
                    rfl

theorem cell22_1459841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 4].length) (baseStart_1459841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459841 prefixEnd_1459841 := by exact prefixLift 1459841
  have htrace : WordTrace (prefixWord ++ tailWord_1459841) baseStart_1459841 baseEnd_1459841 := by
    simpa [prefixWord, tailWord_1459841, baseEnd_1459841] using wordTrace_append hprefix tailTrace_1459841
  have hstable : (prefixWord ++ tailWord_1459841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459841).length < 2 ^ (prefixWord ++ tailWord_1459841).sum := by decide
  have hdescent : baseEnd_1459841 < baseStart_1459841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459852 : List Nat := [2, 2, 1, 2, 1, 1, 4, 9]
def baseStart_1459852 : Nat := 118140960795 + 1459852 * 2 ^ 59
def prefixEnd_1459852 : Nat := 4983230072969 + 3 ^ 40 * 1459852 * 2
def baseEnd_1459852 : Nat := 55526352624261300447131

theorem tailTrace_1459852 : CollatzResearch.WordTrace tailWord_1459852 prefixEnd_1459852 55526352624261300447131 := by
  unfold tailWord_1459852
  simp only [CollatzResearch.WordTrace]
  refine ⟨26622588353606500858550905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35496784471475334478067873 26622588353606500858550905)
  ·
    refine ⟨19966941265204875643913179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26622588353606500858550905 19966941265204875643913179)
    ·
      refine ⟨29950411897807313465869769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19966941265204875643913179 29950411897807313465869769)
      ·
        refine ⟨22462808923355485099402327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29950411897807313465869769 22462808923355485099402327)
        ·
          refine ⟨33694213385033227649103491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22462808923355485099402327 33694213385033227649103491)
          ·
            refine ⟨50541320077549841473655237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33694213385033227649103491 50541320077549841473655237)
            ·
              refine ⟨9476497514540595276310357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50541320077549841473655237 9476497514540595276310357)
              ·
                refine ⟨55526352624261300447131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9476497514540595276310357 55526352624261300447131)
                ·
                  rfl

theorem cell22_1459852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 9].length) (baseStart_1459852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459852 prefixEnd_1459852 := by exact prefixLift 1459852
  have htrace : WordTrace (prefixWord ++ tailWord_1459852) baseStart_1459852 baseEnd_1459852 := by
    simpa [prefixWord, tailWord_1459852, baseEnd_1459852] using wordTrace_append hprefix tailTrace_1459852
  have hstable : (prefixWord ++ tailWord_1459852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459852).length < 2 ^ (prefixWord ++ tailWord_1459852).sum := by decide
  have hdescent : baseEnd_1459852 < baseStart_1459852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459854 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1459854 : Nat := 118140960795 + 1459854 * 2 ^ 59
def prefixEnd_1459854 : Nat := 4983230072969 + 3 ^ 40 * 1459854 * 2
def baseEnd_1459854 : Nat := 499737858259224365474173

theorem tailTrace_1459854 : CollatzResearch.WordTrace tailWord_1459854 prefixEnd_1459854 499737858259224365474173 := by
  unfold tailWord_1459854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6655656206650719507334327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35496833102137170705783077 6655656206650719507334327)
  ·
    refine ⟨9983484309976079261001491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6655656206650719507334327 9983484309976079261001491)
    ·
      refine ⟨14975226464964118891502237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9983484309976079261001491 14975226464964118891502237)
      ·
        refine ⟨5615709924361544584313339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14975226464964118891502237 5615709924361544584313339)
        ·
          refine ⟨8423564886542316876470009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5615709924361544584313339 8423564886542316876470009)
          ·
            refine ⟨6317673664906737657352507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8423564886542316876470009 6317673664906737657352507)
            ·
              refine ⟨9476510497360106486028761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6317673664906737657352507 9476510497360106486028761)
              ·
                refine ⟨7107382873020079864521571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9476510497360106486028761 7107382873020079864521571)
                ·
                  refine ⟨10661074309530119796782357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7107382873020079864521571 10661074309530119796782357)
                  ·
                    refine ⟨499737858259224365474173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10661074309530119796782357 499737858259224365474173)
                    ·
                      rfl

theorem cell22_1459854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1459854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459854 prefixEnd_1459854 := by exact prefixLift 1459854
  have htrace : WordTrace (prefixWord ++ tailWord_1459854) baseStart_1459854 baseEnd_1459854 := by
    simpa [prefixWord, tailWord_1459854, baseEnd_1459854] using wordTrace_append hprefix tailTrace_1459854
  have hstable : (prefixWord ++ tailWord_1459854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459854).length < 2 ^ (prefixWord ++ tailWord_1459854).sum := by decide
  have hdescent : baseEnd_1459854 < baseStart_1459854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459991 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 1, 5]
def baseStart_1459991 : Nat := 118140960795 + 1459991 * 2 ^ 59
def prefixEnd_1459991 : Nat := 4983230072969 + 3 ^ 40 * 1459991 * 2
def baseEnd_1459991 : Nat := 499784756159001674798753

theorem tailTrace_1459991 : CollatzResearch.WordTrace tailWord_1459991 prefixEnd_1459991 499784756159001674798753 := by
  unfold tailWord_1459991
  simp only [CollatzResearch.WordTrace]
  refine ⟨53250246453709428456411827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35500164302472952304274551 53250246453709428456411827)
  ·
    refine ⟨79875369680564142684617741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53250246453709428456411827 79875369680564142684617741)
    ·
      refine ⟨29953263630211553506731653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79875369680564142684617741 29953263630211553506731653)
      ·
        refine ⟨5616236930664666282512185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29953263630211553506731653 5616236930664666282512185)
        ·
          refine ⟨4212177697998499711884139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5616236930664666282512185 4212177697998499711884139)
          ·
            refine ⟨6318266546997749567826209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212177697998499711884139 6318266546997749567826209)
            ·
              refine ⟨4738699910248312175869657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6318266546997749567826209 4738699910248312175869657)
              ·
                refine ⟨3554024932686234131902243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4738699910248312175869657 3554024932686234131902243)
                ·
                  refine ⟨5331037399029351197853365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554024932686234131902243 5331037399029351197853365)
                  ·
                    refine ⟨499784756159001674798753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5331037399029351197853365 499784756159001674798753)
                    ·
                      rfl

theorem cell22_1459991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_1459991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1459991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1459991 prefixEnd_1459991 := by exact prefixLift 1459991
  have htrace : WordTrace (prefixWord ++ tailWord_1459991) baseStart_1459991 baseEnd_1459991 := by
    simpa [prefixWord, tailWord_1459991, baseEnd_1459991] using wordTrace_append hprefix tailTrace_1459991
  have hstable : (prefixWord ++ tailWord_1459991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459991).length < 2 ^ (prefixWord ++ tailWord_1459991).sum := by decide
  have hdescent : baseEnd_1459991 < baseStart_1459991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460008 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1460008 : Nat := 118140960795 + 1460008 * 2 ^ 59
def prefixEnd_1460008 : Nat := 4983230072969 + 3 ^ 40 * 1460008 * 2
def baseEnd_1460008 : Nat := 499790575606419297123701

theorem tailTrace_1460008 : CollatzResearch.WordTrace tailWord_1460008 prefixEnd_1460008 499790575606419297123701 := by
  unfold tailWord_1460008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26625433247323920179890339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35500577663098560239853785 26625433247323920179890339)
  ·
    refine ⟨39938149870985880269835509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26625433247323920179890339 39938149870985880269835509)
    ·
      refine ⟨3744201550404926275297079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39938149870985880269835509 3744201550404926275297079)
      ·
        refine ⟨5616302325607389412945619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3744201550404926275297079 5616302325607389412945619)
        ·
          refine ⟨8424453488411084119418429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616302325607389412945619 8424453488411084119418429)
          ·
            refine ⟨3159170058154156544781911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8424453488411084119418429 3159170058154156544781911)
            ·
              refine ⟨4738755087231234817172867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159170058154156544781911 4738755087231234817172867)
              ·
                refine ⟨7108132630846852225759301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738755087231234817172867 7108132630846852225759301)
                ·
                  refine ⟨1332774868283784792329869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7108132630846852225759301 1332774868283784792329869)
                  ·
                    refine ⟨499790575606419297123701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1332774868283784792329869 499790575606419297123701)
                    ·
                      rfl

theorem cell22_1460008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1460008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460008 prefixEnd_1460008 := by exact prefixLift 1460008
  have htrace : WordTrace (prefixWord ++ tailWord_1460008) baseStart_1460008 baseEnd_1460008 := by
    simpa [prefixWord, tailWord_1460008, baseEnd_1460008] using wordTrace_append hprefix tailTrace_1460008
  have hstable : (prefixWord ++ tailWord_1460008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460008).length < 2 ^ (prefixWord ++ tailWord_1460008).sum := by decide
  have hdescent : baseEnd_1460008 < baseStart_1460008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460025 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 1, 5]
def baseStart_1460025 : Nat := 118140960795 + 1460025 * 2 ^ 59
def prefixEnd_1460025 : Nat := 4983230072969 + 3 ^ 40 * 1460025 * 2
def baseEnd_1460025 : Nat := 499796395053836919448649

theorem tailTrace_1460025 : CollatzResearch.WordTrace tailWord_1460025 prefixEnd_1460025 499796395053836919448649 := by
  unfold tailWord_1460025
  simp only [CollatzResearch.WordTrace]
  refine ⟨53251486535586252263149529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35500991023724168175433019 53251486535586252263149529)
  ·
    refine ⟨39938614901689689197362147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53251486535586252263149529 39938614901689689197362147)
    ·
      refine ⟨59907922352534533796043221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39938614901689689197362147 59907922352534533796043221)
      ·
        refine ⟨1404091930137528135844763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 59907922352534533796043221 1404091930137528135844763)
        ·
          refine ⟨2106137895206292203767145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404091930137528135844763 2106137895206292203767145)
          ·
            refine ⟨1579603421404719152825359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2106137895206292203767145 1579603421404719152825359)
            ·
              refine ⟨2369405132107078729238039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579603421404719152825359 2369405132107078729238039)
              ·
                refine ⟨3554107698160618093857059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369405132107078729238039 3554107698160618093857059)
                ·
                  refine ⟨5331161547240927140785589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554107698160618093857059 5331161547240927140785589)
                  ·
                    refine ⟨499796395053836919448649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5331161547240927140785589 499796395053836919448649)
                    ·
                      rfl

theorem cell22_1460025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_1460025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460025 prefixEnd_1460025 := by exact prefixLift 1460025
  have htrace : WordTrace (prefixWord ++ tailWord_1460025) baseStart_1460025 baseEnd_1460025 := by
    simpa [prefixWord, tailWord_1460025, baseEnd_1460025] using wordTrace_append hprefix tailTrace_1460025
  have hstable : (prefixWord ++ tailWord_1460025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460025).length < 2 ^ (prefixWord ++ tailWord_1460025).sum := by decide
  have hdescent : baseEnd_1460025 < baseStart_1460025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460079 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 10]
def baseStart_1460079 : Nat := 118140960795 + 1460079 * 2 ^ 59
def prefixEnd_1460079 : Nat := 4983230072969 + 3 ^ 40 * 1460079 * 2
def baseEnd_1460079 : Nat := 499814880357398778598483

theorem tailTrace_1460079 : CollatzResearch.WordTrace tailWord_1460079 prefixEnd_1460079 499814880357398778598483 := by
  unfold tailWord_1460079
  simp only [CollatzResearch.WordTrace]
  refine ⟨53253456077390619485615291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35502304051593746323743527 53253456077390619485615291)
  ·
    refine ⟨79880184116085929228422937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53253456077390619485615291 79880184116085929228422937)
    ·
      refine ⟨59910138087064446921317203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79880184116085929228422937 59910138087064446921317203)
      ·
        refine ⟨89865207130596670381975805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59910138087064446921317203 89865207130596670381975805)
        ·
          refine ⟨33699452673973751393240927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89865207130596670381975805 33699452673973751393240927)
          ·
            refine ⟨50549179010960627089861391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33699452673973751393240927 50549179010960627089861391)
            ·
              refine ⟨75823768516440940634792087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50549179010960627089861391 75823768516440940634792087)
              ·
                refine ⟨113735652774661410952188131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75823768516440940634792087 113735652774661410952188131)
                ·
                  refine ⟨170603479161992116428282197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113735652774661410952188131 170603479161992116428282197)
                  ·
                    refine ⟨499814880357398778598483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 170603479161992116428282197 499814880357398778598483)
                    ·
                      rfl

theorem cell22_1460079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_1460079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460079 prefixEnd_1460079 := by exact prefixLift 1460079
  have htrace : WordTrace (prefixWord ++ tailWord_1460079) baseStart_1460079 baseEnd_1460079 := by
    simpa [prefixWord, tailWord_1460079, baseEnd_1460079] using wordTrace_append hprefix tailTrace_1460079
  have hstable : (prefixWord ++ tailWord_1460079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460079).length < 2 ^ (prefixWord ++ tailWord_1460079).sum := by decide
  have hdescent : baseEnd_1460079 < baseStart_1460079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460096 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_1460096 : Nat := 118140960795 + 1460096 * 2 ^ 59
def prefixEnd_1460096 : Nat := 4983230072969 + 3 ^ 40 * 1460096 * 2
def baseEnd_1460096 : Nat := 499820699804816400923431

theorem tailTrace_1460096 : CollatzResearch.WordTrace tailWord_1460096 prefixEnd_1460096 499820699804816400923431 := by
  unfold tailWord_1460096
  simp only [CollatzResearch.WordTrace]
  refine ⟨26627038059164515694492071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35502717412219354259322761 26627038059164515694492071)
  ·
    refine ⟨39940557088746773541738107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26627038059164515694492071 39940557088746773541738107)
    ·
      refine ⟨59910835633120160312607161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39940557088746773541738107 59910835633120160312607161)
      ·
        refine ⟨44933126724840120234455371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59910835633120160312607161 44933126724840120234455371)
        ·
          refine ⟨67399690087260180351683057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44933126724840120234455371 67399690087260180351683057)
          ·
            refine ⟨50549767565445135263762293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67399690087260180351683057 50549767565445135263762293)
            ·
              refine ⟨4739040709260481430977715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50549767565445135263762293 4739040709260481430977715)
              ·
                refine ⟨7108561063890722146466573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739040709260481430977715 7108561063890722146466573)
                ·
                  refine ⟨2665710398959020804924965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7108561063890722146466573 2665710398959020804924965)
                  ·
                    refine ⟨499820699804816400923431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665710398959020804924965 499820699804816400923431)
                    ·
                      rfl

theorem cell22_1460096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_1460096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460096 prefixEnd_1460096 := by exact prefixLift 1460096
  have htrace : WordTrace (prefixWord ++ tailWord_1460096) baseStart_1460096 baseEnd_1460096 := by
    simpa [prefixWord, tailWord_1460096, baseEnd_1460096] using wordTrace_append hprefix tailTrace_1460096
  have hstable : (prefixWord ++ tailWord_1460096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460096).length < 2 ^ (prefixWord ++ tailWord_1460096).sum := by decide
  have hdescent : baseEnd_1460096 < baseStart_1460096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460143 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 2, 3]
def baseStart_1460143 : Nat := 118140960795 + 1460143 * 2 ^ 59
def prefixEnd_1460143 : Nat := 4983230072969 + 3 ^ 40 * 1460143 * 2
def baseEnd_1460143 : Nat := 499836788865323944998287

theorem tailTrace_1460143 : CollatzResearch.WordTrace tailWord_1460143 prefixEnd_1460143 499836788865323944998287 := by
  unfold tailWord_1460143
  simp only [CollatzResearch.WordTrace]
  refine ⟨53255790349158758415945083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35503860232772505610630055 53255790349158758415945083)
  ·
    refine ⟨79883685523738137623917625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53255790349158758415945083 79883685523738137623917625)
    ·
      refine ⟨59912764142803603217938219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79883685523738137623917625 59912764142803603217938219)
      ·
        refine ⟨89869146214205404826907329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59912764142803603217938219 89869146214205404826907329)
        ·
          refine ⟨67401859660654053620180497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89869146214205404826907329 67401859660654053620180497)
          ·
            refine ⟨50551394745490540215135373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67401859660654053620180497 50551394745490540215135373)
            ·
              refine ⟨18956773029558952580675765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50551394745490540215135373 18956773029558952580675765)
              ·
                refine ⟨1777197471521151804438353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18956773029558952580675765 1777197471521151804438353)
                ·
                  refine ⟨1332898103640863853328765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1777197471521151804438353 1332898103640863853328765)
                  ·
                    refine ⟨499836788865323944998287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1332898103640863853328765 499836788865323944998287)
                    ·
                      rfl

theorem cell22_1460143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_1460143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460143 prefixEnd_1460143 := by exact prefixLift 1460143
  have htrace : WordTrace (prefixWord ++ tailWord_1460143) baseStart_1460143 baseEnd_1460143 := by
    simpa [prefixWord, tailWord_1460143, baseEnd_1460143] using wordTrace_append hprefix tailTrace_1460143
  have hstable : (prefixWord ++ tailWord_1460143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460143).length < 2 ^ (prefixWord ++ tailWord_1460143).sum := by decide
  have hdescent : baseEnd_1460143 < baseStart_1460143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460158 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1460158 : Nat := 118140960795 + 1460158 * 2 ^ 59
def prefixEnd_1460158 : Nat := 4983230072969 + 3 ^ 40 * 1460158 * 2
def baseEnd_1460158 : Nat := 499841923671868905873241

theorem tailTrace_1460158 : CollatzResearch.WordTrace tailWord_1460158 prefixEnd_1460158 499841923671868905873241 := by
  unfold tailWord_1460158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6657042180513051997217641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35504224962736277318494085 6657042180513051997217641)
  ·
    refine ⟨4992781635384788997913231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6657042180513051997217641 4992781635384788997913231)
    ·
      refine ⟨7489172453077183496869847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4992781635384788997913231 7489172453077183496869847)
      ·
        refine ⟨11233758679615775245304771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7489172453077183496869847 11233758679615775245304771)
        ·
          refine ⟨16850638019423662867957157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11233758679615775245304771 16850638019423662867957157)
          ·
            refine ⟨3159494628641936787741967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16850638019423662867957157 3159494628641936787741967)
            ·
              refine ⟨4739241942962905181612951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159494628641936787741967 4739241942962905181612951)
              ·
                refine ⟨7108862914444357772419427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739241942962905181612951 7108862914444357772419427)
                ·
                  refine ⟨10663294371666536658629141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7108862914444357772419427 10663294371666536658629141)
                  ·
                    refine ⟨499841923671868905873241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10663294371666536658629141 499841923671868905873241)
                    ·
                      rfl

theorem cell22_1460158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1460158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460158 prefixEnd_1460158 := by exact prefixLift 1460158
  have htrace : WordTrace (prefixWord ++ tailWord_1460158) baseStart_1460158 baseEnd_1460158 := by
    simpa [prefixWord, tailWord_1460158, baseEnd_1460158] using wordTrace_append hprefix tailTrace_1460158
  have hstable : (prefixWord ++ tailWord_1460158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460158).length < 2 ^ (prefixWord ++ tailWord_1460158).sum := by decide
  have hdescent : baseEnd_1460158 < baseStart_1460158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460194 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1460194 : Nat := 118140960795 + 1460194 * 2 ^ 59
def prefixEnd_1460194 : Nat := 4983230072969 + 3 ^ 40 * 1460194 * 2
def baseEnd_1460194 : Nat := 499854247207576811973131

theorem tailTrace_1460194 : CollatzResearch.WordTrace tailWord_1460194 prefixEnd_1460194 499854247207576811973131 := by
  unfold tailWord_1460194
  simp only [CollatzResearch.WordTrace]
  refine ⟨13314412617993498531512909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35505100314649329417367757 13314412617993498531512909)
  ·
    refine ⟨4992904731747561949317341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13314412617993498531512909 4992904731747561949317341)
    ·
      refine ⟨1872339274405335730994003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4992904731747561949317341 1872339274405335730994003)
      ·
        refine ⟨2808508911608003596491005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872339274405335730994003 2808508911608003596491005)
        ·
          refine ⟨1053190841853001348684127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2808508911608003596491005 1053190841853001348684127)
          ·
            refine ⟨1579786262779502023026191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053190841853001348684127 1579786262779502023026191)
            ·
              refine ⟨2369679394169253034539287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579786262779502023026191 2369679394169253034539287)
              ·
                refine ⟨3554519091253879551808931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369679394169253034539287 3554519091253879551808931)
                ·
                  refine ⟨5331778636880819327713397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554519091253879551808931 5331778636880819327713397)
                  ·
                    refine ⟨499854247207576811973131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5331778636880819327713397 499854247207576811973131)
                    ·
                      rfl

theorem cell22_1460194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1460194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460194 prefixEnd_1460194 := by exact prefixLift 1460194
  have htrace : WordTrace (prefixWord ++ tailWord_1460194) baseStart_1460194 baseEnd_1460194 := by
    simpa [prefixWord, tailWord_1460194, baseEnd_1460194] using wordTrace_append hprefix tailTrace_1460194
  have hstable : (prefixWord ++ tailWord_1460194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460194).length < 2 ^ (prefixWord ++ tailWord_1460194).sum := by decide
  have hdescent : baseEnd_1460194 < baseStart_1460194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460216 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_1460216 : Nat := 118140960795 + 1460216 * 2 ^ 59
def prefixEnd_1460216 : Nat := 4983230072969 + 3 ^ 40 * 1460216 * 2
def baseEnd_1460216 : Nat := 499861778257176087923063

theorem tailTrace_1460216 : CollatzResearch.WordTrace tailWord_1460216 prefixEnd_1460216 499861778257176087923063 := by
  unfold tailWord_1460216
  simp only [CollatzResearch.WordTrace]
  refine ⟨26629226438947145941676251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35505635251929527922235001 26629226438947145941676251)
  ·
    refine ⟨39943839658420718912514377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26629226438947145941676251 39943839658420718912514377)
    ·
      refine ⟨29957879743815539184385783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39943839658420718912514377 29957879743815539184385783)
      ·
        refine ⟨44936819615723308776578675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29957879743815539184385783 44936819615723308776578675)
        ·
          refine ⟨67405229423584963164868013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44936819615723308776578675 67405229423584963164868013)
          ·
            refine ⟨25276961033844361186825505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67405229423584963164868013 25276961033844361186825505)
            ·
              refine ⟨18957720775383270890119129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25276961033844361186825505 18957720775383270890119129)
              ·
                refine ⟨14218290581537453167589347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18957720775383270890119129 14218290581537453167589347)
                ·
                  refine ⟨21327435872306179751384021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14218290581537453167589347 21327435872306179751384021)
                  ·
                    refine ⟨499861778257176087923063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21327435872306179751384021 499861778257176087923063)
                    ·
                      rfl

theorem cell22_1460216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_1460216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460216 prefixEnd_1460216 := by exact prefixLift 1460216
  have htrace : WordTrace (prefixWord ++ tailWord_1460216) baseStart_1460216 baseEnd_1460216 := by
    simpa [prefixWord, tailWord_1460216, baseEnd_1460216] using wordTrace_append hprefix tailTrace_1460216
  have hstable : (prefixWord ++ tailWord_1460216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460216).length < 2 ^ (prefixWord ++ tailWord_1460216).sum := by decide
  have hdescent : baseEnd_1460216 < baseStart_1460216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460248 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_1460248 : Nat := 118140960795 + 1460248 * 2 ^ 59
def prefixEnd_1460248 : Nat := 4983230072969 + 3 ^ 40 * 1460248 * 2
def baseEnd_1460248 : Nat := 499872732511138671122965

theorem tailTrace_1460248 : CollatzResearch.WordTrace tailWord_1460248 prefixEnd_1460248 499872732511138671122965 := by
  unfold tailWord_1460248
  simp only [CollatzResearch.WordTrace]
  refine ⟨26629810006889180674258699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35506413342518907565678265 26629810006889180674258699)
  ·
    refine ⟨39944715010333771011388049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26629810006889180674258699 39944715010333771011388049)
    ·
      refine ⟨29958536257750328258541037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39944715010333771011388049 29958536257750328258541037)
      ·
        refine ⟨11234451096656373096952889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29958536257750328258541037 11234451096656373096952889)
        ·
          refine ⟨8425838322492279822714667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11234451096656373096952889 8425838322492279822714667)
          ·
            refine ⟨12638757483738419734072001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425838322492279822714667 12638757483738419734072001)
            ·
              refine ⟨9479068112803814800554001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12638757483738419734072001 9479068112803814800554001)
              ·
                refine ⟨7109301084602861100415501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9479068112803814800554001 7109301084602861100415501)
                ·
                  refine ⟨2665987906726072912655813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7109301084602861100415501 2665987906726072912655813)
                  ·
                    refine ⟨499872732511138671122965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2665987906726072912655813 499872732511138671122965)
                    ·
                      rfl

theorem cell22_1460248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_1460248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460248 prefixEnd_1460248 := by exact prefixLift 1460248
  have htrace : WordTrace (prefixWord ++ tailWord_1460248) baseStart_1460248 baseEnd_1460248 := by
    simpa [prefixWord, tailWord_1460248, baseEnd_1460248] using wordTrace_append hprefix tailTrace_1460248
  have hstable : (prefixWord ++ tailWord_1460248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460248).length < 2 ^ (prefixWord ++ tailWord_1460248).sum := by decide
  have hdescent : baseEnd_1460248 < baseStart_1460248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460252 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 5]
def baseStart_1460252 : Nat := 118140960795 + 1460252 * 2 ^ 59
def prefixEnd_1460252 : Nat := 4983230072969 + 3 ^ 40 * 1460252 * 2
def baseEnd_1460252 : Nat := 166624700597627998007651

theorem tailTrace_1460252 : CollatzResearch.WordTrace tailWord_1460252 prefixEnd_1460252 166624700597627998007651 := by
  unfold tailWord_1460252
  simp only [CollatzResearch.WordTrace]
  refine ⟨26629882952881935015831505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35506510603842580021108673 26629882952881935015831505)
  ·
    refine ⟨19972412214661451261873629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26629882952881935015831505 19972412214661451261873629)
    ·
      refine ⟨7489654580498044223202611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19972412214661451261873629 7489654580498044223202611)
      ·
        refine ⟨11234481870747066334803917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7489654580498044223202611 11234481870747066334803917)
        ·
          refine ⟨4212930701530149875551469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11234481870747066334803917 4212930701530149875551469)
          ·
            refine ⟨1579849013073806203331801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4212930701530149875551469 1579849013073806203331801)
            ·
              refine ⟨1184886759805354652498851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1579849013073806203331801 1184886759805354652498851)
              ·
                refine ⟨1777330139708031978748277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184886759805354652498851 1777330139708031978748277)
                ·
                  refine ⟨166624700597627998007651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1777330139708031978748277 166624700597627998007651)
                  ·
                    rfl

theorem cell22_1460252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_1460252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460252 prefixEnd_1460252 := by exact prefixLift 1460252
  have htrace : WordTrace (prefixWord ++ tailWord_1460252) baseStart_1460252 baseEnd_1460252 := by
    simpa [prefixWord, tailWord_1460252, baseEnd_1460252] using wordTrace_append hprefix tailTrace_1460252
  have hstable : (prefixWord ++ tailWord_1460252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460252).length < 2 ^ (prefixWord ++ tailWord_1460252).sum := by decide
  have hdescent : baseEnd_1460252 < baseStart_1460252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460325 : List Nat := [1, 3, 1, 3, 2, 3, 3, 6]
def baseStart_1460325 : Nat := 118140960795 + 1460325 * 2 ^ 59
def prefixEnd_1460325 : Nat := 4983230072969 + 3 ^ 40 * 1460325 * 2
def baseEnd_1460325 : Nat := 55544343464970681883081

theorem tailTrace_1460325 : CollatzResearch.WordTrace tailWord_1460325 prefixEnd_1460325 55544343464970681883081 := by
  unfold tailWord_1460325
  simp only [CollatzResearch.WordTrace]
  refine ⟨53262428434499403499070429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35508285622999602332713619 53262428434499403499070429)
  ·
    refine ⟨19973410662937276312151411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53262428434499403499070429 19973410662937276312151411)
    ·
      refine ⟨29960115994405914468227117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19973410662937276312151411 29960115994405914468227117)
      ·
        refine ⟨11235043497902217925585169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29960115994405914468227117 11235043497902217925585169)
        ·
          refine ⟨8426282623426663444188877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11235043497902217925585169 8426282623426663444188877)
          ·
            refine ⟨3159855983784998791570829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8426282623426663444188877 3159855983784998791570829)
            ·
              refine ⟨1184945993919374546839061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3159855983784998791570829 1184945993919374546839061)
              ·
                refine ⟨55544343464970681883081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1184945993919374546839061 55544343464970681883081)
                ·
                  rfl

theorem cell22_1460325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 6].length) (baseStart_1460325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460325 prefixEnd_1460325 := by exact prefixLift 1460325
  have htrace : WordTrace (prefixWord ++ tailWord_1460325) baseStart_1460325 baseEnd_1460325 := by
    simpa [prefixWord, tailWord_1460325, baseEnd_1460325] using wordTrace_append hprefix tailTrace_1460325
  have hstable : (prefixWord ++ tailWord_1460325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460325).length < 2 ^ (prefixWord ++ tailWord_1460325).sum := by decide
  have hdescent : baseEnd_1460325 < baseStart_1460325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460357 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_1460357 : Nat := 118140960795 + 1460357 * 2 ^ 59
def prefixEnd_1460357 : Nat := 4983230072969 + 3 ^ 40 * 1460357 * 2
def baseEnd_1460357 : Nat := 499910045438698720147631

theorem tailTrace_1460357 : CollatzResearch.WordTrace tailWord_1460357 prefixEnd_1460357 499910045438698720147631 := by
  unfold tailWord_1460357
  simp only [CollatzResearch.WordTrace]
  refine ⟨53263595570383472964235325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35509063713588981976156883 53263595570383472964235325)
  ·
    refine ⟨19973848338893802361588247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53263595570383472964235325 19973848338893802361588247)
    ·
      refine ⟨29960772508340703542382371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19973848338893802361588247 29960772508340703542382371)
      ·
        refine ⟨44941158762511055313573557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29960772508340703542382371 44941158762511055313573557)
        ·
          refine ⟨4213233633985411435647521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44941158762511055313573557 4213233633985411435647521)
          ·
            refine ⟨3159925225489058576735641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4213233633985411435647521 3159925225489058576735641)
            ·
              refine ⟨2369943919116793932551731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3159925225489058576735641 2369943919116793932551731)
              ·
                refine ⟨3554915878675190898827597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369943919116793932551731 3554915878675190898827597)
                ·
                  refine ⟨1333093454503196587060349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3554915878675190898827597 1333093454503196587060349)
                  ·
                    refine ⟨499910045438698720147631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1333093454503196587060349 499910045438698720147631)
                    ·
                      rfl

theorem cell22_1460357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_1460357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460357 prefixEnd_1460357 := by exact prefixLift 1460357
  have htrace : WordTrace (prefixWord ++ tailWord_1460357) baseStart_1460357 baseEnd_1460357 := by
    simpa [prefixWord, tailWord_1460357, baseEnd_1460357] using wordTrace_append hprefix tailTrace_1460357
  have hstable : (prefixWord ++ tailWord_1460357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460357).length < 2 ^ (prefixWord ++ tailWord_1460357).sum := by decide
  have hdescent : baseEnd_1460357 < baseStart_1460357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460368 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_1460368 : Nat := 118140960795 + 1460368 * 2 ^ 59
def prefixEnd_1460368 : Nat := 4983230072969 + 3 ^ 40 * 1460368 * 2
def baseEnd_1460368 : Nat := 499913810963498358122597

theorem tailTrace_1460368 : CollatzResearch.WordTrace tailWord_1460368 prefixEnd_1460368 499913810963498358122597 := by
  unfold tailWord_1460368
  simp only [CollatzResearch.WordTrace]
  refine ⟨26631998386671810921442879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35509331182229081228590505 26631998386671810921442879)
  ·
    refine ⟨39947997580007716382164319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26631998386671810921442879 39947997580007716382164319)
    ·
      refine ⟨59921996370011574573246479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39947997580007716382164319 59921996370011574573246479)
      ·
        refine ⟨89882994555017361859869719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59921996370011574573246479 89882994555017361859869719)
        ·
          refine ⟨134824491832526042789804579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89882994555017361859869719 134824491832526042789804579)
          ·
            refine ⟨202236737748789064184706869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134824491832526042789804579 202236737748789064184706869)
            ·
              refine ⟨18959694163948974767316269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202236737748789064184706869 18959694163948974767316269)
              ·
                refine ⟨7109885311480865537743601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18959694163948974767316269 7109885311480865537743601)
                ·
                  refine ⟨5332413983610649153307701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7109885311480865537743601 5332413983610649153307701)
                  ·
                    refine ⟨499913810963498358122597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5332413983610649153307701 499913810963498358122597)
                    ·
                      rfl

theorem cell22_1460368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_1460368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460368 prefixEnd_1460368 := by exact prefixLift 1460368
  have htrace : WordTrace (prefixWord ++ tailWord_1460368) baseStart_1460368 baseEnd_1460368 := by
    simpa [prefixWord, tailWord_1460368, baseEnd_1460368] using wordTrace_append hprefix tailTrace_1460368
  have hstable : (prefixWord ++ tailWord_1460368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460368).length < 2 ^ (prefixWord ++ tailWord_1460368).sum := by decide
  have hdescent : baseEnd_1460368 < baseStart_1460368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460434 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_1460434 : Nat := 118140960795 + 1460434 * 2 ^ 59
def prefixEnd_1460434 : Nat := 4983230072969 + 3 ^ 40 * 1460434 * 2
def baseEnd_1460434 : Nat := 499936404112296185972395

theorem tailTrace_1460434 : CollatzResearch.WordTrace tailWord_1460434 prefixEnd_1460434 499936404112296185972395 := by
  unfold tailWord_1460434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13316600997776128778697089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35510935994069676743192237 13316600997776128778697089)
  ·
    refine ⟨9987450748332096584022817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13316600997776128778697089 9987450748332096584022817)
    ·
      refine ⟨7490588061249072438017113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9987450748332096584022817 7490588061249072438017113)
      ·
        refine ⟨5617941045936804328512835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7490588061249072438017113 5617941045936804328512835)
        ·
          refine ⟨8426911568905206492769253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617941045936804328512835 8426911568905206492769253)
          ·
            refine ⟨1580045919169726217394235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8426911568905206492769253 1580045919169726217394235)
            ·
              refine ⟨2370068878754589326091353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580045919169726217394235 2370068878754589326091353)
              ·
                refine ⟨1777551659065941994568515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370068878754589326091353 1777551659065941994568515)
                ·
                  refine ⟨2666327488598912991852773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777551659065941994568515 2666327488598912991852773)
                  ·
                    refine ⟨499936404112296185972395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666327488598912991852773 499936404112296185972395)
                    ·
                      rfl

theorem cell22_1460434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_1460434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460434 prefixEnd_1460434 := by exact prefixLift 1460434
  have htrace : WordTrace (prefixWord ++ tailWord_1460434) baseStart_1460434 baseEnd_1460434 := by
    simpa [prefixWord, tailWord_1460434, baseEnd_1460434] using wordTrace_append hprefix tailTrace_1460434
  have hstable : (prefixWord ++ tailWord_1460434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460434).length < 2 ^ (prefixWord ++ tailWord_1460434).sum := by decide
  have hdescent : baseEnd_1460434 < baseStart_1460434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460451 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 1, 4]
def baseStart_1460451 : Nat := 118140960795 + 1460451 * 2 ^ 59
def prefixEnd_1460451 : Nat := 4983230072969 + 3 ^ 40 * 1460451 * 2
def baseEnd_1460451 : Nat := 499942223559713808297343

theorem tailTrace_1460451 : CollatzResearch.WordTrace tailWord_1460451 prefixEnd_1460451 499942223559713808297343 := by
  unfold tailWord_1460451
  simp only [CollatzResearch.WordTrace]
  refine ⟨53267024032042927018157207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35511349354695284678771471 53267024032042927018157207)
  ·
    refine ⟨79900536048064390527235811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53267024032042927018157207 79900536048064390527235811)
    ·
      refine ⟨119850804072096585790853717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79900536048064390527235811 119850804072096585790853717)
      ·
        refine ⟨1404501610219881864736567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 119850804072096585790853717 1404501610219881864736567)
        ·
          refine ⟨2106752415329822797104851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404501610219881864736567 2106752415329822797104851)
          ·
            refine ⟨3160128622994734195657277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106752415329822797104851 3160128622994734195657277)
            ·
              refine ⟨1185048233623025323371479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3160128622994734195657277 1185048233623025323371479)
              ·
                refine ⟨1777572350434537985057219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185048233623025323371479 1777572350434537985057219)
                ·
                  refine ⟨2666358525651806977585829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777572350434537985057219 2666358525651806977585829)
                  ·
                    refine ⟨499942223559713808297343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666358525651806977585829 499942223559713808297343)
                    ·
                      rfl

theorem cell22_1460451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 4].length) (baseStart_1460451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460451 prefixEnd_1460451 := by exact prefixLift 1460451
  have htrace : WordTrace (prefixWord ++ tailWord_1460451) baseStart_1460451 baseEnd_1460451 := by
    simpa [prefixWord, tailWord_1460451, baseEnd_1460451] using wordTrace_append hprefix tailTrace_1460451
  have hstable : (prefixWord ++ tailWord_1460451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460451).length < 2 ^ (prefixWord ++ tailWord_1460451).sum := by decide
  have hdescent : baseEnd_1460451 < baseStart_1460451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460466 : List Nat := [3, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_1460466 : Nat := 118140960795 + 1460466 * 2 ^ 59
def prefixEnd_1460466 : Nat := 4983230072969 + 3 ^ 40 * 1460466 * 2
def baseEnd_1460466 : Nat := 166649119455419589724099

theorem tailTrace_1460466 : CollatzResearch.WordTrace tailWord_1460466 prefixEnd_1460466 166649119455419589724099 := by
  unfold tailWord_1460466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13316892781747146144988313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35511714084659056386635501 13316892781747146144988313)
  ·
    refine ⟨9987669586310359608741235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13316892781747146144988313 9987669586310359608741235)
    ·
      refine ⟨14981504379465539413111853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9987669586310359608741235 14981504379465539413111853)
      ·
        refine ⟨5618064142299577279916945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14981504379465539413111853 5618064142299577279916945)
        ·
          refine ⟨4213548106724682959937709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618064142299577279916945 4213548106724682959937709)
          ·
            refine ⟨1580080540021756109976641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4213548106724682959937709 1580080540021756109976641)
            ·
              refine ⟨1185060405016317082482481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580080540021756109976641 1185060405016317082482481)
              ·
                refine ⟨888795303762237811861861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185060405016317082482481 888795303762237811861861)
                ·
                  refine ⟨166649119455419589724099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 888795303762237811861861 166649119455419589724099)
                  ·
                    rfl

theorem cell22_1460466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_1460466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460466 prefixEnd_1460466 := by exact prefixLift 1460466
  have htrace : WordTrace (prefixWord ++ tailWord_1460466) baseStart_1460466 baseEnd_1460466 := by
    simpa [prefixWord, tailWord_1460466, baseEnd_1460466] using wordTrace_append hprefix tailTrace_1460466
  have hstable : (prefixWord ++ tailWord_1460466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460466).length < 2 ^ (prefixWord ++ tailWord_1460466).sum := by decide
  have hdescent : baseEnd_1460466 < baseStart_1460466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460475 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 9, 3]
def baseStart_1460475 : Nat := 118140960795 + 1460475 * 2 ^ 59
def prefixEnd_1460475 : Nat := 4983230072969 + 3 ^ 40 * 1460475 * 2
def baseEnd_1460475 : Nat := 499950439250185745697269

theorem tailTrace_1460475 : CollatzResearch.WordTrace tailWord_1460475 prefixEnd_1460475 499950439250185745697269 := by
  unfold tailWord_1460475
  simp only [CollatzResearch.WordTrace]
  refine ⟨53267899383955979117030879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35511932922637319411353919 53267899383955979117030879)
  ·
    refine ⟨79901849075933968675546319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53267899383955979117030879 79901849075933968675546319)
    ·
      refine ⟨119852773613900953013319479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79901849075933968675546319 119852773613900953013319479)
      ·
        refine ⟨179779160420851429519979219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119852773613900953013319479 179779160420851429519979219)
        ·
          refine ⟨269668740631277144279968829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179779160420851429519979219 269668740631277144279968829)
          ·
            refine ⟨101125777736728929104988311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 269668740631277144279968829 101125777736728929104988311)
            ·
              refine ⟨151688666605093393657482467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101125777736728929104988311 151688666605093393657482467)
              ·
                refine ⟨227532999907640090486223701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151688666605093393657482467 227532999907640090486223701)
                ·
                  refine ⟨1333201171333828655192717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 227532999907640090486223701 1333201171333828655192717)
                  ·
                    refine ⟨499950439250185745697269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1333201171333828655192717 499950439250185745697269)
                    ·
                      rfl

theorem cell22_1460475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 3].length) (baseStart_1460475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460475 prefixEnd_1460475 := by exact prefixLift 1460475
  have htrace : WordTrace (prefixWord ++ tailWord_1460475) baseStart_1460475 baseEnd_1460475 := by
    simpa [prefixWord, tailWord_1460475, baseEnd_1460475] using wordTrace_append hprefix tailTrace_1460475
  have hstable : (prefixWord ++ tailWord_1460475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460475).length < 2 ^ (prefixWord ++ tailWord_1460475).sum := by decide
  have hdescent : baseEnd_1460475 < baseStart_1460475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460492 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_1460492 : Nat := 118140960795 + 1460492 * 2 ^ 59
def prefixEnd_1460492 : Nat := 4983230072969 + 3 ^ 40 * 1460492 * 2
def baseEnd_1460492 : Nat := 499956258697603368022217

theorem tailTrace_1460492 : CollatzResearch.WordTrace tailWord_1460492 prefixEnd_1460492 499956258697603368022217 := by
  unfold tailWord_1460492
  simp only [CollatzResearch.WordTrace]
  refine ⟨26634259712447195510199865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35512346283262927346933153 26634259712447195510199865)
  ·
    refine ⟨19975694784335396632649899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26634259712447195510199865 19975694784335396632649899)
    ·
      refine ⟨29963542176503094948974849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19975694784335396632649899 29963542176503094948974849)
      ·
        refine ⟨22472656632377321211731137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29963542176503094948974849 22472656632377321211731137)
        ·
          refine ⟨16854492474282990908798353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22472656632377321211731137 16854492474282990908798353)
          ·
            refine ⟨12640869355712243181598765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16854492474282990908798353 12640869355712243181598765)
            ·
              refine ⟨4740326008392091193099537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12640869355712243181598765 4740326008392091193099537)
              ·
                refine ⟨3555244506294068394824653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4740326008392091193099537 3555244506294068394824653)
                ·
                  refine ⟨1333216689860275648059245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3555244506294068394824653 1333216689860275648059245)
                  ·
                    refine ⟨499956258697603368022217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1333216689860275648059245 499956258697603368022217)
                    ·
                      rfl

theorem cell22_1460492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_1460492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460492 prefixEnd_1460492 := by exact prefixLift 1460492
  have htrace : WordTrace (prefixWord ++ tailWord_1460492) baseStart_1460492 baseEnd_1460492 := by
    simpa [prefixWord, tailWord_1460492, baseEnd_1460492] using wordTrace_append hprefix tailTrace_1460492
  have hstable : (prefixWord ++ tailWord_1460492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460492).length < 2 ^ (prefixWord ++ tailWord_1460492).sum := by decide
  have hdescent : baseEnd_1460492 < baseStart_1460492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460535 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 5, 4]
def baseStart_1460535 : Nat := 118140960795 + 1460535 * 2 ^ 59
def prefixEnd_1460535 : Nat := 4983230072969 + 3 ^ 40 * 1460535 * 2
def baseEnd_1460535 : Nat := 499970978476365589197085

theorem tailTrace_1460535 : CollatzResearch.WordTrace tailWord_1460535 prefixEnd_1460535 499970978476365589197085 := by
  unfold tailWord_1460535
  simp only [CollatzResearch.WordTrace]
  refine ⟨53270087763738609364215059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35513391842492406242810039 53270087763738609364215059)
  ·
    refine ⟨79905131645607914046322589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53270087763738609364215059 79905131645607914046322589)
    ·
      refine ⟨29964424367102967767370971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79905131645607914046322589 29964424367102967767370971)
      ·
        refine ⟨44946636550654451651056457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29964424367102967767370971 44946636550654451651056457)
        ·
          refine ⟨33709977412990838738292343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44946636550654451651056457 33709977412990838738292343)
          ·
            refine ⟨50564966119486258107438515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33709977412990838738292343 50564966119486258107438515)
            ·
              refine ⟨75847449179229387161157773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50564966119486258107438515 75847449179229387161157773)
              ·
                refine ⟨28442793442211020185434165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75847449179229387161157773 28442793442211020185434165)
                ·
                  refine ⟨2666511885207283142384453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28442793442211020185434165 2666511885207283142384453)
                  ·
                    refine ⟨499970978476365589197085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666511885207283142384453 499970978476365589197085)
                    ·
                      rfl

theorem cell22_1460535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_1460535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460535 prefixEnd_1460535 := by exact prefixLift 1460535
  have htrace : WordTrace (prefixWord ++ tailWord_1460535) baseStart_1460535 baseEnd_1460535 := by
    simpa [prefixWord, tailWord_1460535, baseEnd_1460535] using wordTrace_append hprefix tailTrace_1460535
  have hstable : (prefixWord ++ tailWord_1460535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460535).length < 2 ^ (prefixWord ++ tailWord_1460535).sum := by decide
  have hdescent : baseEnd_1460535 < baseStart_1460535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460537 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_1460537 : Nat := 118140960795 + 1460537 * 2 ^ 59
def prefixEnd_1460537 : Nat := 4983230072969 + 3 ^ 40 * 1460537 * 2
def baseEnd_1460537 : Nat := 499971663117238250647079

theorem tailTrace_1460537 : CollatzResearch.WordTrace tailWord_1460537 prefixEnd_1460537 499971663117238250647079 := by
  unfold tailWord_1460537
  simp only [CollatzResearch.WordTrace]
  refine ⟨53270160709731363705787865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35513440473154242470525243 53270160709731363705787865)
  ·
    refine ⟨39952620532298522779340899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53270160709731363705787865 39952620532298522779340899)
    ·
      refine ⟨59928930798447784169011349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39952620532298522779340899 59928930798447784169011349)
      ·
        refine ⟨2809168631177239882922407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59928930798447784169011349 2809168631177239882922407)
        ·
          refine ⟨4213752946765859824383611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809168631177239882922407 4213752946765859824383611)
          ·
            refine ⟨6320629420148789736575417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213752946765859824383611 6320629420148789736575417)
            ·
              refine ⟨4740472065111592302431563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6320629420148789736575417 4740472065111592302431563)
              ·
                refine ⟨7110708097667388453647345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4740472065111592302431563 7110708097667388453647345)
                ·
                  refine ⟨5333031073250541340235509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7110708097667388453647345 5333031073250541340235509)
                  ·
                    refine ⟨499971663117238250647079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5333031073250541340235509 499971663117238250647079)
                    ·
                      rfl

theorem cell22_1460537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_1460537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460537 prefixEnd_1460537 := by exact prefixLift 1460537
  have htrace : WordTrace (prefixWord ++ tailWord_1460537) baseStart_1460537 baseEnd_1460537 := by
    simpa [prefixWord, tailWord_1460537, baseEnd_1460537] using wordTrace_append hprefix tailTrace_1460537
  have hstable : (prefixWord ++ tailWord_1460537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460537).length < 2 ^ (prefixWord ++ tailWord_1460537).sum := by decide
  have hdescent : baseEnd_1460537 < baseStart_1460537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460552 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_1460552 : Nat := 118140960795 + 1460552 * 2 ^ 59
def prefixEnd_1460552 : Nat := 4983230072969 + 3 ^ 40 * 1460552 * 2
def baseEnd_1460552 : Nat := 499976797923783211522033

theorem tailTrace_1460552 : CollatzResearch.WordTrace tailWord_1460552 prefixEnd_1460552 499976797923783211522033 := by
  unfold tailWord_1460552
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635353902338510633791955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35513805203118014178389273 26635353902338510633791955)
  ·
    refine ⟨39953030853507765950687933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26635353902338510633791955 39953030853507765950687933)
    ·
      refine ⟨14982386570065412231507975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39953030853507765950687933 14982386570065412231507975)
      ·
        refine ⟨22473579855098118347261963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14982386570065412231507975 22473579855098118347261963)
        ·
          refine ⟨33710369782647177520892945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22473579855098118347261963 33710369782647177520892945)
          ·
            refine ⟨25282777336985383140669709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33710369782647177520892945 25282777336985383140669709)
            ·
              refine ⟨9481041501369518677751141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25282777336985383140669709 9481041501369518677751141)
              ·
                refine ⟨1777695281506784752078339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9481041501369518677751141 1777695281506784752078339)
                ·
                  refine ⟨2666542922260177128117509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777695281506784752078339 2666542922260177128117509)
                  ·
                    refine ⟨499976797923783211522033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2666542922260177128117509 499976797923783211522033)
                    ·
                      rfl

theorem cell22_1460552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_1460552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460552 prefixEnd_1460552 := by exact prefixLift 1460552
  have htrace : WordTrace (prefixWord ++ tailWord_1460552) baseStart_1460552 baseEnd_1460552 := by
    simpa [prefixWord, tailWord_1460552, baseEnd_1460552] using wordTrace_append hprefix tailTrace_1460552
  have hstable : (prefixWord ++ tailWord_1460552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460552).length < 2 ^ (prefixWord ++ tailWord_1460552).sum := by decide
  have hdescent : baseEnd_1460552 < baseStart_1460552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460584 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 6]
def baseStart_1460584 : Nat := 118140960795 + 1460584 * 2 ^ 59
def prefixEnd_1460584 : Nat := 4983230072969 + 3 ^ 40 * 1460584 * 2
def baseEnd_1460584 : Nat := 166662584059248598240645

theorem tailTrace_1460584 : CollatzResearch.WordTrace tailWord_1460584 prefixEnd_1460584 166662584059248598240645 := by
  unfold tailWord_1460584
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635937470280545366374403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35514583293707393821832537 26635937470280545366374403)
  ·
    refine ⟨39953906205420818049561605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26635937470280545366374403 39953906205420818049561605)
    ·
      refine ⟨7491357413516403384292801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39953906205420818049561605 7491357413516403384292801)
      ·
        refine ⟨5618518060137302538219601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7491357413516403384292801 5618518060137302538219601)
        ·
          refine ⟨4213888545102976903664701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618518060137302538219601 4213888545102976903664701)
          ·
            refine ⟨1580208204413616338874263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4213888545102976903664701 1580208204413616338874263)
            ·
              refine ⟨2370312306620424508311395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580208204413616338874263 2370312306620424508311395)
              ·
                refine ⟨3555468459930636762467093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370312306620424508311395 3555468459930636762467093)
                ·
                  refine ⟨166662584059248598240645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3555468459930636762467093 166662584059248598240645)
                  ·
                    rfl

theorem cell22_1460584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_1460584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460584 prefixEnd_1460584 := by exact prefixLift 1460584
  have htrace : WordTrace (prefixWord ++ tailWord_1460584) baseStart_1460584 baseEnd_1460584 := by
    simpa [prefixWord, tailWord_1460584, baseEnd_1460584] using wordTrace_append hprefix tailTrace_1460584
  have hstable : (prefixWord ++ tailWord_1460584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460584).length < 2 ^ (prefixWord ++ tailWord_1460584).sum := by decide
  have hdescent : baseEnd_1460584 < baseStart_1460584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460625 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1460625 : Nat := 118140960795 + 1460625 * 2 ^ 59
def prefixEnd_1460625 : Nat := 4983230072969 + 3 ^ 40 * 1460625 * 2
def baseEnd_1460625 : Nat := 500001787315635354446809

theorem tailTrace_1460625 : CollatzResearch.WordTrace tailWord_1460625 prefixEnd_1460625 500001787315635354446809 := by
  unfold tailWord_1460625
  simp only [CollatzResearch.WordTrace]
  refine ⟨53273370333412554734991329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35515580222275036489994219 53273370333412554734991329)
  ·
    refine ⟨39955027750059416051243497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53273370333412554734991329 39955027750059416051243497)
    ·
      refine ⟨29966270812544562038432623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39955027750059416051243497 29966270812544562038432623)
      ·
        refine ⟨44949406218816843057648935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29966270812544562038432623 44949406218816843057648935)
        ·
          refine ⟨67424109328225264586473403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44949406218816843057648935 67424109328225264586473403)
          ·
            refine ⟨101136163992337896879710105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67424109328225264586473403 101136163992337896879710105)
            ·
              refine ⟨75852122994253422659782579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101136163992337896879710105 75852122994253422659782579)
              ·
                refine ⟨113778184491380133989673869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75852122994253422659782579 113778184491380133989673869)
                ·
                  refine ⟨42666819184267550246127701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113778184491380133989673869 42666819184267550246127701)
                  ·
                    refine ⟨500001787315635354446809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42666819184267550246127701 500001787315635354446809)
                    ·
                      rfl

theorem cell22_1460625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1460625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460625 prefixEnd_1460625 := by exact prefixLift 1460625
  have htrace : WordTrace (prefixWord ++ tailWord_1460625) baseStart_1460625 baseEnd_1460625 := by
    simpa [prefixWord, tailWord_1460625, baseEnd_1460625] using wordTrace_append hprefix tailTrace_1460625
  have hstable : (prefixWord ++ tailWord_1460625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460625).length < 2 ^ (prefixWord ++ tailWord_1460625).sum := by decide
  have hdescent : baseEnd_1460625 < baseStart_1460625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460642 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1460642 : Nat := 118140960795 + 1460642 * 2 ^ 59
def prefixEnd_1460642 : Nat := 4983230072969 + 3 ^ 40 * 1460642 * 2
def baseEnd_1460642 : Nat := 500007606763052976771757

theorem tailTrace_1460642 : CollatzResearch.WordTrace tailWord_1460642 prefixEnd_1460642 500007606763052976771757 := by
  unfold tailWord_1460642
  simp only [CollatzResearch.WordTrace]
  refine ⟨13318497593587741659590045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35515993582900644425573453 13318497593587741659590045)
  ·
    refine ⟨4994436597595403122346267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13318497593587741659590045 4994436597595403122346267)
    ·
      refine ⟨7491654896393104683519401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4994436597595403122346267 7491654896393104683519401)
      ·
        refine ⟨5618741172294828512639551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7491654896393104683519401 5618741172294828512639551)
        ·
          refine ⟨8428111758442242768959327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5618741172294828512639551 8428111758442242768959327)
          ·
            refine ⟨12642167637663364153438991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8428111758442242768959327 12642167637663364153438991)
            ·
              refine ⟨18963251456495046230158487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12642167637663364153438991 18963251456495046230158487)
              ·
                refine ⟨28444877184742569345237731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18963251456495046230158487 28444877184742569345237731)
                ·
                  refine ⟨42667315777113854017856597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28444877184742569345237731 42667315777113854017856597)
                  ·
                    refine ⟨500007606763052976771757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42667315777113854017856597 500007606763052976771757)
                    ·
                      rfl

theorem cell22_1460642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1460642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460642 prefixEnd_1460642 := by exact prefixLift 1460642
  have htrace : WordTrace (prefixWord ++ tailWord_1460642) baseStart_1460642 baseEnd_1460642 := by
    simpa [prefixWord, tailWord_1460642, baseEnd_1460642] using wordTrace_append hprefix tailTrace_1460642
  have hstable : (prefixWord ++ tailWord_1460642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460642).length < 2 ^ (prefixWord ++ tailWord_1460642).sum := by decide
  have hdescent : baseEnd_1460642 < baseStart_1460642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460661 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_1460661 : Nat := 118140960795 + 1460661 * 2 ^ 59
def prefixEnd_1460661 : Nat := 4983230072969 + 3 ^ 40 * 1460661 * 2
def baseEnd_1460661 : Nat := 500014110851343260546699

theorem tailTrace_1460661 : CollatzResearch.WordTrace tailWord_1460661 prefixEnd_1460661 500014110851343260546699 := by
  unfold tailWord_1460661
  simp only [CollatzResearch.WordTrace]
  refine ⟨53274683361282132883301837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35516455574188088588867891 53274683361282132883301837)
  ·
    refine ⟨19978006260480799831238189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53274683361282132883301837 19978006260480799831238189)
    ·
      refine ⟨7491752347680299936714321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19978006260480799831238189 7491752347680299936714321)
      ·
        refine ⟨5618814260760224952535741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7491752347680299936714321 5618814260760224952535741)
        ·
          refine ⟨2107055347785084357200903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5618814260760224952535741 2107055347785084357200903)
          ·
            refine ⟨3160583021677626535801355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107055347785084357200903 3160583021677626535801355)
            ·
              refine ⟨4740874532516439803702033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160583021677626535801355 4740874532516439803702033)
              ·
                refine ⟨3555655899387329852776525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4740874532516439803702033 3555655899387329852776525)
                ·
                  refine ⟨1333370962270248694791197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3555655899387329852776525 1333370962270248694791197)
                  ·
                    refine ⟨500014110851343260546699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1333370962270248694791197 500014110851343260546699)
                    ·
                      rfl

theorem cell22_1460661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_1460661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460661 prefixEnd_1460661 := by exact prefixLift 1460661
  have htrace : WordTrace (prefixWord ++ tailWord_1460661) baseStart_1460661 baseEnd_1460661 := by
    simpa [prefixWord, tailWord_1460661, baseEnd_1460661] using wordTrace_append hprefix tailTrace_1460661
  have hstable : (prefixWord ++ tailWord_1460661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460661).length < 2 ^ (prefixWord ++ tailWord_1460661).sum := by decide
  have hdescent : baseEnd_1460661 < baseStart_1460661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460747 : List Nat := [1, 1, 1, 1, 7, 1, 10]
def baseStart_1460747 : Nat := 118140960795 + 1460747 * 2 ^ 59
def prefixEnd_1460747 : Nat := 4983230072969 + 3 ^ 40 * 1460747 * 2
def baseEnd_1460747 : Nat := 18520131496624729736905

theorem tailTrace_1460747 : CollatzResearch.WordTrace tailWord_1460747 prefixEnd_1460747 18520131496624729736905 := by
  unfold tailWord_1460747
  simp only [CollatzResearch.WordTrace]
  refine ⟨53277820038970569570932495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35518546692647046380621663 53277820038970569570932495)
  ·
    refine ⟨79916730058455854356398743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53277820038970569570932495 79916730058455854356398743)
    ·
      refine ⟨119875095087683781534598115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79916730058455854356398743 119875095087683781534598115)
      ·
        refine ⟨179812642631525672301897173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119875095087683781534598115 179812642631525672301897173)
        ·
          refine ⟨4214358811676382944575715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 179812642631525672301897173 4214358811676382944575715)
          ·
            refine ⟨6321538217514574416863573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214358811676382944575715 6321538217514574416863573)
            ·
              refine ⟨18520131496624729736905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6321538217514574416863573 18520131496624729736905)
              ·
                rfl

theorem cell22_1460747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 10].length) (baseStart_1460747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460747 prefixEnd_1460747 := by exact prefixLift 1460747
  have htrace : WordTrace (prefixWord ++ tailWord_1460747) baseStart_1460747 baseEnd_1460747 := by
    simpa [prefixWord, tailWord_1460747, baseEnd_1460747] using wordTrace_append hprefix tailTrace_1460747
  have hstable : (prefixWord ++ tailWord_1460747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460747).length < 2 ^ (prefixWord ++ tailWord_1460747).sum := by decide
  have hdescent : baseEnd_1460747 < baseStart_1460747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460764 : List Nat := [2, 2, 3, 1, 2, 3, 2, 7]
def baseStart_1460764 : Nat := 118140960795 + 1460764 * 2 ^ 59
def prefixEnd_1460764 : Nat := 4983230072969 + 3 ^ 40 * 1460764 * 2
def baseEnd_1460764 : Nat := 55561041095142813913487

theorem tailTrace_1460764 : CollatzResearch.WordTrace tailWord_1460764 prefixEnd_1460764 55561041095142813913487 := by
  unfold tailWord_1460764
  simp only [CollatzResearch.WordTrace]
  refine ⟨26639220039954490737150673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35518960053272654316200897 26639220039954490737150673)
  ·
    refine ⟨19979415029965868052863005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26639220039954490737150673 19979415029965868052863005)
    ·
      refine ⟨7492280636237200519823627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19979415029965868052863005 7492280636237200519823627)
      ·
        refine ⟨11238420954355800779735441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7492280636237200519823627 11238420954355800779735441)
        ·
          refine ⟨8428815715766850584801581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11238420954355800779735441 8428815715766850584801581)
          ·
            refine ⟨3160805893412568969300593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8428815715766850584801581 3160805893412568969300593)
            ·
              refine ⟨2370604420059426726975445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160805893412568969300593 2370604420059426726975445)
              ·
                refine ⟨55561041095142813913487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2370604420059426726975445 55561041095142813913487)
                ·
                  rfl

theorem cell22_1460764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 7].length) (baseStart_1460764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460764 prefixEnd_1460764 := by exact prefixLift 1460764
  have htrace : WordTrace (prefixWord ++ tailWord_1460764) baseStart_1460764 baseEnd_1460764 := by
    simpa [prefixWord, tailWord_1460764, baseEnd_1460764] using wordTrace_append hprefix tailTrace_1460764
  have hstable : (prefixWord ++ tailWord_1460764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460764).length < 2 ^ (prefixWord ++ tailWord_1460764).sum := by decide
  have hdescent : baseEnd_1460764 < baseStart_1460764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460768 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 2, 3]
def baseStart_1460768 : Nat := 118140960795 + 1460768 * 2 ^ 59
def prefixEnd_1460768 : Nat := 4983230072969 + 3 ^ 40 * 1460768 * 2
def baseEnd_1460768 : Nat := 500050739138030648121371

theorem tailTrace_1460768 : CollatzResearch.WordTrace tailWord_1460768 prefixEnd_1460768 500050739138030648121371 := by
  unfold tailWord_1460768
  simp only [CollatzResearch.WordTrace]
  refine ⟨26639292985947245078723479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35519057314596326771631305 26639292985947245078723479)
  ·
    refine ⟨39958939478920867618085219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26639292985947245078723479 39958939478920867618085219)
    ·
      refine ⟨59938409218381301427127829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39958939478920867618085219 59938409218381301427127829)
      ·
        refine ⟨2809612932111623504396617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59938409218381301427127829 2809612932111623504396617)
        ·
          refine ⟨2107209699083717628297463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2809612932111623504396617 2107209699083717628297463)
          ·
            refine ⟨3160814548625576442446195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107209699083717628297463 3160814548625576442446195)
            ·
              refine ⟨4741221822938364663669293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160814548625576442446195 4741221822938364663669293)
              ·
                refine ⟨1777958183601886748875985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4741221822938364663669293 1777958183601886748875985)
                ·
                  refine ⟨1333468637701415061656989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1777958183601886748875985 1333468637701415061656989)
                  ·
                    refine ⟨500050739138030648121371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1333468637701415061656989 500050739138030648121371)
                    ·
                      rfl

theorem cell22_1460768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_1460768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460768 prefixEnd_1460768 := by exact prefixLift 1460768
  have htrace : WordTrace (prefixWord ++ tailWord_1460768) baseStart_1460768 baseEnd_1460768 := by
    simpa [prefixWord, tailWord_1460768, baseEnd_1460768] using wordTrace_append hprefix tailTrace_1460768
  have hstable : (prefixWord ++ tailWord_1460768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460768).length < 2 ^ (prefixWord ++ tailWord_1460768).sum := by decide
  have hdescent : baseEnd_1460768 < baseStart_1460768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460779 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 3, 3]
def baseStart_1460779 : Nat := 118140960795 + 1460779 * 2 ^ 59
def prefixEnd_1460779 : Nat := 4983230072969 + 3 ^ 40 * 1460779 * 2
def baseEnd_1460779 : Nat := 500054504662830286096337

theorem tailTrace_1460779 : CollatzResearch.WordTrace tailWord_1460779 prefixEnd_1460779 500054504662830286096337 := by
  unfold tailWord_1460779
  simp only [CollatzResearch.WordTrace]
  refine ⟨53278987174854639036097391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35519324783236426024064927 53278987174854639036097391)
  ·
    refine ⟨79918480762281958554146087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53278987174854639036097391 79918480762281958554146087)
    ·
      refine ⟨119877721143422937831219131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79918480762281958554146087 119877721143422937831219131)
      ·
        refine ⟨179816581715134406746828697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119877721143422937831219131 179816581715134406746828697)
        ·
          refine ⟨134862436286350805060121523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179816581715134406746828697 134862436286350805060121523)
          ·
            refine ⟨202293654429526207590182285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134862436286350805060121523 202293654429526207590182285)
            ·
              refine ⟨75860120411072327846318357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202293654429526207590182285 75860120411072327846318357)
              ·
                refine ⟨3555943144269015367796173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75860120411072327846318357 3555943144269015367796173)
                ·
                  refine ⟨1333478679100880762923565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3555943144269015367796173 1333478679100880762923565)
                  ·
                    refine ⟨500054504662830286096337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1333478679100880762923565 500054504662830286096337)
                    ·
                      rfl

theorem cell22_1460779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 3].length) (baseStart_1460779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460779 prefixEnd_1460779 := by exact prefixLift 1460779
  have htrace : WordTrace (prefixWord ++ tailWord_1460779) baseStart_1460779 baseEnd_1460779 := by
    simpa [prefixWord, tailWord_1460779, baseEnd_1460779] using wordTrace_append hprefix tailTrace_1460779
  have hstable : (prefixWord ++ tailWord_1460779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460779).length < 2 ^ (prefixWord ++ tailWord_1460779).sum := by decide
  have hdescent : baseEnd_1460779 < baseStart_1460779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460804 : List Nat := [2, 3, 5, 1, 1, 2, 2, 2, 4]
def baseStart_1460804 : Nat := 118140960795 + 1460804 * 2 ^ 59
def prefixEnd_1460804 : Nat := 4983230072969 + 3 ^ 40 * 1460804 * 2
def baseEnd_1460804 : Nat := 166687687557912851407087

theorem tailTrace_1460804 : CollatzResearch.WordTrace tailWord_1460804 prefixEnd_1460804 166687687557912851407087 := by
  unfold tailWord_1460804
  simp only [CollatzResearch.WordTrace]
  refine ⟨26639949499882034152878733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35519932666509378870504977 26639949499882034152878733)
  ·
    refine ⟨9989981062455762807329525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26639949499882034152878733 9989981062455762807329525)
    ·
      refine ⟨936560724605227763187143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9989981062455762807329525 936560724605227763187143)
      ·
        refine ⟨1404841086907841644780715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936560724605227763187143 1404841086907841644780715)
        ·
          refine ⟨2107261630361762467171073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404841086907841644780715 2107261630361762467171073)
          ·
            refine ⟨1580446222771321850378305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2107261630361762467171073 1580446222771321850378305)
            ·
              refine ⟨1185334667078491387783729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580446222771321850378305 1185334667078491387783729)
              ·
                refine ⟨889001000308868540837797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185334667078491387783729 889001000308868540837797)
                ·
                  refine ⟨166687687557912851407087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889001000308868540837797 166687687557912851407087)
                  ·
                    rfl

theorem cell22_1460804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_1460804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460804 prefixEnd_1460804 := by exact prefixLift 1460804
  have htrace : WordTrace (prefixWord ++ tailWord_1460804) baseStart_1460804 baseEnd_1460804 := by
    simpa [prefixWord, tailWord_1460804, baseEnd_1460804] using wordTrace_append hprefix tailTrace_1460804
  have hstable : (prefixWord ++ tailWord_1460804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460804).length < 2 ^ (prefixWord ++ tailWord_1460804).sum := by decide
  have hdescent : baseEnd_1460804 < baseStart_1460804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460871 : List Nat := [1, 1, 4, 2, 1, 2, 1, 6, 4]
def baseStart_1460871 : Nat := 118140960795 + 1460871 * 2 ^ 59
def prefixEnd_1460871 : Nat := 4983230072969 + 3 ^ 40 * 1460871 * 2
def baseEnd_1460871 : Nat := 166695332714324237598685

theorem tailTrace_1460871 : CollatzResearch.WordTrace tailWord_1460871 prefixEnd_1460871 166695332714324237598685 := by
  unfold tailWord_1460871
  simp only [CollatzResearch.WordTrace]
  refine ⟨53282342690521338748446467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35521561793680892498964311 53282342690521338748446467)
  ·
    refine ⟨79923514035782008122669701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53282342690521338748446467 79923514035782008122669701)
    ·
      refine ⟨14985658881709126523000569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79923514035782008122669701 14985658881709126523000569)
      ·
        refine ⟨11239244161281844892250427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14985658881709126523000569 11239244161281844892250427)
        ·
          refine ⟨16858866241922767338375641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11239244161281844892250427 16858866241922767338375641)
          ·
            refine ⟨12644149681442075503781731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16858866241922767338375641 12644149681442075503781731)
            ·
              refine ⟨18966224522163113255672597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12644149681442075503781731 18966224522163113255672597)
              ·
                refine ⟨889041774476395933859653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18966224522163113255672597 889041774476395933859653)
                ·
                  refine ⟨166695332714324237598685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889041774476395933859653 166695332714324237598685)
                  ·
                    rfl

theorem cell22_1460871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 4].length) (baseStart_1460871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460871 prefixEnd_1460871 := by exact prefixLift 1460871
  have htrace : WordTrace (prefixWord ++ tailWord_1460871) baseStart_1460871 baseEnd_1460871 := by
    simpa [prefixWord, tailWord_1460871, baseEnd_1460871] using wordTrace_append hprefix tailTrace_1460871
  have hstable : (prefixWord ++ tailWord_1460871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460871).length < 2 ^ (prefixWord ++ tailWord_1460871).sum := by decide
  have hdescent : baseEnd_1460871 < baseStart_1460871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460890 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_1460890 : Nat := 118140960795 + 1460890 * 2 ^ 59
def prefixEnd_1460890 : Nat := 4983230072969 + 3 ^ 40 * 1460890 * 2
def baseEnd_1460890 : Nat := 500092502231262996570997

theorem tailTrace_1460890 : CollatzResearch.WordTrace tailWord_1460890 prefixEnd_1460890 500092502231262996570997 := by
  unfold tailWord_1460890
  simp only [CollatzResearch.WordTrace]
  refine ⟨13320758919363126248347031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35522023784968336662258749 13320758919363126248347031)
  ·
    refine ⟨19981138379044689372520547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13320758919363126248347031 19981138379044689372520547)
    ·
      refine ⟨29971707568567034058780821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19981138379044689372520547 29971707568567034058780821)
      ·
        refine ⟨1404923792276579721505351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29971707568567034058780821 1404923792276579721505351)
        ·
          refine ⟨2107385688414869582258027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404923792276579721505351 2107385688414869582258027)
          ·
            refine ⟨3161078532622304373387041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107385688414869582258027 3161078532622304373387041)
            ·
              refine ⟨2370808899466728280040281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161078532622304373387041 2370808899466728280040281)
              ·
                refine ⟨1778106674600046210030211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370808899466728280040281 1778106674600046210030211)
                ·
                  refine ⟨2667160011900069315045317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778106674600046210030211 2667160011900069315045317)
                  ·
                    refine ⟨500092502231262996570997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667160011900069315045317 500092502231262996570997)
                    ·
                      rfl

theorem cell22_1460890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_1460890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460890 prefixEnd_1460890 := by exact prefixLift 1460890
  have htrace : WordTrace (prefixWord ++ tailWord_1460890) baseStart_1460890 baseEnd_1460890 := by
    simpa [prefixWord, tailWord_1460890, baseEnd_1460890] using wordTrace_append hprefix tailTrace_1460890
  have hstable : (prefixWord ++ tailWord_1460890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460890).length < 2 ^ (prefixWord ++ tailWord_1460890).sum := by decide
  have hdescent : baseEnd_1460890 < baseStart_1460890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460978 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1460978 : Nat := 118140960795 + 1460978 * 2 ^ 59
def prefixEnd_1460978 : Nat := 4983230072969 + 3 ^ 40 * 1460978 * 2
def baseEnd_1460978 : Nat := 166707542143220033456909

theorem tailTrace_1460978 : CollatzResearch.WordTrace tailWord_1460978 prefixEnd_1460978 166707542143220033456909 := by
  unfold tailWord_1460978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13321561325283424005647897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35524163534089130681727725 13321561325283424005647897)
  ·
    refine ⟨9991170993962568004235923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13321561325283424005647897 9991170993962568004235923)
    ·
      refine ⟨14986756490943852006353885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9991170993962568004235923 14986756490943852006353885)
      ·
        refine ⟨5620033684103944502382707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14986756490943852006353885 5620033684103944502382707)
        ·
          refine ⟨8430050526155916753574061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5620033684103944502382707 8430050526155916753574061)
          ·
            refine ⟨3161268947308468782590273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8430050526155916753574061 3161268947308468782590273)
            ·
              refine ⟨2370951710481351586942705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161268947308468782590273 2370951710481351586942705)
              ·
                refine ⟨1778213782861013690207029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370951710481351586942705 1778213782861013690207029)
                ·
                  refine ⟨166707542143220033456909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1778213782861013690207029 166707542143220033456909)
                  ·
                    rfl

theorem cell22_1460978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1460978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1460978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1460978 prefixEnd_1460978 := by exact prefixLift 1460978
  have htrace : WordTrace (prefixWord ++ tailWord_1460978) baseStart_1460978 baseEnd_1460978 := by
    simpa [prefixWord, tailWord_1460978, baseEnd_1460978] using wordTrace_append hprefix tailTrace_1460978
  have hstable : (prefixWord ++ tailWord_1460978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460978).length < 2 ^ (prefixWord ++ tailWord_1460978).sum := by decide
  have hdescent : baseEnd_1460978 < baseStart_1460978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461023 : List Nat := [1, 1, 2, 4, 2, 2, 1, 5, 4]
def baseStart_1461023 : Nat := 118140960795 + 1461023 * 2 ^ 59
def prefixEnd_1461023 : Nat := 4983230072969 + 3 ^ 40 * 1461023 * 2
def baseEnd_1461023 : Nat := 166712676949764994331863

theorem tailTrace_1461023 : CollatzResearch.WordTrace tailWord_1461023 prefixEnd_1461023 166712676949764994331863 := by
  unfold tailWord_1461023
  simp only [CollatzResearch.WordTrace]
  refine ⟨53287886585970668707979723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35525257723980445805319815 53287886585970668707979723)
  ·
    refine ⟨79931829878956003061969585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53287886585970668707979723 79931829878956003061969585)
    ·
      refine ⟨59948872409217002296477189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79931829878956003061969585 59948872409217002296477189)
      ·
        refine ⟨11240413576728187930589473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59948872409217002296477189 11240413576728187930589473)
        ·
          refine ⟨8430310182546140947942105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11240413576728187930589473 8430310182546140947942105)
          ·
            refine ⟨6322732636909605710956579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8430310182546140947942105 6322732636909605710956579)
            ·
              refine ⟨9484098955364408566434869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6322732636909605710956579 9484098955364408566434869)
              ·
                refine ⟨889134277065413303103269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9484098955364408566434869 889134277065413303103269)
                ·
                  refine ⟨166712676949764994331863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889134277065413303103269 166712676949764994331863)
                  ·
                    rfl

theorem cell22_1461023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 4].length) (baseStart_1461023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461023 prefixEnd_1461023 := by exact prefixLift 1461023
  have htrace : WordTrace (prefixWord ++ tailWord_1461023) baseStart_1461023 baseEnd_1461023 := by
    simpa [prefixWord, tailWord_1461023, baseEnd_1461023] using wordTrace_append hprefix tailTrace_1461023
  have hstable : (prefixWord ++ tailWord_1461023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461023).length < 2 ^ (prefixWord ++ tailWord_1461023).sum := by decide
  have hdescent : baseEnd_1461023 < baseStart_1461023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461036 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1461036 : Nat := 118140960795 + 1461036 * 2 ^ 59
def prefixEnd_1461036 : Nat := 4983230072969 + 3 ^ 40 * 1461036 * 2
def baseEnd_1461036 : Nat := 500142481014967282420549

theorem tailTrace_1461036 : CollatzResearch.WordTrace tailWord_1461036 prefixEnd_1461036 500142481014967282420549 := by
  unfold tailWord_1461036
  simp only [CollatzResearch.WordTrace]
  refine ⟨26644180367461785964101481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35525573823282381285468641 26644180367461785964101481)
  ·
    refine ⟨19983135275596339473076111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26644180367461785964101481 19983135275596339473076111)
    ·
      refine ⟨29974702913394509209614167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19983135275596339473076111 29974702913394509209614167)
      ·
        refine ⟨44962054370091763814421251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29974702913394509209614167 44962054370091763814421251)
        ·
          refine ⟨67443081555137645721631877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44962054370091763814421251 67443081555137645721631877)
          ·
            refine ⟨12645577791588308572805977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67443081555137645721631877 12645577791588308572805977)
            ·
              refine ⟨9484183343691231429604483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12645577791588308572805977 9484183343691231429604483)
              ·
                refine ⟨14226275015536847144406725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9484183343691231429604483 14226275015536847144406725)
                ·
                  refine ⟨2667426565413158839576261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14226275015536847144406725 2667426565413158839576261)
                  ·
                    refine ⟨500142481014967282420549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667426565413158839576261 500142481014967282420549)
                    ·
                      rfl

theorem cell22_1461036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1461036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461036 prefixEnd_1461036 := by exact prefixLift 1461036
  have htrace : WordTrace (prefixWord ++ tailWord_1461036) baseStart_1461036 baseEnd_1461036 := by
    simpa [prefixWord, tailWord_1461036, baseEnd_1461036] using wordTrace_append hprefix tailTrace_1461036
  have hstable : (prefixWord ++ tailWord_1461036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461036).length < 2 ^ (prefixWord ++ tailWord_1461036).sum := by decide
  have hdescent : baseEnd_1461036 < baseStart_1461036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461068 : List Nat := [2, 2, 1, 3, 3, 1, 4, 6]
def baseStart_1461068 : Nat := 118140960795 + 1461068 * 2 ^ 59
def prefixEnd_1461068 : Nat := 4983230072969 + 3 ^ 40 * 1461068 * 2
def baseEnd_1461068 : Nat := 55572603918769985068939

theorem tailTrace_1461068 : CollatzResearch.WordTrace tailWord_1461068 prefixEnd_1461068 55572603918769985068939 := by
  unfold tailWord_1461068
  simp only [CollatzResearch.WordTrace]
  refine ⟨26644763935403820696683929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35526351913871760928911905 26644763935403820696683929)
  ·
    refine ⟨19983572951552865522512947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26644763935403820696683929 19983572951552865522512947)
    ·
      refine ⟨29975359427329298283769421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19983572951552865522512947 29975359427329298283769421)
      ·
        refine ⟨11240759785248486856413533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29975359427329298283769421 11240759785248486856413533)
        ·
          refine ⟨4215284919468182571155075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11240759785248486856413533 4215284919468182571155075)
          ·
            refine ⟨6322927379202273856732613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4215284919468182571155075 6322927379202273856732613)
            ·
              refine ⟨1185548883600426348137365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6322927379202273856732613 1185548883600426348137365)
              ·
                refine ⟨55572603918769985068939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1185548883600426348137365 55572603918769985068939)
                ·
                  rfl

theorem cell22_1461068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 6].length) (baseStart_1461068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461068 prefixEnd_1461068 := by exact prefixLift 1461068
  have htrace : WordTrace (prefixWord ++ tailWord_1461068) baseStart_1461068 baseEnd_1461068 := by
    simpa [prefixWord, tailWord_1461068, baseEnd_1461068] using wordTrace_append hprefix tailTrace_1461068
  have hstable : (prefixWord ++ tailWord_1461068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461068).length < 2 ^ (prefixWord ++ tailWord_1461068).sum := by decide
  have hdescent : baseEnd_1461068 < baseStart_1461068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461111 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 2, 5]
def baseStart_1461111 : Nat := 118140960795 + 1461111 * 2 ^ 59
def prefixEnd_1461111 : Nat := 4983230072969 + 3 ^ 40 * 1461111 * 2
def baseEnd_1461111 : Nat := 500168155047692086795319

theorem tailTrace_1461111 : CollatzResearch.WordTrace tailWord_1461111 prefixEnd_1461111 500168155047692086795319 := by
  unfold tailWord_1461111
  simp only [CollatzResearch.WordTrace]
  refine ⟨53291096209651859737183187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35527397473101239824788791 53291096209651859737183187)
  ·
    refine ⟨79936644314477789605774781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53291096209651859737183187 79936644314477789605774781)
    ·
      refine ⟨29976241617929171102165543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79936644314477789605774781 29976241617929171102165543)
      ·
        refine ⟨44964362426893756653248315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29976241617929171102165543 44964362426893756653248315)
        ·
          refine ⟨67446543640340634979872473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44964362426893756653248315 67446543640340634979872473)
          ·
            refine ⟨50584907730255476234904355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67446543640340634979872473 50584907730255476234904355)
            ·
              refine ⟨75877361595383214352356533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50584907730255476234904355 75877361595383214352356533)
              ·
                refine ⟨7113502649567176345533425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75877361595383214352356533 7113502649567176345533425)
                ·
                  refine ⟨5335126987175382259150069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7113502649567176345533425 5335126987175382259150069)
                  ·
                    refine ⟨500168155047692086795319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5335126987175382259150069 500168155047692086795319)
                    ·
                      rfl

theorem cell22_1461111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_1461111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461111 prefixEnd_1461111 := by exact prefixLift 1461111
  have htrace : WordTrace (prefixWord ++ tailWord_1461111) baseStart_1461111 baseEnd_1461111 := by
    simpa [prefixWord, tailWord_1461111, baseEnd_1461111] using wordTrace_append hprefix tailTrace_1461111
  have hstable : (prefixWord ++ tailWord_1461111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461111).length < 2 ^ (prefixWord ++ tailWord_1461111).sum := by decide
  have hdescent : baseEnd_1461111 < baseStart_1461111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461113 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 5]
def baseStart_1461113 : Nat := 118140960795 + 1461113 * 2 ^ 59
def prefixEnd_1461113 : Nat := 4983230072969 + 3 ^ 40 * 1461113 * 2
def baseEnd_1461113 : Nat := 166722946562854916081771

theorem tailTrace_1461113 : CollatzResearch.WordTrace tailWord_1461113 prefixEnd_1461113 166722946562854916081771 := by
  unfold tailWord_1461113
  simp only [CollatzResearch.WordTrace]
  refine ⟨53291169155644614078755993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35527446103763076052503995 53291169155644614078755993)
  ·
    refine ⟨39968376866733460559066995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53291169155644614078755993 39968376866733460559066995)
    ·
      refine ⟨59952565300100190838600493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39968376866733460559066995 59952565300100190838600493)
      ·
        refine ⟨22482211987537571564475185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59952565300100190838600493 22482211987537571564475185)
        ·
          refine ⟨16861658990653178673356389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22482211987537571564475185 16861658990653178673356389)
          ·
            refine ⟨3161561060747471001254323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16861658990653178673356389 3161561060747471001254323)
            ·
              refine ⟨4742341591121206501881485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161561060747471001254323 4742341591121206501881485)
              ·
                refine ⟨1778378096670452438205557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4742341591121206501881485 1778378096670452438205557)
                ·
                  refine ⟨166722946562854916081771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1778378096670452438205557 166722946562854916081771)
                  ·
                    rfl

theorem cell22_1461113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_1461113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461113 prefixEnd_1461113 := by exact prefixLift 1461113
  have htrace : WordTrace (prefixWord ++ tailWord_1461113) baseStart_1461113 baseEnd_1461113 := by
    simpa [prefixWord, tailWord_1461113, baseEnd_1461113] using wordTrace_append hprefix tailTrace_1461113
  have hstable : (prefixWord ++ tailWord_1461113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461113).length < 2 ^ (prefixWord ++ tailWord_1461113).sum := by decide
  have hdescent : baseEnd_1461113 < baseStart_1461113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461192 : List Nat := [2, 1, 3, 1, 5, 1, 2, 3, 4]
def baseStart_1461192 : Nat := 118140960795 + 1461192 * 2 ^ 59
def prefixEnd_1461192 : Nat := 4983230072969 + 3 ^ 40 * 1461192 * 2
def baseEnd_1461192 : Nat := 166731961001011625173357

theorem tailTrace_1461192 : CollatzResearch.WordTrace tailWord_1461192 prefixEnd_1461192 166731961001011625173357 := by
  unfold tailWord_1461192
  simp only [CollatzResearch.WordTrace]
  refine ⟨26647025261179205285440915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35529367014905607047254553 26647025261179205285440915)
  ·
    refine ⟨39970537891768807928161373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26647025261179205285440915 39970537891768807928161373)
    ·
      refine ⟨14988951709413302973060515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39970537891768807928161373 14988951709413302973060515)
      ·
        refine ⟨22483427564119954459590773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14988951709413302973060515 22483427564119954459590773)
        ·
          refine ⟨2107821334136245730586635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22483427564119954459590773 2107821334136245730586635)
          ·
            refine ⟨3161732001204368595879953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107821334136245730586635 3161732001204368595879953)
            ·
              refine ⟨2371299000903276446909965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161732001204368595879953 2371299000903276446909965)
              ·
                refine ⟨889237125338728667591237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2371299000903276446909965 889237125338728667591237)
                ·
                  refine ⟨166731961001011625173357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889237125338728667591237 166731961001011625173357)
                  ·
                    rfl

theorem cell22_1461192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 4].length) (baseStart_1461192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461192 prefixEnd_1461192 := by exact prefixLift 1461192
  have htrace : WordTrace (prefixWord ++ tailWord_1461192) baseStart_1461192 baseEnd_1461192 := by
    simpa [prefixWord, tailWord_1461192, baseEnd_1461192] using wordTrace_append hprefix tailTrace_1461192
  have hstable : (prefixWord ++ tailWord_1461192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461192).length < 2 ^ (prefixWord ++ tailWord_1461192).sum := by decide
  have hdescent : baseEnd_1461192 < baseStart_1461192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461237 : List Nat := [1, 3, 5, 2, 1, 1, 1, 8]
def baseStart_1461237 : Nat := 118140960795 + 1461237 * 2 ^ 59
def prefixEnd_1461237 : Nat := 4983230072969 + 3 ^ 40 * 1461237 * 2
def baseEnd_1461237 : Nat := 55579031935852195349437

theorem tailTrace_1461237 : CollatzResearch.WordTrace tailWord_1461237 prefixEnd_1461237 55579031935852195349437 := by
  unfold tailWord_1461237
  simp only [CollatzResearch.WordTrace]
  refine ⟨53295691807195383256269965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35530461204796922170846643 53295691807195383256269965)
  ·
    refine ⟨19985884427698268721101237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53295691807195383256269965 19985884427698268721101237)
    ·
      refine ⟨1873676665096712692603241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19985884427698268721101237 1873676665096712692603241)
      ·
        refine ⟨1405257498822534519452431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1873676665096712692603241 1405257498822534519452431)
        ·
          refine ⟨2107886248233801779178647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405257498822534519452431 2107886248233801779178647)
          ·
            refine ⟨3161829372350702668767971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107886248233801779178647 3161829372350702668767971)
            ·
              refine ⟨4742744058526054003151957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161829372350702668767971 4742744058526054003151957)
              ·
                refine ⟨55579031935852195349437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4742744058526054003151957 55579031935852195349437)
                ·
                  rfl

theorem cell22_1461237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 8].length) (baseStart_1461237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461237 prefixEnd_1461237 := by exact prefixLift 1461237
  have htrace : WordTrace (prefixWord ++ tailWord_1461237) baseStart_1461237 baseEnd_1461237 := by
    simpa [prefixWord, tailWord_1461237, baseEnd_1461237] using wordTrace_append hprefix tailTrace_1461237
  have hstable : (prefixWord ++ tailWord_1461237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461237).length < 2 ^ (prefixWord ++ tailWord_1461237).sum := by decide
  have hdescent : baseEnd_1461237 < baseStart_1461237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461282 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1461282 : Nat := 118140960795 + 1461282 * 2 ^ 59
def prefixEnd_1461282 : Nat := 4983230072969 + 3 ^ 40 * 1461282 * 2
def baseEnd_1461282 : Nat := 166742230614101546923265

theorem tailTrace_1461282 : CollatzResearch.WordTrace tailWord_1461282 prefixEnd_1461282 166742230614101546923265 := by
  unfold tailWord_1461282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13324333273008088985414525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35531555394688237294438733 13324333273008088985414525)
  ·
    refine ⟨4996624977378033369530447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13324333273008088985414525 4996624977378033369530447)
    ·
      refine ⟨7494937466067050054295671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4996624977378033369530447 7494937466067050054295671)
      ·
        refine ⟨11242406199100575081443507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7494937466067050054295671 11242406199100575081443507)
        ·
          refine ⟨16863609298650862622165261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11242406199100575081443507 16863609298650862622165261)
          ·
            refine ⟨6323853486994073483311973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16863609298650862622165261 6323853486994073483311973)
            ·
              refine ⟨1185722528811388778120995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6323853486994073483311973 1185722528811388778120995)
              ·
                refine ⟨1778583793217083167181493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185722528811388778120995 1778583793217083167181493)
                ·
                  refine ⟨166742230614101546923265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1778583793217083167181493 166742230614101546923265)
                  ·
                    rfl

theorem cell22_1461282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1461282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461282 prefixEnd_1461282 := by exact prefixLift 1461282
  have htrace : WordTrace (prefixWord ++ tailWord_1461282) baseStart_1461282 baseEnd_1461282 := by
    simpa [prefixWord, tailWord_1461282, baseEnd_1461282] using wordTrace_append hprefix tailTrace_1461282
  have hstable : (prefixWord ++ tailWord_1461282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461282).length < 2 ^ (prefixWord ++ tailWord_1461282).sum := by decide
  have hdescent : baseEnd_1461282 < baseStart_1461282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461312 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 1, 4]
def baseStart_1461312 : Nat := 118140960795 + 1461312 * 2 ^ 59
def prefixEnd_1461312 : Nat := 4983230072969 + 3 ^ 40 * 1461312 * 2
def baseEnd_1461312 : Nat := 500236961455394562519703

theorem tailTrace_1461312 : CollatzResearch.WordTrace tailWord_1461312 prefixEnd_1461312 500236961455394562519703 := by
  unfold tailWord_1461312
  simp only [CollatzResearch.WordTrace]
  refine ⟨26649213640961835532625095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35532284854615780710166793 26649213640961835532625095)
  ·
    refine ⟨39973820461442753298937643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26649213640961835532625095 39973820461442753298937643)
    ·
      refine ⟨59960730692164129948406465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39973820461442753298937643 59960730692164129948406465)
      ·
        refine ⟨44970548019123097461304849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59960730692164129948406465 44970548019123097461304849)
        ·
          refine ⟨33727911014342323095978637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44970548019123097461304849 33727911014342323095978637)
          ·
            refine ⟨12647966630378371160991989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33727911014342323095978637 12647966630378371160991989)
            ·
              refine ⟨1185746871597972296342999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12647966630378371160991989 1185746871597972296342999)
              ·
                refine ⟨1778620307396958444514499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185746871597972296342999 1778620307396958444514499)
                ·
                  refine ⟨2667930461095437666771749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778620307396958444514499 2667930461095437666771749)
                  ·
                    refine ⟨500236961455394562519703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2667930461095437666771749 500236961455394562519703)
                    ·
                      rfl

theorem cell22_1461312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 4].length) (baseStart_1461312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461312 prefixEnd_1461312 := by exact prefixLift 1461312
  have htrace : WordTrace (prefixWord ++ tailWord_1461312) baseStart_1461312 baseEnd_1461312 := by
    simpa [prefixWord, tailWord_1461312, baseEnd_1461312] using wordTrace_append hprefix tailTrace_1461312
  have hstable : (prefixWord ++ tailWord_1461312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461312).length < 2 ^ (prefixWord ++ tailWord_1461312).sum := by decide
  have hdescent : baseEnd_1461312 < baseStart_1461312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461338 : List Nat := [3, 1, 1, 2, 1, 1, 2, 11]
def baseStart_1461338 : Nat := 118140960795 + 1461338 * 2 ^ 59
def prefixEnd_1461338 : Nat := 4983230072969 + 3 ^ 40 * 1461338 * 2
def baseEnd_1461338 : Nat := 55582873531859906818847

theorem tailTrace_1461338 : CollatzResearch.WordTrace tailWord_1461338 prefixEnd_1461338 55582873531859906818847 := by
  unfold tailWord_1461338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13324843894957369376424167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35532917053219651670464445 13324843894957369376424167)
  ·
    refine ⟨19987265842436054064636251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13324843894957369376424167 19987265842436054064636251)
    ·
      refine ⟨29980898763654081096954377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19987265842436054064636251 29980898763654081096954377)
      ·
        refine ⟨22485674072740560822715783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29980898763654081096954377 22485674072740560822715783)
        ·
          refine ⟨33728511109110841234073675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22485674072740560822715783 33728511109110841234073675)
          ·
            refine ⟨50592766663666261851110513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33728511109110841234073675 50592766663666261851110513)
            ·
              refine ⟨37944574997749696388332885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50592766663666261851110513 37944574997749696388332885)
              ·
                refine ⟨55582873531859906818847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37944574997749696388332885 55582873531859906818847)
                ·
                  rfl

theorem cell22_1461338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_1461338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461338 prefixEnd_1461338 := by exact prefixLift 1461338
  have htrace : WordTrace (prefixWord ++ tailWord_1461338) baseStart_1461338 baseEnd_1461338 := by
    simpa [prefixWord, tailWord_1461338, baseEnd_1461338] using wordTrace_append hprefix tailTrace_1461338
  have hstable : (prefixWord ++ tailWord_1461338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461338).length < 2 ^ (prefixWord ++ tailWord_1461338).sum := by decide
  have hdescent : baseEnd_1461338 < baseStart_1461338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461340 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1461340 : Nat := 118140960795 + 1461340 * 2 ^ 59
def prefixEnd_1461340 : Nat := 4983230072969 + 3 ^ 40 * 1461340 * 2
def baseEnd_1461340 : Nat := 500246546427611822819617

theorem tailTrace_1461340 : CollatzResearch.WordTrace tailWord_1461340 prefixEnd_1461340 500246546427611822819617 := by
  unfold tailWord_1461340
  simp only [CollatzResearch.WordTrace]
  refine ⟨26649724262911115923634737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35532965683881487898179649 26649724262911115923634737)
  ·
    refine ⟨19987293197183336942726053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26649724262911115923634737 19987293197183336942726053)
    ·
      refine ⟨3747617474471875676761135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19987293197183336942726053 3747617474471875676761135)
      ·
        refine ⟨5621426211707813515141703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3747617474471875676761135 5621426211707813515141703)
        ·
          refine ⟨8432139317561720272712555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5621426211707813515141703 8432139317561720272712555)
          ·
            refine ⟨12648208976342580409068833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8432139317561720272712555 12648208976342580409068833)
            ·
              refine ⟨9486156732256935306801625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12648208976342580409068833 9486156732256935306801625)
              ·
                refine ⟨7114617549192701480101219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9486156732256935306801625 7114617549192701480101219)
                ·
                  refine ⟨10671926323789052220151829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7114617549192701480101219 10671926323789052220151829)
                  ·
                    refine ⟨500246546427611822819617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10671926323789052220151829 500246546427611822819617)
                    ·
                      rfl

theorem cell22_1461340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1461340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461340 prefixEnd_1461340 := by exact prefixLift 1461340
  have htrace : WordTrace (prefixWord ++ tailWord_1461340) baseStart_1461340 baseEnd_1461340 := by
    simpa [prefixWord, tailWord_1461340, baseEnd_1461340] using wordTrace_append hprefix tailTrace_1461340
  have hstable : (prefixWord ++ tailWord_1461340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461340).length < 2 ^ (prefixWord ++ tailWord_1461340).sum := by decide
  have hdescent : baseEnd_1461340 < baseStart_1461340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461357 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_1461357 : Nat := 118140960795 + 1461357 * 2 ^ 59
def prefixEnd_1461357 : Nat := 4983230072969 + 3 ^ 40 * 1461357 * 2
def baseEnd_1461357 : Nat := 500252365875029445144565

theorem tailTrace_1461357 : CollatzResearch.WordTrace tailWord_1461357 prefixEnd_1461357 500252365875029445144565 := by
  unfold tailWord_1461357
  simp only [CollatzResearch.WordTrace]
  refine ⟨53300068566760643750638325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35533379044507095833758883 53300068566760643750638325)
  ·
    refine ⟨4996881428133810351622343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53300068566760643750638325 4996881428133810351622343)
    ·
      refine ⟨7495322142200715527433515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4996881428133810351622343 7495322142200715527433515)
      ·
        refine ⟨11242983213301073291150273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7495322142200715527433515 11242983213301073291150273)
        ·
          refine ⟨8432237409975804968362705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11242983213301073291150273 8432237409975804968362705)
          ·
            refine ⟨6324178057481853726272029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8432237409975804968362705 6324178057481853726272029)
            ·
              refine ⟨2371566771555695147352011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6324178057481853726272029 2371566771555695147352011)
              ·
                refine ⟨3557350157333542721028017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371566771555695147352011 3557350157333542721028017)
                ·
                  refine ⟨2668012618000157040771013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3557350157333542721028017 2668012618000157040771013)
                  ·
                    refine ⟨500252365875029445144565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668012618000157040771013 500252365875029445144565)
                    ·
                      rfl

theorem cell22_1461357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_1461357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461357 prefixEnd_1461357 := by exact prefixLift 1461357
  have htrace : WordTrace (prefixWord ++ tailWord_1461357) baseStart_1461357 baseEnd_1461357 := by
    simpa [prefixWord, tailWord_1461357, baseEnd_1461357] using wordTrace_append hprefix tailTrace_1461357
  have hstable : (prefixWord ++ tailWord_1461357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461357).length < 2 ^ (prefixWord ++ tailWord_1461357).sum := by decide
  have hdescent : baseEnd_1461357 < baseStart_1461357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461438 : List Nat := [4, 2, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_1461438 : Nat := 118140960795 + 1461438 * 2 ^ 59
def prefixEnd_1461438 : Nat := 4983230072969 + 3 ^ 40 * 1461438 * 2
def baseEnd_1461438 : Nat := 500280093830372233869317

theorem tailTrace_1461438 : CollatzResearch.WordTrace tailWord_1461438 prefixEnd_1461438 500280093830372233869317 := by
  unfold tailWord_1461438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6662877859933399323042121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35535348586311463056224645 6662877859933399323042121)
  ·
    refine ⟨4997158394950049492281591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6662877859933399323042121 4997158394950049492281591)
    ·
      refine ⟨7495737592425074238422387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4997158394950049492281591 7495737592425074238422387)
      ·
        refine ⟨11243606388637611357633581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7495737592425074238422387 11243606388637611357633581)
        ·
          refine ⟨4216352395739104259112593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11243606388637611357633581 4216352395739104259112593)
          ·
            refine ⟨3162264296804328194334445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4216352395739104259112593 3162264296804328194334445)
            ·
              refine ⟨1185849111301623072875417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3162264296804328194334445 1185849111301623072875417)
              ·
                refine ⟨889386833476217304656563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185849111301623072875417 889386833476217304656563)
                ·
                  refine ⟨1334080250214325956984845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889386833476217304656563 1334080250214325956984845)
                  ·
                    refine ⟨500280093830372233869317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334080250214325956984845 500280093830372233869317)
                    ·
                      rfl

theorem cell22_1461438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_1461438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461438 prefixEnd_1461438 := by exact prefixLift 1461438
  have htrace : WordTrace (prefixWord ++ tailWord_1461438) baseStart_1461438 baseEnd_1461438 := by
    simpa [prefixWord, tailWord_1461438, baseEnd_1461438] using wordTrace_append hprefix tailTrace_1461438
  have hstable : (prefixWord ++ tailWord_1461438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461438).length < 2 ^ (prefixWord ++ tailWord_1461438).sum := by decide
  have hdescent : baseEnd_1461438 < baseStart_1461438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461490 : List Nat := [3, 2, 1, 3, 13]
def baseStart_1461490 : Nat := 118140960795 + 1461490 * 2 ^ 59
def prefixEnd_1461490 : Nat := 4983230072969 + 3 ^ 40 * 1461490 * 2
def baseEnd_1461490 : Nat := 2058839071987907125799

theorem tailTrace_1461490 : CollatzResearch.WordTrace tailWord_1461490 prefixEnd_1461490 2058839071987907125799 := by
  unfold tailWord_1461490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326229868819701866307481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35536612983519204976819949 13326229868819701866307481)
  ·
    refine ⟨9994672401614776399730611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13326229868819701866307481 9994672401614776399730611)
    ·
      refine ⟨14992008602422164599595917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9994672401614776399730611 14992008602422164599595917)
      ·
        refine ⟨5622003225908311724848469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14992008602422164599595917 5622003225908311724848469)
        ·
          refine ⟨2058839071987907125799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 5622003225908311724848469 2058839071987907125799)
          ·
            rfl

theorem cell22_1461490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 13].length) (baseStart_1461490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461490 prefixEnd_1461490 := by exact prefixLift 1461490
  have htrace : WordTrace (prefixWord ++ tailWord_1461490) baseStart_1461490 baseEnd_1461490 := by
    simpa [prefixWord, tailWord_1461490, baseEnd_1461490] using wordTrace_append hprefix tailTrace_1461490
  have hstable : (prefixWord ++ tailWord_1461490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461490).length < 2 ^ (prefixWord ++ tailWord_1461490).sum := by decide
  have hdescent : baseEnd_1461490 < baseStart_1461490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461507 : List Nat := [1, 1, 1, 3, 2, 6, 1, 7]
def baseStart_1461507 : Nat := 118140960795 + 1461507 * 2 ^ 59
def prefixEnd_1461507 : Nat := 4983230072969 + 3 ^ 40 * 1461507 * 2
def baseEnd_1461507 : Nat := 55589301548942117099345

theorem tailTrace_1461507 : CollatzResearch.WordTrace tailWord_1461507 prefixEnd_1461507 55589301548942117099345 := by
  unfold tailWord_1461507
  simp only [CollatzResearch.WordTrace]
  refine ⟨53305539516217219368598775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35537026344144812912399183 53305539516217219368598775)
  ·
    refine ⟨79958309274325829052898163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53305539516217219368598775 79958309274325829052898163)
    ·
      refine ⟨119937463911488743579347245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79958309274325829052898163 119937463911488743579347245)
      ·
        refine ⟨44976548966808278842255217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119937463911488743579347245 44976548966808278842255217)
        ·
          refine ⟨33732411725106209131691413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44976548966808278842255217 33732411725106209131691413)
          ·
            refine ⟨1581206799614353553048035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33732411725106209131691413 1581206799614353553048035)
            ·
              refine ⟨2371810199421530329572053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581206799614353553048035 2371810199421530329572053)
              ·
                refine ⟨55589301548942117099345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2371810199421530329572053 55589301548942117099345)
                ·
                  rfl

theorem cell22_1461507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 7].length) (baseStart_1461507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461507 prefixEnd_1461507 := by exact prefixLift 1461507
  have htrace : WordTrace (prefixWord ++ tailWord_1461507) baseStart_1461507 baseEnd_1461507 := by
    simpa [prefixWord, tailWord_1461507, baseEnd_1461507] using wordTrace_append hprefix tailTrace_1461507
  have hstable : (prefixWord ++ tailWord_1461507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461507).length < 2 ^ (prefixWord ++ tailWord_1461507).sum := by decide
  have hdescent : baseEnd_1461507 < baseStart_1461507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461556 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1461556 : Nat := 118140960795 + 1461556 * 2 ^ 59
def prefixEnd_1461556 : Nat := 4983230072969 + 3 ^ 40 * 1461556 * 2
def baseEnd_1461556 : Nat := 500320487641859259418955

theorem tailTrace_1461556 : CollatzResearch.WordTrace tailWord_1461556 prefixEnd_1461556 500320487641859259418955 := by
  unfold tailWord_1461556
  simp only [CollatzResearch.WordTrace]
  refine ⟨26653663346519850368566261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35538217795359800491421681 26653663346519850368566261)
  ·
    refine ⟨2498780938736235972053087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26653663346519850368566261 2498780938736235972053087)
    ·
      refine ⟨3748171408104353958079631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498780938736235972053087 3748171408104353958079631)
      ·
        refine ⟨5622257112156530937119447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748171408104353958079631 5622257112156530937119447)
        ·
          refine ⟨8433385668234796405679171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5622257112156530937119447 8433385668234796405679171)
          ·
            refine ⟨12650078502352194608518757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433385668234796405679171 12650078502352194608518757)
            ·
              refine ⟨2371889719191036489097267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12650078502352194608518757 2371889719191036489097267)
              ·
                refine ⟨3557834578786554733645901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371889719191036489097267 3557834578786554733645901)
                ·
                  refine ⟨1334187967044958025117213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3557834578786554733645901 1334187967044958025117213)
                  ·
                    refine ⟨500320487641859259418955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334187967044958025117213 500320487641859259418955)
                    ·
                      rfl

theorem cell22_1461556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1461556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461556 prefixEnd_1461556 := by exact prefixLift 1461556
  have htrace : WordTrace (prefixWord ++ tailWord_1461556) baseStart_1461556 baseEnd_1461556 := by
    simpa [prefixWord, tailWord_1461556, baseEnd_1461556] using wordTrace_append hprefix tailTrace_1461556
  have hstable : (prefixWord ++ tailWord_1461556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461556).length < 2 ^ (prefixWord ++ tailWord_1461556).sum := by decide
  have hdescent : baseEnd_1461556 < baseStart_1461556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461567 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 2, 5]
def baseStart_1461567 : Nat := 118140960795 + 1461567 * 2 ^ 59
def prefixEnd_1461567 : Nat := 4983230072969 + 3 ^ 40 * 1461567 * 2
def baseEnd_1461567 : Nat := 500324253166658897393921

theorem tailTrace_1461567 : CollatzResearch.WordTrace tailWord_1461567 prefixEnd_1461567 500324253166658897393921 := by
  unfold tailWord_1461567
  simp only [CollatzResearch.WordTrace]
  refine ⟨53307727895999849615782955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35538485263999899743855303 53307727895999849615782955)
  ·
    refine ⟨79961591843999774423674433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53307727895999849615782955 79961591843999774423674433)
    ·
      refine ⟨59971193882999830817755825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79961591843999774423674433 59971193882999830817755825)
      ·
        refine ⟨44978395412249873113316869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59971193882999830817755825 44978395412249873113316869)
        ·
          refine ⟨8433449139796851208746913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44978395412249873113316869 8433449139796851208746913)
          ·
            refine ⟨6325086854847638406560185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8433449139796851208746913 6325086854847638406560185)
            ·
              refine ⟨4743815141135728804920139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6325086854847638406560185 4743815141135728804920139)
              ·
                refine ⟨7115722711703593207380209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743815141135728804920139 7115722711703593207380209)
                ·
                  refine ⟨5336792033777694905535157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7115722711703593207380209 5336792033777694905535157)
                  ·
                    refine ⟨500324253166658897393921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5336792033777694905535157 500324253166658897393921)
                    ·
                      rfl

theorem cell22_1461567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_1461567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461567 prefixEnd_1461567 := by exact prefixLift 1461567
  have htrace : WordTrace (prefixWord ++ tailWord_1461567) baseStart_1461567 baseEnd_1461567 := by
    simpa [prefixWord, tailWord_1461567, baseEnd_1461567] using wordTrace_append hprefix tailTrace_1461567
  have hstable : (prefixWord ++ tailWord_1461567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461567).length < 2 ^ (prefixWord ++ tailWord_1461567).sum := by decide
  have hdescent : baseEnd_1461567 < baseStart_1461567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461627 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 4, 4]
def baseStart_1461627 : Nat := 118140960795 + 1461627 * 2 ^ 59
def prefixEnd_1461627 : Nat := 4983230072969 + 3 ^ 40 * 1461627 * 2
def baseEnd_1461627 : Nat := 500344792392838740893737

theorem tailTrace_1461627 : CollatzResearch.WordTrace tailWord_1461627 prefixEnd_1461627 500344792392838740893737 := by
  unfold tailWord_1461627
  simp only [CollatzResearch.WordTrace]
  refine ⟨53309916275782479862967135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35539944183854986575311423 53309916275782479862967135)
  ·
    refine ⟨79964874413673719794450703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53309916275782479862967135 79964874413673719794450703)
    ·
      refine ⟨119947311620510579691676055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79964874413673719794450703 119947311620510579691676055)
      ·
        refine ⟨179920967430765869537514083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119947311620510579691676055 179920967430765869537514083)
        ·
          refine ⟨269881451146148804306271125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179920967430765869537514083 269881451146148804306271125)
          ·
            refine ⟨12650693022475725201856459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 269881451146148804306271125 12650693022475725201856459)
            ·
              refine ⟨18976039533713587802784689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12650693022475725201856459 18976039533713587802784689)
              ·
                refine ⟨14232029650285190852088517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18976039533713587802784689 14232029650285190852088517)
                ·
                  refine ⟨2668505559428473284766597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14232029650285190852088517 2668505559428473284766597)
                  ·
                    refine ⟨500344792392838740893737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668505559428473284766597 500344792392838740893737)
                    ·
                      rfl

theorem cell22_1461627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 4].length) (baseStart_1461627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461627 prefixEnd_1461627 := by exact prefixLift 1461627
  have htrace : WordTrace (prefixWord ++ tailWord_1461627) baseStart_1461627 baseEnd_1461627 := by
    simpa [prefixWord, tailWord_1461627, baseEnd_1461627] using wordTrace_append hprefix tailTrace_1461627
  have hstable : (prefixWord ++ tailWord_1461627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461627).length < 2 ^ (prefixWord ++ tailWord_1461627).sum := by decide
  have hdescent : baseEnd_1461627 < baseStart_1461627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461633 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1461633 : Nat := 118140960795 + 1461633 * 2 ^ 59
def prefixEnd_1461633 : Nat := 4983230072969 + 3 ^ 40 * 1461633 * 2
def baseEnd_1461633 : Nat := 500346846315456725243719

theorem tailTrace_1461633 : CollatzResearch.WordTrace tailWord_1461633 prefixEnd_1461633 500346846315456725243719 := by
  unfold tailWord_1461633
  simp only [CollatzResearch.WordTrace]
  refine ⟨53310135113760742887685553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35540090075840495258457035 53310135113760742887685553)
  ·
    refine ⟨39982601335320557165764165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53310135113760742887685553 39982601335320557165764165)
    ·
      refine ⟨7496737750372604468580781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39982601335320557165764165 7496737750372604468580781)
      ·
        refine ⟨2811276656389726675717793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7496737750372604468580781 2811276656389726675717793)
        ·
          refine ⟨2108457492292295006788345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2811276656389726675717793 2108457492292295006788345)
          ·
            refine ⟨1581343119219221255091259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2108457492292295006788345 1581343119219221255091259)
            ·
              refine ⟨2372014678828831882636889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581343119219221255091259 2372014678828831882636889)
              ·
                refine ⟨1779011009121623911977667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372014678828831882636889 1779011009121623911977667)
                ·
                  refine ⟨2668516513682435867966501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779011009121623911977667 2668516513682435867966501)
                  ·
                    refine ⟨500346846315456725243719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668516513682435867966501 500346846315456725243719)
                    ·
                      rfl

theorem cell22_1461633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1461633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461633 prefixEnd_1461633 := by exact prefixLift 1461633
  have htrace : WordTrace (prefixWord ++ tailWord_1461633) baseStart_1461633 baseEnd_1461633 := by
    simpa [prefixWord, tailWord_1461633, baseEnd_1461633] using wordTrace_append hprefix tailTrace_1461633
  have hstable : (prefixWord ++ tailWord_1461633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461633).length < 2 ^ (prefixWord ++ tailWord_1461633).sum := by decide
  have hdescent : baseEnd_1461633 < baseStart_1461633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461644 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_1461644 : Nat := 118140960795 + 1461644 * 2 ^ 59
def prefixEnd_1461644 : Nat := 4983230072969 + 3 ^ 40 * 1461644 * 2
def baseEnd_1461644 : Nat := 500350611840256363218685

theorem tailTrace_1461644 : CollatzResearch.WordTrace tailWord_1461644 prefixEnd_1461644 500350611840256363218685 := by
  unfold tailWord_1461644
  simp only [CollatzResearch.WordTrace]
  refine ⟨26655268158360445883167993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35540357544480594510890657 26655268158360445883167993)
  ·
    refine ⟨19991451118770334412375995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26655268158360445883167993 19991451118770334412375995)
    ·
      refine ⟨29987176678155501618563993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19991451118770334412375995 29987176678155501618563993)
      ·
        refine ⟨22490382508616626213922995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29987176678155501618563993 22490382508616626213922995)
        ·
          refine ⟨33735573762924939320884493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22490382508616626213922995 33735573762924939320884493)
          ·
            refine ⟨12650840161096852245331685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33735573762924939320884493 12650840161096852245331685)
            ·
              refine ⟨2372032530205659795999691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12650840161096852245331685 2372032530205659795999691)
              ·
                refine ⟨3558048795308489693999537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2372032530205659795999691 3558048795308489693999537)
                ·
                  refine ⟨2668536596481367270499653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3558048795308489693999537 2668536596481367270499653)
                  ·
                    refine ⟨500350611840256363218685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668536596481367270499653 500350611840256363218685)
                    ·
                      rfl

theorem cell22_1461644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_1461644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461644 prefixEnd_1461644 := by exact prefixLift 1461644
  have htrace : WordTrace (prefixWord ++ tailWord_1461644) baseStart_1461644 baseEnd_1461644 := by
    simpa [prefixWord, tailWord_1461644, baseEnd_1461644] using wordTrace_append hprefix tailTrace_1461644
  have hstable : (prefixWord ++ tailWord_1461644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461644).length < 2 ^ (prefixWord ++ tailWord_1461644).sum := by decide
  have hdescent : baseEnd_1461644 < baseStart_1461644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461646 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1461646 : Nat := 118140960795 + 1461646 * 2 ^ 59
def prefixEnd_1461646 : Nat := 4983230072969 + 3 ^ 40 * 1461646 * 2
def baseEnd_1461646 : Nat := 500351296481129024668679

theorem tailTrace_1461646 : CollatzResearch.WordTrace tailWord_1461646 prefixEnd_1461646 500351296481129024668679 := by
  unfold tailWord_1461646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663826157839205763488599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35540406175142430738605861 6663826157839205763488599)
  ·
    refine ⟨9995739236758808645232899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6663826157839205763488599 9995739236758808645232899)
    ·
      refine ⟨14993608855138212967849349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9995739236758808645232899 14993608855138212967849349)
      ·
        refine ⟨2811301660338414931471753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14993608855138212967849349 2811301660338414931471753)
        ·
          refine ⟨2108476245253811198603815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2811301660338414931471753 2108476245253811198603815)
          ·
            refine ⟨3162714367880716797905723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108476245253811198603815 3162714367880716797905723)
            ·
              refine ⟨4744071551821075196858585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162714367880716797905723 4744071551821075196858585)
              ·
                refine ⟨3558053663865806397643939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744071551821075196858585 3558053663865806397643939)
                ·
                  refine ⟨5337080495798709596465909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3558053663865806397643939 5337080495798709596465909)
                  ·
                    refine ⟨500351296481129024668679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5337080495798709596465909 500351296481129024668679)
                    ·
                      rfl

theorem cell22_1461646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1461646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461646 prefixEnd_1461646 := by exact prefixLift 1461646
  have htrace : WordTrace (prefixWord ++ tailWord_1461646) baseStart_1461646 baseEnd_1461646 := by
    simpa [prefixWord, tailWord_1461646, baseEnd_1461646] using wordTrace_append hprefix tailTrace_1461646
  have hstable : (prefixWord ++ tailWord_1461646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461646).length < 2 ^ (prefixWord ++ tailWord_1461646).sum := by decide
  have hdescent : baseEnd_1461646 < baseStart_1461646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461650 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1461650 : Nat := 118140960795 + 1461650 * 2 ^ 59
def prefixEnd_1461650 : Nat := 4983230072969 + 3 ^ 40 * 1461650 * 2
def baseEnd_1461650 : Nat := 500352665762874347568667

theorem tailTrace_1461650 : CollatzResearch.WordTrace tailWord_1461650 prefixEnd_1461650 500352665762874347568667 := by
  unfold tailWord_1461650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327688788674788697763601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35540503436466103194036269 13327688788674788697763601)
  ·
    refine ⟨9995766591506091523322701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13327688788674788697763601 9995766591506091523322701)
    ·
      refine ⟨3748412471814784321246013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9995766591506091523322701 3748412471814784321246013)
      ·
        refine ⟨1405654676930544120467255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3748412471814784321246013 1405654676930544120467255)
        ·
          refine ⟨2108482015395816180700883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405654676930544120467255 2108482015395816180700883)
          ·
            refine ⟨3162723023093724271051325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108482015395816180700883 3162723023093724271051325)
            ·
              refine ⟨1186021133660146601644247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3162723023093724271051325 1186021133660146601644247)
              ·
                refine ⟨1779031700490219902466371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186021133660146601644247 1779031700490219902466371)
                ·
                  refine ⟨2668547550735329853699557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1779031700490219902466371 2668547550735329853699557)
                  ·
                    refine ⟨500352665762874347568667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668547550735329853699557 500352665762874347568667)
                    ·
                      rfl

theorem cell22_1461650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1461650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461650 prefixEnd_1461650 := by exact prefixLift 1461650
  have htrace : WordTrace (prefixWord ++ tailWord_1461650) baseStart_1461650 baseEnd_1461650 := by
    simpa [prefixWord, tailWord_1461650, baseEnd_1461650] using wordTrace_append hprefix tailTrace_1461650
  have hstable : (prefixWord ++ tailWord_1461650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461650).length < 2 ^ (prefixWord ++ tailWord_1461650).sum := by decide
  have hdescent : baseEnd_1461650 < baseStart_1461650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461708 : List Nat := [2, 2, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_1461708 : Nat := 118140960795 + 1461708 * 2 ^ 59
def prefixEnd_1461708 : Nat := 4983230072969 + 3 ^ 40 * 1461708 * 2
def baseEnd_1461708 : Nat := 500372520348181529618489

theorem tailTrace_1461708 : CollatzResearch.WordTrace tailWord_1461708 prefixEnd_1461708 500372520348181529618489 := by
  unfold tailWord_1461708
  simp only [CollatzResearch.WordTrace]
  refine ⟨26656435294244515348332889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35541913725659353797777185 26656435294244515348332889)
  ·
    refine ⟨19992326470683386511249667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26656435294244515348332889 19992326470683386511249667)
    ·
      refine ⟨29988489706025079766874501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19992326470683386511249667 29988489706025079766874501)
      ·
        refine ⟨5622841819879702456288969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29988489706025079766874501 5622841819879702456288969)
        ·
          refine ⟨4217131364909776842216727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5622841819879702456288969 4217131364909776842216727)
          ·
            refine ⟨6325697047364665263325091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4217131364909776842216727 6325697047364665263325091)
            ·
              refine ⟨9488545571046997894987637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6325697047364665263325091 9488545571046997894987637)
              ·
                refine ⟨889551147285656052655091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9488545571046997894987637 889551147285656052655091)
                ·
                  refine ⟨1334326720928484078982637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889551147285656052655091 1334326720928484078982637)
                  ·
                    refine ⟨500372520348181529618489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334326720928484078982637 500372520348181529618489)
                    ·
                      rfl

theorem cell22_1461708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_1461708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461708 prefixEnd_1461708 := by exact prefixLift 1461708
  have htrace : WordTrace (prefixWord ++ tailWord_1461708) baseStart_1461708 baseEnd_1461708 := by
    simpa [prefixWord, tailWord_1461708, baseEnd_1461708] using wordTrace_append hprefix tailTrace_1461708
  have hstable : (prefixWord ++ tailWord_1461708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461708).length < 2 ^ (prefixWord ++ tailWord_1461708).sum := by decide
  have hdescent : baseEnd_1461708 < baseStart_1461708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461721 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 5]
def baseStart_1461721 : Nat := 118140960795 + 1461721 * 2 ^ 59
def prefixEnd_1461721 : Nat := 4983230072969 + 3 ^ 40 * 1461721 * 2
def baseEnd_1461721 : Nat := 166792323504617943014483

theorem tailTrace_1461721 : CollatzResearch.WordTrace tailWord_1461721 prefixEnd_1461721 166792323504617943014483 := by
  unfold tailWord_1461721
  simp only [CollatzResearch.WordTrace]
  refine ⟨53313344737441933916889017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35542229824961289277926011 53313344737441933916889017)
  ·
    refine ⟨39985008553081450437666763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53313344737441933916889017 39985008553081450437666763)
    ·
      refine ⟨59977512829622175656500145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39985008553081450437666763 59977512829622175656500145)
      ·
        refine ⟨44983134622216631742375109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59977512829622175656500145 44983134622216631742375109)
        ·
          refine ⟨8434337741665618451695333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44983134622216631742375109 8434337741665618451695333)
          ·
            refine ⟨1581438326562303459692875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8434337741665618451695333 1581438326562303459692875)
            ·
              refine ⟨2372157489843455189539313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581438326562303459692875 2372157489843455189539313)
              ·
                refine ⟨1779118117382591392154485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372157489843455189539313 1779118117382591392154485)
                ·
                  refine ⟨166792323504617943014483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1779118117382591392154485 166792323504617943014483)
                  ·
                    rfl

theorem cell22_1461721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_1461721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461721 prefixEnd_1461721 := by exact prefixLift 1461721
  have htrace : WordTrace (prefixWord ++ tailWord_1461721) baseStart_1461721 baseEnd_1461721 := by
    simpa [prefixWord, tailWord_1461721, baseEnd_1461721] using wordTrace_append hprefix tailTrace_1461721
  have hstable : (prefixWord ++ tailWord_1461721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461721).length < 2 ^ (prefixWord ++ tailWord_1461721).sum := by decide
  have hdescent : baseEnd_1461721 < baseStart_1461721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461738 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_1461738 : Nat := 118140960795 + 1461738 * 2 ^ 59
def prefixEnd_1461738 : Nat := 4983230072969 + 3 ^ 40 * 1461738 * 2
def baseEnd_1461738 : Nat := 166794263320423817122799

theorem tailTrace_1461738 : CollatzResearch.WordTrace tailWord_1461738 prefixEnd_1461738 166794263320423817122799 := by
  unfold tailWord_1461738
  simp only [CollatzResearch.WordTrace]
  refine ⟨13328491194595086455064467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35542643185586897213505245 13328491194595086455064467)
  ·
    refine ⟨19992736791892629682596701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13328491194595086455064467 19992736791892629682596701)
    ·
      refine ⟨7497276296959736130973763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19992736791892629682596701 7497276296959736130973763)
      ·
        refine ⟨11245914445439604196460645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7497276296959736130973763 11245914445439604196460645)
        ·
          refine ⟨2108608958519925786836371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11245914445439604196460645 2108608958519925786836371)
          ·
            refine ⟨3162913437779888680254557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108608958519925786836371 3162913437779888680254557)
            ·
              refine ⟨1186092539167458255095459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3162913437779888680254557 1186092539167458255095459)
              ·
                refine ⟨1779138808751187382643189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186092539167458255095459 1779138808751187382643189)
                ·
                  refine ⟨166794263320423817122799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1779138808751187382643189 166794263320423817122799)
                  ·
                    rfl

theorem cell22_1461738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_1461738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461738 prefixEnd_1461738 := by exact prefixLift 1461738
  have htrace : WordTrace (prefixWord ++ tailWord_1461738) baseStart_1461738 baseEnd_1461738 := by
    simpa [prefixWord, tailWord_1461738, baseEnd_1461738] using wordTrace_append hprefix tailTrace_1461738
  have hstable : (prefixWord ++ tailWord_1461738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461738).length < 2 ^ (prefixWord ++ tailWord_1461738).sum := by decide
  have hdescent : baseEnd_1461738 < baseStart_1461738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461779 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 4, 4]
def baseStart_1461779 : Nat := 118140960795 + 1461779 * 2 ^ 59
def prefixEnd_1461779 : Nat := 4983230072969 + 3 ^ 40 * 1461779 * 2
def baseEnd_1461779 : Nat := 500396825099161011093271

theorem tailTrace_1461779 : CollatzResearch.WordTrace tailWord_1461779 prefixEnd_1461779 500396825099161011093271 := by
  unfold tailWord_1461779
  simp only [CollatzResearch.WordTrace]
  refine ⟨53315460171231809822500391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35543640114154539881666927 53315460171231809822500391)
  ·
    refine ⟨79973190256847714733750587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53315460171231809822500391 79973190256847714733750587)
    ·
      refine ⟨119959785385271572100625881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79973190256847714733750587 119959785385271572100625881)
      ·
        refine ⟨89969839038953679075469411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119959785385271572100625881 89969839038953679075469411)
        ·
          refine ⟨134954758558430518613204117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89969839038953679075469411 134954758558430518613204117)
          ·
            refine ⟨6326004307426430559993943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134954758558430518613204117 6326004307426430559993943)
            ·
              refine ⟨9489006461139645839990915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6326004307426430559993943 9489006461139645839990915)
              ·
                refine ⟨14233509691709468759986373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9489006461139645839990915 14233509691709468759986373)
                ·
                  refine ⟨2668783067195525392497445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14233509691709468759986373 2668783067195525392497445)
                  ·
                    refine ⟨500396825099161011093271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2668783067195525392497445 500396825099161011093271)
                    ·
                      rfl

theorem cell22_1461779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 4].length) (baseStart_1461779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461779 prefixEnd_1461779 := by exact prefixLift 1461779
  have htrace : WordTrace (prefixWord ++ tailWord_1461779) baseStart_1461779 baseEnd_1461779 := by
    simpa [prefixWord, tailWord_1461779, baseEnd_1461779] using wordTrace_append hprefix tailTrace_1461779
  have hstable : (prefixWord ++ tailWord_1461779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461779).length < 2 ^ (prefixWord ++ tailWord_1461779).sum := by decide
  have hdescent : baseEnd_1461779 < baseStart_1461779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461781 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_1461781 : Nat := 118140960795 + 1461781 * 2 ^ 59
def prefixEnd_1461781 : Nat := 4983230072969 + 3 ^ 40 * 1461781 * 2
def baseEnd_1461781 : Nat := 500397509740033672543265

theorem tailTrace_1461781 : CollatzResearch.WordTrace tailWord_1461781 prefixEnd_1461781 500397509740033672543265 := by
  unfold tailWord_1461781
  simp only [CollatzResearch.WordTrace]
  refine ⟨53315533117224564164073197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35543688744816376109382131 53315533117224564164073197)
  ·
    refine ⟨19993324918959211561527449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53315533117224564164073197 19993324918959211561527449)
    ·
      refine ⟨14994993689219408671145587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19993324918959211561527449 14994993689219408671145587)
      ·
        refine ⟨22492490533829113006718381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14994993689219408671145587 22492490533829113006718381)
        ·
          refine ⟨8434683950185917377519393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22492490533829113006718381 8434683950185917377519393)
          ·
            refine ⟨6326012962639438033139545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8434683950185917377519393 6326012962639438033139545)
            ·
              refine ⟨4744509721979578524854659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6326012962639438033139545 4744509721979578524854659)
              ·
                refine ⟨7116764582969367787281989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4744509721979578524854659 7116764582969367787281989)
                ·
                  refine ⟨1334393359306756460115373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7116764582969367787281989 1334393359306756460115373)
                  ·
                    refine ⟨500397509740033672543265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334393359306756460115373 500397509740033672543265)
                    ·
                      rfl

theorem cell22_1461781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_1461781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461781 prefixEnd_1461781 := by exact prefixLift 1461781
  have htrace : WordTrace (prefixWord ++ tailWord_1461781) baseStart_1461781 baseEnd_1461781 := by
    simpa [prefixWord, tailWord_1461781, baseEnd_1461781] using wordTrace_append hprefix tailTrace_1461781
  have hstable : (prefixWord ++ tailWord_1461781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461781).length < 2 ^ (prefixWord ++ tailWord_1461781).sum := by decide
  have hdescent : baseEnd_1461781 < baseStart_1461781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461794 : List Nat := [3, 3, 1, 1, 1, 1, 3, 9]
def baseStart_1461794 : Nat := 118140960795 + 1461794 * 2 ^ 59
def prefixEnd_1461794 : Nat := 4983230072969 + 3 ^ 40 * 1461794 * 2
def baseEnd_1461794 : Nat := 55600217767300663552025

theorem tailTrace_1461794 : CollatzResearch.WordTrace tailWord_1461794 prefixEnd_1461794 55600217767300663552025 := by
  unfold tailWord_1461794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13329001816544366846074109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35544004844118311589530957 13329001816544366846074109)
  ·
    refine ⟨4998375681204137567277791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13329001816544366846074109 4998375681204137567277791)
    ·
      refine ⟨7497563521806206350916687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4998375681204137567277791 7497563521806206350916687)
      ·
        refine ⟨11246345282709309526375031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7497563521806206350916687 11246345282709309526375031)
        ·
          refine ⟨16869517924063964289562547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11246345282709309526375031 16869517924063964289562547)
          ·
            refine ⟨25304276886095946434343821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16869517924063964289562547 25304276886095946434343821)
            ·
              refine ⟨9489103832285979912878933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25304276886095946434343821 9489103832285979912878933)
              ·
                refine ⟨55600217767300663552025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9489103832285979912878933 55600217767300663552025)
                ·
                  rfl

theorem cell22_1461794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_1461794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461794 prefixEnd_1461794 := by exact prefixLift 1461794
  have htrace : WordTrace (prefixWord ++ tailWord_1461794) baseStart_1461794 baseEnd_1461794 := by
    simpa [prefixWord, tailWord_1461794, baseEnd_1461794] using wordTrace_append hprefix tailTrace_1461794
  have hstable : (prefixWord ++ tailWord_1461794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461794).length < 2 ^ (prefixWord ++ tailWord_1461794).sum := by decide
  have hdescent : baseEnd_1461794 < baseStart_1461794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461877 : List Nat := [1, 3, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1461877 : Nat := 118140960795 + 1461877 * 2 ^ 59
def prefixEnd_1461877 : Nat := 4983230072969 + 3 ^ 40 * 1461877 * 2
def baseEnd_1461877 : Nat := 500430372501921422142971

theorem tailTrace_1461877 : CollatzResearch.WordTrace tailWord_1461877 prefixEnd_1461877 500430372501921422142971 := by
  unfold tailWord_1461877
  simp only [CollatzResearch.WordTrace]
  refine ⟨53319034524876772559567885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35546023016584515039711923 53319034524876772559567885)
  ·
    refine ⟨19994637946828789709837957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53319034524876772559567885 19994637946828789709837957)
    ·
      refine ⟨3748994615030398070594617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19994637946828789709837957 3748994615030398070594617)
      ·
        refine ⟨2811745961272798552945963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3748994615030398070594617 2811745961272798552945963)
        ·
          refine ⟨4217618941909197829418945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2811745961272798552945963 4217618941909197829418945)
          ·
            refine ⟨3163214206431898372064209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4217618941909197829418945 3163214206431898372064209)
            ·
              refine ⟨2372410654823923779048157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163214206431898372064209 2372410654823923779048157)
              ·
                refine ⟨889653995558971417143059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2372410654823923779048157 889653995558971417143059)
                ·
                  refine ⟨1334480993338457125714589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889653995558971417143059 1334480993338457125714589)
                  ·
                    refine ⟨500430372501921422142971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334480993338457125714589 500430372501921422142971)
                    ·
                      rfl

theorem cell22_1461877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1461877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461877 prefixEnd_1461877 := by exact prefixLift 1461877
  have htrace : WordTrace (prefixWord ++ tailWord_1461877) baseStart_1461877 baseEnd_1461877 := by
    simpa [prefixWord, tailWord_1461877, baseEnd_1461877] using wordTrace_append hprefix tailTrace_1461877
  have hstable : (prefixWord ++ tailWord_1461877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461877).length < 2 ^ (prefixWord ++ tailWord_1461877).sum := by decide
  have hdescent : baseEnd_1461877 < baseStart_1461877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461884 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 10]
def baseStart_1461884 : Nat := 118140960795 + 1461884 * 2 ^ 59
def prefixEnd_1461884 : Nat := 4983230072969 + 3 ^ 40 * 1461884 * 2
def baseEnd_1461884 : Nat := 166810922914991912405983

theorem tailTrace_1461884 : CollatzResearch.WordTrace tailWord_1461884 prefixEnd_1461884 166810922914991912405983 := by
  unfold tailWord_1461884
  simp only [CollatzResearch.WordTrace]
  refine ⟨26659644917925706377536353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35546193223900941836715137 26659644917925706377536353)
  ·
    refine ⟨19994733688444279783152265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26659644917925706377536353 19994733688444279783152265)
    ·
      refine ⟨14996050266333209837364199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19994733688444279783152265 14996050266333209837364199)
      ·
        refine ⟨22494075399499814756046299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14996050266333209837364199 22494075399499814756046299)
        ·
          refine ⟨33741113099249722134069449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22494075399499814756046299 33741113099249722134069449)
          ·
            refine ⟨25305834824437291600552087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33741113099249722134069449 25305834824437291600552087)
            ·
              refine ⟨37958752236655937400828131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25305834824437291600552087 37958752236655937400828131)
              ·
                refine ⟨56938128354983906101242197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37958752236655937400828131 56938128354983906101242197)
                ·
                  refine ⟨166810922914991912405983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56938128354983906101242197 166810922914991912405983)
                  ·
                    rfl

theorem cell22_1461884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_1461884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461884 prefixEnd_1461884 := by exact prefixLift 1461884
  have htrace : WordTrace (prefixWord ++ tailWord_1461884) baseStart_1461884 baseEnd_1461884 := by
    simpa [prefixWord, tailWord_1461884, baseEnd_1461884] using wordTrace_append hprefix tailTrace_1461884
  have hstable : (prefixWord ++ tailWord_1461884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461884).length < 2 ^ (prefixWord ++ tailWord_1461884).sum := by decide
  have hdescent : baseEnd_1461884 < baseStart_1461884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461918 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_1461918 : Nat := 118140960795 + 1461918 * 2 ^ 59
def prefixEnd_1461918 : Nat := 4983230072969 + 3 ^ 40 * 1461918 * 2
def baseEnd_1461918 : Nat := 166814802546603660622615

theorem tailTrace_1461918 : CollatzResearch.WordTrace tailWord_1461918 prefixEnd_1461918 166814802546603660622615 := by
  unfold tailWord_1461918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6665066239716029570226301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35547019945152157707873605 6665066239716029570226301)
  ·
    refine ⟨2499399839893511088834863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6665066239716029570226301 2499399839893511088834863)
    ·
      refine ⟨3749099759840266633252295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2499399839893511088834863 3749099759840266633252295)
      ·
        refine ⟨5623649639760399949878443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749099759840266633252295 5623649639760399949878443)
        ·
          refine ⟨8435474459640599924817665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623649639760399949878443 8435474459640599924817665)
          ·
            refine ⟨6326605844730449943613249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8435474459640599924817665 6326605844730449943613249)
            ·
              refine ⟨4744954383547837457709937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6326605844730449943613249 4744954383547837457709937)
              ·
                refine ⟨3558715787660878093282453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4744954383547837457709937 3558715787660878093282453)
                ·
                  refine ⟨166814802546603660622615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3558715787660878093282453 166814802546603660622615)
                  ·
                    rfl

theorem cell22_1461918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_1461918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461918 prefixEnd_1461918 := by exact prefixLift 1461918
  have htrace : WordTrace (prefixWord ++ tailWord_1461918) baseStart_1461918 baseEnd_1461918 := by
    simpa [prefixWord, tailWord_1461918, baseEnd_1461918] using wordTrace_append hprefix tailTrace_1461918
  have hstable : (prefixWord ++ tailWord_1461918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461918).length < 2 ^ (prefixWord ++ tailWord_1461918).sum := by decide
  have hdescent : baseEnd_1461918 < baseStart_1461918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461928 : List Nat := [2, 1, 7, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1461928 : Nat := 118140960795 + 1461928 * 2 ^ 59
def prefixEnd_1461928 : Nat := 4983230072969 + 3 ^ 40 * 1461928 * 2
def baseEnd_1461928 : Nat := 500447830844174289117815

theorem tailTrace_1461928 : CollatzResearch.WordTrace tailWord_1461928 prefixEnd_1461928 500447830844174289117815 := by
  unfold tailWord_1461928
  simp only [CollatzResearch.WordTrace]
  refine ⟨26660447323846004134837219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35547263098461338846449625 26660447323846004134837219)
  ·
    refine ⟨39990670985769006202255829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26660447323846004134837219 39990670985769006202255829)
    ·
      refine ⟨937281351228961082865371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39990670985769006202255829 937281351228961082865371)
      ·
        refine ⟨1405922026843441624298057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937281351228961082865371 1405922026843441624298057)
        ·
          refine ⟨1054441520132581218223543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1405922026843441624298057 1054441520132581218223543)
          ·
            refine ⟨1581662280198871827335315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054441520132581218223543 1581662280198871827335315)
            ·
              refine ⟨2372493420298307741002973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581662280198871827335315 2372493420298307741002973)
              ·
                refine ⟨889685032611865402876115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2372493420298307741002973 889685032611865402876115)
                ·
                  refine ⟨1334527548917798104314173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889685032611865402876115 1334527548917798104314173)
                  ·
                    refine ⟨500447830844174289117815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334527548917798104314173 500447830844174289117815)
                    ·
                      rfl

theorem cell22_1461928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1461928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461928 prefixEnd_1461928 := by exact prefixLift 1461928
  have htrace : WordTrace (prefixWord ++ tailWord_1461928) baseStart_1461928 baseEnd_1461928 := by
    simpa [prefixWord, tailWord_1461928, baseEnd_1461928] using wordTrace_append hprefix tailTrace_1461928
  have hstable : (prefixWord ++ tailWord_1461928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461928).length < 2 ^ (prefixWord ++ tailWord_1461928).sum := by decide
  have hdescent : baseEnd_1461928 < baseStart_1461928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461933 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1461933 : Nat := 118140960795 + 1461933 * 2 ^ 59
def prefixEnd_1461933 : Nat := 4983230072969 + 3 ^ 40 * 1461933 * 2
def baseEnd_1461933 : Nat := 500449542446355942742799

theorem tailTrace_1461933 : CollatzResearch.WordTrace tailWord_1461933 prefixEnd_1461933 500449542446355942742799 := by
  unfold tailWord_1461933
  simp only [CollatzResearch.WordTrace]
  refine ⟨53321077012673894123606453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35547384675115929415737635 53321077012673894123606453)
  ·
    refine ⟨4998850969938177574088105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53321077012673894123606453 4998850969938177574088105)
    ·
      refine ⟨3749138227453633180566079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4998850969938177574088105 3749138227453633180566079)
      ·
        refine ⟨5623707341180449770849119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749138227453633180566079 5623707341180449770849119)
        ·
          refine ⟨8435561011770674656273679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623707341180449770849119 8435561011770674656273679)
          ·
            refine ⟨12653341517656011984410519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8435561011770674656273679 12653341517656011984410519)
            ·
              refine ⟨18980012276484017976615779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12653341517656011984410519 18980012276484017976615779)
              ·
                refine ⟨28470018414726026964923669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18980012276484017976615779 28470018414726026964923669)
                ·
                  refine ⟨1334532113190282513980797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28470018414726026964923669 1334532113190282513980797)
                  ·
                    refine ⟨500449542446355942742799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334532113190282513980797 500449542446355942742799)
                    ·
                      rfl

theorem cell22_1461933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1461933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461933 prefixEnd_1461933 := by exact prefixLift 1461933
  have htrace : WordTrace (prefixWord ++ tailWord_1461933) baseStart_1461933 baseEnd_1461933 := by
    simpa [prefixWord, tailWord_1461933, baseEnd_1461933] using wordTrace_append hprefix tailTrace_1461933
  have hstable : (prefixWord ++ tailWord_1461933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461933).length < 2 ^ (prefixWord ++ tailWord_1461933).sum := by decide
  have hdescent : baseEnd_1461933 < baseStart_1461933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461946 : List Nat := [3, 1, 1, 1, 2, 6, 8]
def baseStart_1461946 : Nat := 118140960795 + 1461946 * 2 ^ 59
def prefixEnd_1461946 : Nat := 4983230072969 + 3 ^ 40 * 1461946 * 2
def baseEnd_1461946 : Nat := 18535333059704749709917

theorem tailTrace_1461946 : CollatzResearch.WordTrace tailWord_1461946 prefixEnd_1461946 18535333059704749709917 := by
  unfold tailWord_1461946
  simp only [CollatzResearch.WordTrace]
  refine ⟨13330387790406699335957423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35547700774417864895886461 13330387790406699335957423)
  ·
    refine ⟨19995581685610049003936135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13330387790406699335957423 19995581685610049003936135)
    ·
      refine ⟨29993372528415073505904203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19995581685610049003936135 29993372528415073505904203)
      ·
        refine ⟨44990058792622610258856305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29993372528415073505904203 44990058792622610258856305)
        ·
          refine ⟨33742544094466957694142229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44990058792622610258856305 33742544094466957694142229)
          ·
            refine ⟨1581681754428138641912917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33742544094466957694142229 1581681754428138641912917)
            ·
              refine ⟨18535333059704749709917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1581681754428138641912917 18535333059704749709917)
              ·
                rfl

theorem cell22_1461946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 8].length) (baseStart_1461946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461946 prefixEnd_1461946 := by exact prefixLift 1461946
  have htrace : WordTrace (prefixWord ++ tailWord_1461946) baseStart_1461946 baseEnd_1461946 := by
    simpa [prefixWord, tailWord_1461946, baseEnd_1461946] using wordTrace_append hprefix tailTrace_1461946
  have hstable : (prefixWord ++ tailWord_1461946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461946).length < 2 ^ (prefixWord ++ tailWord_1461946).sum := by decide
  have hdescent : baseEnd_1461946 < baseStart_1461946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461948 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1461948 : Nat := 118140960795 + 1461948 * 2 ^ 59
def prefixEnd_1461948 : Nat := 4983230072969 + 3 ^ 40 * 1461948 * 2
def baseEnd_1461948 : Nat := 500454677252900903617753

theorem tailTrace_1461948 : CollatzResearch.WordTrace tailWord_1461948 prefixEnd_1461948 500454677252900903617753 := by
  unfold tailWord_1461948
  simp only [CollatzResearch.WordTrace]
  refine ⟨26660812053809775842701249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35547749405079701123601665 26660812053809775842701249)
  ·
    refine ⟨19995609040357331882025937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26660812053809775842701249 19995609040357331882025937)
    ·
      refine ⟨14996706780267998911519453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19995609040357331882025937 14996706780267998911519453)
      ·
        refine ⟨5623765042600499591819795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14996706780267998911519453 5623765042600499591819795)
        ·
          refine ⟨8435647563900749387729693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623765042600499591819795 8435647563900749387729693)
          ·
            refine ⟨3163367836462781020398635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8435647563900749387729693 3163367836462781020398635)
            ·
              refine ⟨4745051754694171530597953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163367836462781020398635 4745051754694171530597953)
              ·
                refine ⟨3558788816020628647948465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745051754694171530597953 3558788816020628647948465)
                ·
                  refine ⟨2669091612015471485961349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3558788816020628647948465 2669091612015471485961349)
                  ·
                    refine ⟨500454677252900903617753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2669091612015471485961349 500454677252900903617753)
                    ·
                      rfl

theorem cell22_1461948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1461948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1461948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1461948 prefixEnd_1461948 := by exact prefixLift 1461948
  have htrace : WordTrace (prefixWord ++ tailWord_1461948) baseStart_1461948 baseEnd_1461948 := by
    simpa [prefixWord, tailWord_1461948, baseEnd_1461948] using wordTrace_append hprefix tailTrace_1461948
  have hstable : (prefixWord ++ tailWord_1461948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461948).length < 2 ^ (prefixWord ++ tailWord_1461948).sum := by decide
  have hdescent : baseEnd_1461948 < baseStart_1461948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462070 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1462070 : Nat := 118140960795 + 1462070 * 2 ^ 59
def prefixEnd_1462070 : Nat := 4983230072969 + 3 ^ 40 * 1462070 * 2
def baseEnd_1462070 : Nat := 166832146782044417355793

theorem tailTrace_1462070 : CollatzResearch.WordTrace tailWord_1462070 prefixEnd_1462070 166832146782044417355793 := by
  unfold tailWord_1462070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332879613323597907583979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35550715875451711014229109 3332879613323597907583979)
  ·
    refine ⟨4999319419985396861375969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3332879613323597907583979 4999319419985396861375969)
    ·
      refine ⟨3749489564989047646031977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4999319419985396861375969 3749489564989047646031977)
      ·
        refine ⟨2812117173741785734523983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3749489564989047646031977 2812117173741785734523983)
        ·
          refine ⟨4218175760612678601785975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2812117173741785734523983 4218175760612678601785975)
          ·
            refine ⟨6327263640919017902678963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4218175760612678601785975 6327263640919017902678963)
            ·
              refine ⟨9490895461378526854018445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6327263640919017902678963 9490895461378526854018445)
              ·
                refine ⟨3559085798016947570256917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9490895461378526854018445 3559085798016947570256917)
                ·
                  refine ⟨166832146782044417355793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3559085798016947570256917 166832146782044417355793)
                  ·
                    rfl

theorem cell22_1462070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1462070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462070 prefixEnd_1462070 := by exact prefixLift 1462070
  have htrace : WordTrace (prefixWord ++ tailWord_1462070) baseStart_1462070 baseEnd_1462070 := by
    simpa [prefixWord, tailWord_1462070, baseEnd_1462070] using wordTrace_append hprefix tailTrace_1462070
  have hstable : (prefixWord ++ tailWord_1462070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462070).length < 2 ^ (prefixWord ++ tailWord_1462070).sum := by decide
  have hdescent : baseEnd_1462070 < baseStart_1462070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462096 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_1462096 : Nat := 118140960795 + 1462096 * 2 ^ 59
def prefixEnd_1462096 : Nat := 4983230072969 + 3 ^ 40 * 1462096 * 2
def baseEnd_1462096 : Nat := 500505340677477850917299

theorem tailTrace_1462096 : CollatzResearch.WordTrace tailWord_1462096 prefixEnd_1462096 500505340677477850917299 := by
  unfold tailWord_1462096
  simp only [CollatzResearch.WordTrace]
  refine ⟨26663511055541686480895071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35551348074055581974526761 26663511055541686480895071)
  ·
    refine ⟨39995266583312529721342607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26663511055541686480895071 39995266583312529721342607)
    ·
      refine ⟨59992899874968794582013911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39995266583312529721342607 59992899874968794582013911)
      ·
        refine ⟨89989349812453191873020867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59992899874968794582013911 89989349812453191873020867)
        ·
          refine ⟨134984024718679787809531301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89989349812453191873020867 134984024718679787809531301)
          ·
            refine ⟨25309504634752460214287119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134984024718679787809531301 25309504634752460214287119)
            ·
              refine ⟨37964256952128690321430679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25309504634752460214287119 37964256952128690321430679)
              ·
                refine ⟨56946385428193035482146019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37964256952128690321430679 56946385428193035482146019)
                ·
                  refine ⟨85419578142289553223219029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56946385428193035482146019 85419578142289553223219029)
                  ·
                    refine ⟨500505340677477850917299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 85419578142289553223219029 500505340677477850917299)
                    ·
                      rfl

theorem cell22_1462096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_1462096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462096 prefixEnd_1462096 := by exact prefixLift 1462096
  have htrace : WordTrace (prefixWord ++ tailWord_1462096) baseStart_1462096 baseEnd_1462096 := by
    simpa [prefixWord, tailWord_1462096, baseEnd_1462096] using wordTrace_append hprefix tailTrace_1462096
  have hstable : (prefixWord ++ tailWord_1462096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462096).length < 2 ^ (prefixWord ++ tailWord_1462096).sum := by decide
  have hdescent : baseEnd_1462096 < baseStart_1462096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462098 : List Nat := [3, 2, 2, 1, 1, 4, 1, 8]
def baseStart_1462098 : Nat := 118140960795 + 1462098 * 2 ^ 59
def prefixEnd_1462098 : Nat := 4983230072969 + 3 ^ 40 * 1462098 * 2
def baseEnd_1462098 : Nat := 55611780590927834707477

theorem tailTrace_1462098 : CollatzResearch.WordTrace tailWord_1462098 prefixEnd_1462098 55611780590927834707477 := by
  unfold tailWord_1462098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331773764269031825840737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35551396704717418202241965 13331773764269031825840737)
  ·
    refine ⟨9998830323201773869380553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13331773764269031825840737 9998830323201773869380553)
    ·
      refine ⟨7499122742401330402035415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9998830323201773869380553 7499122742401330402035415)
      ·
        refine ⟨11248684113601995603053123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7499122742401330402035415 11248684113601995603053123)
        ·
          refine ⟨16873026170402993404579685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11248684113601995603053123 16873026170402993404579685)
          ·
            refine ⟨3163692406950561263358691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16873026170402993404579685 3163692406950561263358691)
            ·
              refine ⟨4745538610425841895038037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163692406950561263358691 4745538610425841895038037)
              ·
                refine ⟨55611780590927834707477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4745538610425841895038037 55611780590927834707477)
                ·
                  rfl

theorem cell22_1462098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_1462098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462098 prefixEnd_1462098 := by exact prefixLift 1462098
  have htrace : WordTrace (prefixWord ++ tailWord_1462098) baseStart_1462098 baseEnd_1462098 := by
    simpa [prefixWord, tailWord_1462098, baseEnd_1462098] using wordTrace_append hprefix tailTrace_1462098
  have hstable : (prefixWord ++ tailWord_1462098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462098).length < 2 ^ (prefixWord ++ tailWord_1462098).sum := by decide
  have hdescent : baseEnd_1462098 < baseStart_1462098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462115 : List Nat := [1, 1, 1, 5, 5, 1, 8]
def baseStart_1462115 : Nat := 118140960795 + 1462115 * 2 ^ 59
def prefixEnd_1462115 : Nat := 4983230072969 + 3 ^ 40 * 1462115 * 2
def baseEnd_1462115 : Nat := 18537475732065486470083

theorem tailTrace_1462115 : CollatzResearch.WordTrace tailWord_1462115 prefixEnd_1462115 18537475732065486470083 := by
  unfold tailWord_1462115
  simp only [CollatzResearch.WordTrace]
  refine ⟨53327715098014539206731799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35551810065343026137821199 53327715098014539206731799)
  ·
    refine ⟨79991572647021808810097699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53327715098014539206731799 79991572647021808810097699)
    ·
      refine ⟨119987358970532713215146549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79991572647021808810097699 119987358970532713215146549)
      ·
        refine ⟨11248814903487441863919989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119987358970532713215146549 11248814903487441863919989)
        ·
          refine ⟨1054576397201947674742499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11248814903487441863919989 1054576397201947674742499)
          ·
            refine ⟨1581864595802921512113749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054576397201947674742499 1581864595802921512113749)
            ·
              refine ⟨18537475732065486470083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1581864595802921512113749 18537475732065486470083)
              ·
                rfl

theorem cell22_1462115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 8].length) (baseStart_1462115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462115 prefixEnd_1462115 := by exact prefixLift 1462115
  have htrace : WordTrace (prefixWord ++ tailWord_1462115) baseStart_1462115 baseEnd_1462115 := by
    simpa [prefixWord, tailWord_1462115, baseEnd_1462115] using wordTrace_append hprefix tailTrace_1462115
  have hstable : (prefixWord ++ tailWord_1462115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462115).length < 2 ^ (prefixWord ++ tailWord_1462115).sum := by decide
  have hdescent : baseEnd_1462115 < baseStart_1462115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462177 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 5]
def baseStart_1462177 : Nat := 118140960795 + 1462177 * 2 ^ 59
def prefixEnd_1462177 : Nat := 4983230072969 + 3 ^ 40 * 1462177 * 2
def baseEnd_1462177 : Nat := 166844356210940213214017

theorem tailTrace_1462177 : CollatzResearch.WordTrace tailWord_1462177 prefixEnd_1462177 166844356210940213214017 := by
  unfold tailWord_1462177
  simp only [CollatzResearch.WordTrace]
  refine ⟨53329976423789923795488785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35553317615859949196992523 53329976423789923795488785)
  ·
    refine ⟨39997482317842442846616589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53329976423789923795488785 39997482317842442846616589)
    ·
      refine ⟨14999055869190916067481221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39997482317842442846616589 14999055869190916067481221)
      ·
        refine ⟨2812322975473296762652729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14999055869190916067481221 2812322975473296762652729)
        ·
          refine ⟨2109242231604972571989547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2812322975473296762652729 2109242231604972571989547)
          ·
            refine ⟨3163863347407458857984321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109242231604972571989547 3163863347407458857984321)
            ·
              refine ⟨2372897510555594143488241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3163863347407458857984321 2372897510555594143488241)
              ·
                refine ⟨1779673132916695607616181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2372897510555594143488241 1779673132916695607616181)
                ·
                  refine ⟨166844356210940213214017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1779673132916695607616181 166844356210940213214017)
                  ·
                    rfl

theorem cell22_1462177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_1462177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462177 prefixEnd_1462177 := by exact prefixLift 1462177
  have htrace : WordTrace (prefixWord ++ tailWord_1462177) baseStart_1462177 baseEnd_1462177 := by
    simpa [prefixWord, tailWord_1462177, baseEnd_1462177] using wordTrace_append hprefix tailTrace_1462177
  have hstable : (prefixWord ++ tailWord_1462177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462177).length < 2 ^ (prefixWord ++ tailWord_1462177).sum := by decide
  have hdescent : baseEnd_1462177 < baseStart_1462177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462203 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 1, 5]
def baseStart_1462203 : Nat := 118140960795 + 1462203 * 2 ^ 59
def prefixEnd_1462203 : Nat := 4983230072969 + 3 ^ 40 * 1462203 * 2
def baseEnd_1462203 : Nat := 500541968964165238491971

theorem tailTrace_1462203 : CollatzResearch.WordTrace tailWord_1462203 prefixEnd_1462203 500541968964165238491971 := by
  unfold tailWord_1462203
  simp only [CollatzResearch.WordTrace]
  refine ⟨53330924721695730235935263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35553949814463820157290175 53330924721695730235935263)
  ·
    refine ⟨79996387082543595353902895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53330924721695730235935263 79996387082543595353902895)
    ·
      refine ⟨119994580623815393030854343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79996387082543595353902895 119994580623815393030854343)
      ·
        refine ⟨179991870935723089546281515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119994580623815393030854343 179991870935723089546281515)
        ·
          refine ⟨269987806403584634319422273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179991870935723089546281515 269987806403584634319422273)
          ·
            refine ⟨202490854802688475739566705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269987806403584634319422273 202490854802688475739566705)
            ·
              refine ⟨151868141102016356804675029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202490854802688475739566705 151868141102016356804675029)
              ·
                refine ⟨3559409557078508362609571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151868141102016356804675029 3559409557078508362609571)
                ·
                  refine ⟨5339114335617762543914357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559409557078508362609571 5339114335617762543914357)
                  ·
                    refine ⟨500541968964165238491971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5339114335617762543914357 500541968964165238491971)
                    ·
                      rfl

theorem cell22_1462203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_1462203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462203 prefixEnd_1462203 := by exact prefixLift 1462203
  have htrace : WordTrace (prefixWord ++ tailWord_1462203) baseStart_1462203 baseEnd_1462203 := by
    simpa [prefixWord, tailWord_1462203, baseEnd_1462203] using wordTrace_append hprefix tailTrace_1462203
  have hstable : (prefixWord ++ tailWord_1462203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462203).length < 2 ^ (prefixWord ++ tailWord_1462203).sum := by decide
  have hdescent : baseEnd_1462203 < baseStart_1462203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462205 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 6]
def baseStart_1462205 : Nat := 118140960795 + 1462205 * 2 ^ 59
def prefixEnd_1462205 : Nat := 4983230072969 + 3 ^ 40 * 1462205 * 2
def baseEnd_1462205 : Nat := 166847551201679299980655

theorem tailTrace_1462205 : CollatzResearch.WordTrace tailWord_1462205 prefixEnd_1462205 166847551201679299980655 := by
  unfold tailWord_1462205
  simp only [CollatzResearch.WordTrace]
  refine ⟨53330997667688484577508069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35553998445125656385005379 53330997667688484577508069)
  ·
    refine ⟨9999562062691590858282763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53330997667688484577508069 9999562062691590858282763)
    ·
      refine ⟨14999343094037386287424145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9999562062691590858282763 14999343094037386287424145)
      ·
        refine ⟨11249507320528039715568109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14999343094037386287424145 11249507320528039715568109)
        ·
          refine ⟨4218565245198014893338041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11249507320528039715568109 4218565245198014893338041)
          ·
            refine ⟨3163923933898511170003531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4218565245198014893338041 3163923933898511170003531)
            ·
              refine ⟨4745885900847766755005297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3163923933898511170003531 4745885900847766755005297)
              ·
                refine ⟨3559414425635825066253973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745885900847766755005297 3559414425635825066253973)
                ·
                  refine ⟨166847551201679299980655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3559414425635825066253973 166847551201679299980655)
                  ·
                    rfl

theorem cell22_1462205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_1462205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462205 prefixEnd_1462205 := by exact prefixLift 1462205
  have htrace : WordTrace (prefixWord ++ tailWord_1462205) baseStart_1462205 baseEnd_1462205 := by
    simpa [prefixWord, tailWord_1462205, baseEnd_1462205] using wordTrace_append hprefix tailTrace_1462205
  have hstable : (prefixWord ++ tailWord_1462205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462205).length < 2 ^ (prefixWord ++ tailWord_1462205).sum := by decide
  have hdescent : baseEnd_1462205 < baseStart_1462205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462220 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_1462220 : Nat := 118140960795 + 1462220 * 2 ^ 59
def prefixEnd_1462220 : Nat := 4983230072969 + 3 ^ 40 * 1462220 * 2
def baseEnd_1462220 : Nat := 500547788411582860816919

theorem tailTrace_1462220 : CollatzResearch.WordTrace tailWord_1462220 prefixEnd_1462220 500547788411582860816919 := by
  unfold tailWord_1462220
  simp only [CollatzResearch.WordTrace]
  refine ⟨26665772381317071069652057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35554363175089428092869409 26665772381317071069652057)
  ·
    refine ⟨19999329285987803302239043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26665772381317071069652057 19999329285987803302239043)
    ·
      refine ⟨29998993928981704953358565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19999329285987803302239043 29998993928981704953358565)
      ·
        refine ⟨5624811361684069678754731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29998993928981704953358565 5624811361684069678754731)
        ·
          refine ⟨8437217042526104518132097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624811361684069678754731 8437217042526104518132097)
          ·
            refine ⟨6327912781894578388599073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8437217042526104518132097 6327912781894578388599073)
            ·
              refine ⟨4745934586420933791449305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6327912781894578388599073 4745934586420933791449305)
              ·
                refine ⟨3559450939815700343586979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745934586420933791449305 3559450939815700343586979)
                ·
                  refine ⟨5339176409723550515380469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3559450939815700343586979 5339176409723550515380469)
                  ·
                    refine ⟨500547788411582860816919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5339176409723550515380469 500547788411582860816919)
                    ·
                      rfl

theorem cell22_1462220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_1462220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462220 prefixEnd_1462220 := by exact prefixLift 1462220
  have htrace : WordTrace (prefixWord ++ tailWord_1462220) baseStart_1462220 baseEnd_1462220 := by
    simpa [prefixWord, tailWord_1462220, baseEnd_1462220] using wordTrace_append hprefix tailTrace_1462220
  have hstable : (prefixWord ++ tailWord_1462220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462220).length < 2 ^ (prefixWord ++ tailWord_1462220).sum := by decide
  have hdescent : baseEnd_1462220 < baseStart_1462220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462222 : List Nat := [4, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_1462222 : Nat := 118140960795 + 1462222 * 2 ^ 59
def prefixEnd_1462222 : Nat := 4983230072969 + 3 ^ 40 * 1462222 * 2
def baseEnd_1462222 : Nat := 166849491017485174088971

theorem tailTrace_1462222 : CollatzResearch.WordTrace tailWord_1462222 prefixEnd_1462222 166849491017485174088971 := by
  unfold tailWord_1462222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6666452213578362060109615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35554411805751264320584613 6666452213578362060109615)
  ·
    refine ⟨9999678320367543090164423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6666452213578362060109615 9999678320367543090164423)
    ·
      refine ⟨14999517480551314635246635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9999678320367543090164423 14999517480551314635246635)
      ·
        refine ⟨22499276220826971952869953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14999517480551314635246635 22499276220826971952869953)
        ·
          refine ⟨16874457165620228964652465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22499276220826971952869953 16874457165620228964652465)
          ·
            refine ⟨12655842874215171723489349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16874457165620228964652465 12655842874215171723489349)
            ·
              refine ⟨2372970538915344698154253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12655842874215171723489349 2372970538915344698154253)
              ·
                refine ⟨889863952093254261807845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2372970538915344698154253 889863952093254261807845)
                ·
                  refine ⟨166849491017485174088971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889863952093254261807845 166849491017485174088971)
                  ·
                    rfl

theorem cell22_1462222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_1462222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462222 prefixEnd_1462222 := by exact prefixLift 1462222
  have htrace : WordTrace (prefixWord ++ tailWord_1462222) baseStart_1462222 baseEnd_1462222 := by
    simpa [prefixWord, tailWord_1462222, baseEnd_1462222] using wordTrace_append hprefix tailTrace_1462222
  have hstable : (prefixWord ++ tailWord_1462222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462222).length < 2 ^ (prefixWord ++ tailWord_1462222).sum := by decide
  have hdescent : baseEnd_1462222 < baseStart_1462222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462436 : List Nat := [2, 3, 1, 2, 5, 1, 2, 6]
def baseStart_1462436 : Nat := 118140960795 + 1462436 * 2 ^ 59
def prefixEnd_1462436 : Nat := 4983230072969 + 3 ^ 40 * 1462436 * 2
def baseEnd_1462436 : Nat := 55624636625092255268473

theorem tailTrace_1462436 : CollatzResearch.WordTrace tailWord_1462436 prefixEnd_1462436 55624636625092255268473 := by
  unfold tailWord_1462436
  simp only [CollatzResearch.WordTrace]
  refine ⟨26669711464925805514583581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35559615286567740686111441 26669711464925805514583581)
  ·
    refine ⟨10001141799347177067968843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26669711464925805514583581 10001141799347177067968843)
    ·
      refine ⟨15001712699020765601953265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10001141799347177067968843 15001712699020765601953265)
      ·
        refine ⟨11251284524265574201464949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15001712699020765601953265 11251284524265574201464949)
        ·
          refine ⟨1054807924149897581387339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11251284524265574201464949 1054807924149897581387339)
          ·
            refine ⟨1582211886224846372081009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054807924149897581387339 1582211886224846372081009)
            ·
              refine ⟨1186658914668634779060757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582211886224846372081009 1186658914668634779060757)
              ·
                refine ⟨55624636625092255268473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1186658914668634779060757 55624636625092255268473)
                ·
                  rfl

theorem cell22_1462436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 6].length) (baseStart_1462436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462436 prefixEnd_1462436 := by exact prefixLift 1462436
  have htrace : WordTrace (prefixWord ++ tailWord_1462436) baseStart_1462436 baseEnd_1462436 := by
    simpa [prefixWord, tailWord_1462436, baseEnd_1462436] using wordTrace_append hprefix tailTrace_1462436
  have hstable : (prefixWord ++ tailWord_1462436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462436).length < 2 ^ (prefixWord ++ tailWord_1462436).sum := by decide
  have hdescent : baseEnd_1462436 < baseStart_1462436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462507 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 1, 5]
def baseStart_1462507 : Nat := 118140960795 + 1462507 * 2 ^ 59
def prefixEnd_1462507 : Nat := 4983230072969 + 3 ^ 40 * 1462507 * 2
def baseEnd_1462507 : Nat := 500646034376809778891039

theorem tailTrace_1462507 : CollatzResearch.WordTrace tailWord_1462507 prefixEnd_1462507 500646034376809778891039 := by
  unfold tailWord_1462507
  simp only [CollatzResearch.WordTrace]
  refine ⟨53342012512594390155001775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35561341675062926770001183 53342012512594390155001775)
  ·
    refine ⟨80013018768891585232502663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53342012512594390155001775 80013018768891585232502663)
    ·
      refine ⟨120019528153337377848753995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80013018768891585232502663 120019528153337377848753995)
      ·
        refine ⟨180029292230006066773130993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120019528153337377848753995 180029292230006066773130993)
        ·
          refine ⟨135021969172504550079848245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180029292230006066773130993 135021969172504550079848245)
          ·
            refine ⟨12658309609922301569985773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135021969172504550079848245 12658309609922301569985773)
            ·
              refine ⟨4746866103720863088744665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12658309609922301569985773 4746866103720863088744665)
              ·
                refine ⟨3560149577790647316558499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4746866103720863088744665 3560149577790647316558499)
                ·
                  refine ⟨5340224366685970974837749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3560149577790647316558499 5340224366685970974837749)
                  ·
                    refine ⟨500646034376809778891039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5340224366685970974837749 500646034376809778891039)
                    ·
                      rfl

theorem cell22_1462507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_1462507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462507 prefixEnd_1462507 := by exact prefixLift 1462507
  have htrace : WordTrace (prefixWord ++ tailWord_1462507) baseStart_1462507 baseEnd_1462507 := by
    simpa [prefixWord, tailWord_1462507, baseEnd_1462507] using wordTrace_append hprefix tailTrace_1462507
  have hstable : (prefixWord ++ tailWord_1462507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462507).length < 2 ^ (prefixWord ++ tailWord_1462507).sum := by decide
  have hdescent : baseEnd_1462507 < baseStart_1462507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462511 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 1, 4]
def baseStart_1462511 : Nat := 118140960795 + 1462511 * 2 ^ 59
def prefixEnd_1462511 : Nat := 4983230072969 + 3 ^ 40 * 1462511 * 2
def baseEnd_1462511 : Nat := 500647403658555101791027

theorem tailTrace_1462511 : CollatzResearch.WordTrace tailWord_1462511 prefixEnd_1462511 500647403658555101791027 := by
  unfold tailWord_1462511
  simp only [CollatzResearch.WordTrace]
  refine ⟨53342158404579898838147387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35561438936386599225431591 53342158404579898838147387)
  ·
    refine ⟨80013237606869848257221081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53342158404579898838147387 80013237606869848257221081)
    ·
      refine ⟨60009928205152386192915811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80013237606869848257221081 60009928205152386192915811)
      ·
        refine ⟨90014892307728579289373717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60009928205152386192915811 90014892307728579289373717)
        ·
          refine ⟨4219448076924777154189393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90014892307728579289373717 4219448076924777154189393)
          ·
            refine ⟨3164586057693582865642045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4219448076924777154189393 3164586057693582865642045)
            ·
              refine ⟨1186719771635093574615767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3164586057693582865642045 1186719771635093574615767)
              ·
                refine ⟨1780079657452640361923651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186719771635093574615767 1780079657452640361923651)
                ·
                  refine ⟨2670119486178960542885477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780079657452640361923651 2670119486178960542885477)
                  ·
                    refine ⟨500647403658555101791027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2670119486178960542885477 500647403658555101791027)
                    ·
                      rfl

theorem cell22_1462511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 4].length) (baseStart_1462511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462511 prefixEnd_1462511 := by exact prefixLift 1462511
  have htrace : WordTrace (prefixWord ++ tailWord_1462511) baseStart_1462511 baseEnd_1462511 := by
    simpa [prefixWord, tailWord_1462511, baseEnd_1462511] using wordTrace_append hprefix tailTrace_1462511
  have hstable : (prefixWord ++ tailWord_1462511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462511).length < 2 ^ (prefixWord ++ tailWord_1462511).sum := by decide
  have hdescent : baseEnd_1462511 < baseStart_1462511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462526 : List Nat := [4, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_1462526 : Nat := 118140960795 + 1462526 * 2 ^ 59
def prefixEnd_1462526 : Nat := 4983230072969 + 3 ^ 40 * 1462526 * 2
def baseEnd_1462526 : Nat := 166884179488366687555327

theorem tailTrace_1462526 : CollatzResearch.WordTrace tailWord_1462526 prefixEnd_1462526 166884179488366687555327 := by
  unfold tailWord_1462526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667838187440694549992929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35561803666350370933295621 6667838187440694549992929)
  ·
    refine ⟨5000878640580520912494697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6667838187440694549992929 5000878640580520912494697)
    ·
      refine ⟨3750658980435390684371023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5000878640580520912494697 3750658980435390684371023)
      ·
        refine ⟨5625988470653086026556535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3750658980435390684371023 5625988470653086026556535)
        ·
          refine ⟨8438982705979629039834803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5625988470653086026556535 8438982705979629039834803)
          ·
            refine ⟨12658474058969443559752205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8438982705979629039834803 12658474058969443559752205)
            ·
              refine ⟨4746927772113541334907077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12658474058969443559752205 4746927772113541334907077)
              ·
                refine ⟨890048957271289000295077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4746927772113541334907077 890048957271289000295077)
                ·
                  refine ⟨166884179488366687555327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890048957271289000295077 166884179488366687555327)
                  ·
                    rfl

theorem cell22_1462526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_1462526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462526 prefixEnd_1462526 := by exact prefixLift 1462526
  have htrace : WordTrace (prefixWord ++ tailWord_1462526) baseStart_1462526 baseEnd_1462526 := by
    simpa [prefixWord, tailWord_1462526, baseEnd_1462526] using wordTrace_append hprefix tailTrace_1462526
  have hstable : (prefixWord ++ tailWord_1462526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462526).length < 2 ^ (prefixWord ++ tailWord_1462526).sum := by decide
  have hdescent : baseEnd_1462526 < baseStart_1462526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462537 : List Nat := [1, 2, 1, 1, 3, 4, 3, 7]
def baseStart_1462537 : Nat := 118140960795 + 1462537 * 2 ^ 59
def prefixEnd_1462537 : Nat := 4983230072969 + 3 ^ 40 * 1462537 * 2
def baseEnd_1462537 : Nat := 55628478221099966737883

theorem tailTrace_1462537 : CollatzResearch.WordTrace tailWord_1462537 prefixEnd_1462537 55628478221099966737883 := by
  unfold tailWord_1462537
  simp only [CollatzResearch.WordTrace]
  refine ⟨53343106702485705278593865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35562071134990470185729243 53343106702485705278593865)
  ·
    refine ⟨40007330026864278958945399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53343106702485705278593865 40007330026864278958945399)
    ·
      refine ⟨60010995040296418438418099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40007330026864278958945399 60010995040296418438418099)
      ·
        refine ⟨90016492560444627657627149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60010995040296418438418099 90016492560444627657627149)
        ·
          refine ⟨33756184710166735371610181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90016492560444627657627149 33756184710166735371610181)
          ·
            refine ⟨6329284633156262882176909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33756184710166735371610181 6329284633156262882176909)
            ·
              refine ⟨2373481737433598580816341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6329284633156262882176909 2373481737433598580816341)
              ·
                refine ⟨55628478221099966737883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2373481737433598580816341 55628478221099966737883)
                ·
                  rfl

theorem cell22_1462537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 7].length) (baseStart_1462537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462537 prefixEnd_1462537 := by exact prefixLift 1462537
  have htrace : WordTrace (prefixWord ++ tailWord_1462537) baseStart_1462537 baseEnd_1462537 := by
    simpa [prefixWord, tailWord_1462537, baseEnd_1462537] using wordTrace_append hprefix tailTrace_1462537
  have hstable : (prefixWord ++ tailWord_1462537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462537).length < 2 ^ (prefixWord ++ tailWord_1462537).sum := by decide
  have hdescent : baseEnd_1462537 < baseStart_1462537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462586 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_1462586 : Nat := 118140960795 + 1462586 * 2 ^ 59
def prefixEnd_1462586 : Nat := 4983230072969 + 3 ^ 40 * 1462586 * 2
def baseEnd_1462586 : Nat := 500673077691279906165797

theorem tailTrace_1462586 : CollatzResearch.WordTrace tailWord_1462586 prefixEnd_1462586 500673077691279906165797 := by
  unfold tailWord_1462586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336223469827046661781903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35563262586205457764751741 13336223469827046661781903)
  ·
    refine ⟨20004335204740569992672855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13336223469827046661781903 20004335204740569992672855)
    ·
      refine ⟨30006502807110854989009283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20004335204740569992672855 30006502807110854989009283)
      ·
        refine ⟨45009754210666282483513925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30006502807110854989009283 45009754210666282483513925)
        ·
          refine ⟨8439328914499927965658861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45009754210666282483513925 8439328914499927965658861)
          ·
            refine ⟨3164748342937472987122073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8439328914499927965658861 3164748342937472987122073)
            ·
              refine ⟨2373561257203104740341555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3164748342937472987122073 2373561257203104740341555)
              ·
                refine ⟨3560341885804657110512333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373561257203104740341555 3560341885804657110512333)
                ·
                  refine ⟨1335128207176746416442125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3560341885804657110512333 1335128207176746416442125)
                  ·
                    refine ⟨500673077691279906165797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335128207176746416442125 500673077691279906165797)
                    ·
                      rfl

theorem cell22_1462586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_1462586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462586 prefixEnd_1462586 := by exact prefixLift 1462586
  have htrace : WordTrace (prefixWord ++ tailWord_1462586) baseStart_1462586 baseEnd_1462586 := by
    simpa [prefixWord, tailWord_1462586, baseEnd_1462586] using wordTrace_append hprefix tailTrace_1462586
  have hstable : (prefixWord ++ tailWord_1462586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462586).length < 2 ^ (prefixWord ++ tailWord_1462586).sum := by decide
  have hdescent : baseEnd_1462586 < baseStart_1462586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462622 : List Nat := [4, 4, 2, 1, 2, 1, 8]
def baseStart_1462622 : Nat := 118140960795 + 1462622 * 2 ^ 59
def prefixEnd_1462622 : Nat := 4983230072969 + 3 ^ 40 * 1462622 * 2
def baseEnd_1462622 : Nat := 18543903749147696750581

theorem tailTrace_1462622 : CollatzResearch.WordTrace tailWord_1462622 prefixEnd_1462622 18543903749147696750581 := by
  unfold tailWord_1462622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668275863397220599429765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35564137938118509863625413 6668275863397220599429765)
  ·
    refine ⟨1250301724386978862393081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6668275863397220599429765 1250301724386978862393081)
    ·
      refine ⟨937726293290234146794811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1250301724386978862393081 937726293290234146794811)
      ·
        refine ⟨1406589439935351220192217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937726293290234146794811 1406589439935351220192217)
        ·
          refine ⟨1054942079951513415144163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406589439935351220192217 1054942079951513415144163)
          ·
            refine ⟨1582413119927270122716245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054942079951513415144163 1582413119927270122716245)
            ·
              refine ⟨18543903749147696750581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1582413119927270122716245 18543903749147696750581)
              ·
                rfl

theorem cell22_1462622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 8].length) (baseStart_1462622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462622 prefixEnd_1462622 := by exact prefixLift 1462622
  have htrace : WordTrace (prefixWord ++ tailWord_1462622) baseStart_1462622 baseEnd_1462622 := by
    simpa [prefixWord, tailWord_1462622, baseEnd_1462622] using wordTrace_append hprefix tailTrace_1462622
  have hstable : (prefixWord ++ tailWord_1462622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462622).length < 2 ^ (prefixWord ++ tailWord_1462622).sum := by decide
  have hdescent : baseEnd_1462622 < baseStart_1462622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462689 : List Nat := [1, 2, 3, 5, 11]
def baseStart_1462689 : Nat := 118140960795 + 1462689 * 2 ^ 59
def prefixEnd_1462689 : Nat := 4983230072969 + 3 ^ 40 * 1462689 * 2
def baseEnd_1462689 : Nat := 2060528134552353789467

theorem tailTrace_1462689 : CollatzResearch.WordTrace tailWord_1462689 prefixEnd_1462689 2060528134552353789467 := by
  unfold tailWord_1462689
  simp only [CollatzResearch.WordTrace]
  refine ⟨53348650597935035238127121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35565767065290023492084747 53348650597935035238127121)
  ·
    refine ⟨40011487948451276428595341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53348650597935035238127121 40011487948451276428595341)
    ·
      refine ⟨15004307980669228660723253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40011487948451276428595341 15004307980669228660723253)
      ·
        refine ⟨1406653873187740186942805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15004307980669228660723253 1406653873187740186942805)
        ·
          refine ⟨2060528134552353789467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1406653873187740186942805 2060528134552353789467)
          ·
            rfl

theorem cell22_1462689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 11].length) (baseStart_1462689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462689 prefixEnd_1462689 := by exact prefixLift 1462689
  have htrace : WordTrace (prefixWord ++ tailWord_1462689) baseStart_1462689 baseEnd_1462689 := by
    simpa [prefixWord, tailWord_1462689, baseEnd_1462689] using wordTrace_append hprefix tailTrace_1462689
  have hstable : (prefixWord ++ tailWord_1462689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462689).length < 2 ^ (prefixWord ++ tailWord_1462689).sum := by decide
  have hdescent : baseEnd_1462689 < baseStart_1462689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462695 : List Nat := [1, 1, 6, 1, 1, 4, 2, 2, 4]
def baseStart_1462695 : Nat := 118140960795 + 1462695 * 2 ^ 59
def prefixEnd_1462695 : Nat := 4983230072969 + 3 ^ 40 * 1462695 * 2
def baseEnd_1462695 : Nat := 166903463539613318396821

theorem tailTrace_1462695 : CollatzResearch.WordTrace tailWord_1462695 prefixEnd_1462695 166903463539613318396821 := by
  unfold tailWord_1462695
  simp only [CollatzResearch.WordTrace]
  refine ⟨53348869435913298262845539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35565912957275532175230359 53348869435913298262845539)
  ·
    refine ⟨80023304153869947394268309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53348869435913298262845539 80023304153869947394268309)
    ·
      refine ⟨3751092382212653784106327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80023304153869947394268309 3751092382212653784106327)
      ·
        refine ⟨5626638573318980676159491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751092382212653784106327 5626638573318980676159491)
        ·
          refine ⟨8439957859978471014239237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626638573318980676159491 8439957859978471014239237)
          ·
            refine ⟨1582492098745963315169857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8439957859978471014239237 1582492098745963315169857)
            ·
              refine ⟨1186869074059472486377393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582492098745963315169857 1186869074059472486377393)
              ·
                refine ⟨890151805544604364783045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186869074059472486377393 890151805544604364783045)
                ·
                  refine ⟨166903463539613318396821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890151805544604364783045 166903463539613318396821)
                  ·
                    rfl

theorem cell22_1462695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 4].length) (baseStart_1462695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462695 prefixEnd_1462695 := by exact prefixLift 1462695
  have htrace : WordTrace (prefixWord ++ tailWord_1462695) baseStart_1462695 baseEnd_1462695 := by
    simpa [prefixWord, tailWord_1462695, baseEnd_1462695] using wordTrace_append hprefix tailTrace_1462695
  have hstable : (prefixWord ++ tailWord_1462695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462695).length < 2 ^ (prefixWord ++ tailWord_1462695).sum := by decide
  have hdescent : baseEnd_1462695 < baseStart_1462695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462734 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_1462734 : Nat := 118140960795 + 1462734 * 2 ^ 59
def prefixEnd_1462734 : Nat := 4983230072969 + 3 ^ 40 * 1462734 * 2
def baseEnd_1462734 : Nat := 166907913705285617821781

theorem tailTrace_1462734 : CollatzResearch.WordTrace tailWord_1462734 prefixEnd_1462734 166907913705285617821781 := by
  unfold tailWord_1462734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668786485346500990439407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35566861255181338615676837 6668786485346500990439407)
  ·
    refine ⟨10003179728019751485659111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6668786485346500990439407 10003179728019751485659111)
    ·
      refine ⟨15004769592029627228488667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10003179728019751485659111 15004769592029627228488667)
      ·
        refine ⟨22507154388044440842733001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15004769592029627228488667 22507154388044440842733001)
        ·
          refine ⟨16880365791033330632049751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22507154388044440842733001 16880365791033330632049751)
          ·
            refine ⟨25320548686549995948074627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16880365791033330632049751 25320548686549995948074627)
            ·
              refine ⟨37980823029824993922111941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25320548686549995948074627 37980823029824993922111941)
              ·
                refine ⟨7121404318092186360395989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37980823029824993922111941 7121404318092186360395989)
                ·
                  refine ⟨166907913705285617821781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7121404318092186360395989 166907913705285617821781)
                  ·
                    rfl

theorem cell22_1462734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_1462734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462734 prefixEnd_1462734 := by exact prefixLift 1462734
  have htrace : WordTrace (prefixWord ++ tailWord_1462734) baseStart_1462734 baseEnd_1462734 := by
    simpa [prefixWord, tailWord_1462734, baseEnd_1462734] using wordTrace_append hprefix tailTrace_1462734
  have hstable : (prefixWord ++ tailWord_1462734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462734).length < 2 ^ (prefixWord ++ tailWord_1462734).sum := by decide
  have hdescent : baseEnd_1462734 < baseStart_1462734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462751 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 5]
def baseStart_1462751 : Nat := 118140960795 + 1462751 * 2 ^ 59
def prefixEnd_1462751 : Nat := 4983230072969 + 3 ^ 40 * 1462751 * 2
def baseEnd_1462751 : Nat := 166909853521091491930097

theorem tailTrace_1462751 : CollatzResearch.WordTrace tailWord_1462751 prefixEnd_1462751 166909853521091491930097 := by
  unfold tailWord_1462751
  simp only [CollatzResearch.WordTrace]
  refine ⟨53350911923710419826884107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35567274615806946551256071 53350911923710419826884107)
  ·
    refine ⟨80026367885565629740326161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53350911923710419826884107 80026367885565629740326161)
    ·
      refine ⟨60019775914174222305244621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80026367885565629740326161 60019775914174222305244621)
      ·
        refine ⟨22507415967815333364466733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60019775914174222305244621 22507415967815333364466733)
        ·
          refine ⟨8440280987930750011675025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22507415967815333364466733 8440280987930750011675025)
          ·
            refine ⟨6330210740948062508756269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8440280987930750011675025 6330210740948062508756269)
            ·
              refine ⟨2373829027855523440783601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6330210740948062508756269 2373829027855523440783601)
              ·
                refine ⟨1780371770891642580587701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2373829027855523440783601 1780371770891642580587701)
                ·
                  refine ⟨166909853521091491930097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1780371770891642580587701 166909853521091491930097)
                  ·
                    rfl

theorem cell22_1462751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 5].length) (baseStart_1462751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462751 prefixEnd_1462751 := by exact prefixLift 1462751
  have htrace : WordTrace (prefixWord ++ tailWord_1462751) baseStart_1462751 baseEnd_1462751 := by
    simpa [prefixWord, tailWord_1462751, baseEnd_1462751] using wordTrace_append hprefix tailTrace_1462751
  have hstable : (prefixWord ++ tailWord_1462751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462751).length < 2 ^ (prefixWord ++ tailWord_1462751).sum := by decide
  have hdescent : baseEnd_1462751 < baseStart_1462751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462766 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1462766 : Nat := 118140960795 + 1462766 * 2 ^ 59
def prefixEnd_1462766 : Nat := 4983230072969 + 3 ^ 40 * 1462766 * 2
def baseEnd_1462766 : Nat := 500734695369819436665245

theorem tailTrace_1462766 : CollatzResearch.WordTrace tailWord_1462766 prefixEnd_1462766 500734695369819436665245 := by
  unfold tailWord_1462766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668932377332009673585019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35567639345770718259120101 6668932377332009673585019)
  ·
    refine ⟨10003398565998014510377529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6668932377332009673585019 10003398565998014510377529)
    ·
      refine ⟨7502548924498510882783147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10003398565998014510377529 7502548924498510882783147)
      ·
        refine ⟨11253823386747766324174721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7502548924498510882783147 11253823386747766324174721)
        ·
          refine ⟨8440367540060824743131041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11253823386747766324174721 8440367540060824743131041)
          ·
            refine ⟨6330275655045618557348281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8440367540060824743131041 6330275655045618557348281)
            ·
              refine ⟨4747706741284213918011211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6330275655045618557348281 4747706741284213918011211)
              ·
                refine ⟨7121560111926320877016817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4747706741284213918011211 7121560111926320877016817)
                ·
                  refine ⟨5341170083944740657762613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7121560111926320877016817 5341170083944740657762613)
                  ·
                    refine ⟨500734695369819436665245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5341170083944740657762613 500734695369819436665245)
                    ·
                      rfl

theorem cell22_1462766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1462766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462766 prefixEnd_1462766 := by exact prefixLift 1462766
  have htrace : WordTrace (prefixWord ++ tailWord_1462766) baseStart_1462766 baseEnd_1462766 := by
    simpa [prefixWord, tailWord_1462766, baseEnd_1462766] using wordTrace_append hprefix tailTrace_1462766
  have hstable : (prefixWord ++ tailWord_1462766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462766).length < 2 ^ (prefixWord ++ tailWord_1462766).sum := by decide
  have hdescent : baseEnd_1462766 < baseStart_1462766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462798 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1462798 : Nat := 118140960795 + 1462798 * 2 ^ 59
def prefixEnd_1462798 : Nat := 4983230072969 + 3 ^ 40 * 1462798 * 2
def baseEnd_1462798 : Nat := 500745649623782019865147

theorem tailTrace_1462798 : CollatzResearch.WordTrace tailWord_1462798 prefixEnd_1462798 500745649623782019865147 := by
  unfold tailWord_1462798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6669078269317518356730631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35568417436360097902563365 6669078269317518356730631)
  ·
    refine ⟨10003617403976277535095947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6669078269317518356730631 10003617403976277535095947)
    ·
      refine ⟨15005426105964416302643921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10003617403976277535095947 15005426105964416302643921)
      ·
        refine ⟨11254069579473312226982941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15005426105964416302643921 11254069579473312226982941)
        ·
          refine ⟨4220276092302492085118603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11254069579473312226982941 4220276092302492085118603)
          ·
            refine ⟨6330414138453738127677905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4220276092302492085118603 6330414138453738127677905)
            ·
              refine ⟨4747810603840303595758429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6330414138453738127677905 4747810603840303595758429)
              ·
                refine ⟨1780428976440113848409411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4747810603840303595758429 1780428976440113848409411)
                ·
                  refine ⟨2670643464660170772614117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1780428976440113848409411 2670643464660170772614117)
                  ·
                    refine ⟨500745649623782019865147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2670643464660170772614117 500745649623782019865147)
                    ·
                      rfl

theorem cell22_1462798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1462798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462798 prefixEnd_1462798 := by exact prefixLift 1462798
  have htrace : WordTrace (prefixWord ++ tailWord_1462798) baseStart_1462798 baseEnd_1462798 := by
    simpa [prefixWord, tailWord_1462798, baseEnd_1462798] using wordTrace_append hprefix tailTrace_1462798
  have hstable : (prefixWord ++ tailWord_1462798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462798).length < 2 ^ (prefixWord ++ tailWord_1462798).sum := by decide
  have hdescent : baseEnd_1462798 < baseStart_1462798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462813 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 6]
def baseStart_1462813 : Nat := 118140960795 + 1462813 * 2 ^ 59
def prefixEnd_1462813 : Nat := 4983230072969 + 3 ^ 40 * 1462813 * 2
def baseEnd_1462813 : Nat := 166916928143442326913367

theorem tailTrace_1462813 : CollatzResearch.WordTrace tailWord_1462813 prefixEnd_1462813 166916928143442326913367 := by
  unfold tailWord_1462813
  simp only [CollatzResearch.WordTrace]
  refine ⟨53353173249485804415641093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35568782166323869610427395 53353173249485804415641093)
  ·
    refine ⟨10003719984278588327932705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53353173249485804415641093 10003719984278588327932705)
    ·
      refine ⟨7502789988208941245949529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10003719984278588327932705 7502789988208941245949529)
      ·
        refine ⟨5627092491156705934462147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7502789988208941245949529 5627092491156705934462147)
        ·
          refine ⟨8440638736735058901693221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627092491156705934462147 8440638736735058901693221)
          ·
            refine ⟨1582619763137823544067479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8440638736735058901693221 1582619763137823544067479)
            ·
              refine ⟨2373929644706735316101219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582619763137823544067479 2373929644706735316101219)
              ·
                refine ⟨3560894467060102974151829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373929644706735316101219 3560894467060102974151829)
                ·
                  refine ⟨166916928143442326913367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3560894467060102974151829 166916928143442326913367)
                  ·
                    rfl

theorem cell22_1462813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_1462813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462813 prefixEnd_1462813 := by exact prefixLift 1462813
  have htrace : WordTrace (prefixWord ++ tailWord_1462813) baseStart_1462813 baseEnd_1462813 := by
    simpa [prefixWord, tailWord_1462813, baseEnd_1462813] using wordTrace_append hprefix tailTrace_1462813
  have hstable : (prefixWord ++ tailWord_1462813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462813).length < 2 ^ (prefixWord ++ tailWord_1462813).sum := by decide
  have hdescent : baseEnd_1462813 < baseStart_1462813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462963 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 4, 3]
def baseStart_1462963 : Nat := 118140960795 + 1462963 * 2 ^ 59
def prefixEnd_1462963 : Nat := 4983230072969 + 3 ^ 40 * 1462963 * 2
def baseEnd_1462963 : Nat := 500802132495776589489641

theorem tailTrace_1462963 : CollatzResearch.WordTrace tailWord_1462963 prefixEnd_1462963 500802132495776589489641 := by
  unfold tailWord_1462963
  simp only [CollatzResearch.WordTrace]
  refine ⟨53358644198942380033601543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35572429465961586689067695 53358644198942380033601543)
  ·
    refine ⟨80037966298413570050402315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53358644198942380033601543 80037966298413570050402315)
    ·
      refine ⟨120056949447620355075603473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80037966298413570050402315 120056949447620355075603473)
      ·
        refine ⟨90042712085715266306702605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120056949447620355075603473 90042712085715266306702605)
        ·
          refine ⟨33766017032143224865013477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90042712085715266306702605 33766017032143224865013477)
          ·
            refine ⟨6331128193526854662190027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33766017032143224865013477 6331128193526854662190027)
            ·
              refine ⟨9496692290290281993285041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6331128193526854662190027 9496692290290281993285041)
              ·
                refine ⟨7122519217717711494963781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9496692290290281993285041 7122519217717711494963781)
                ·
                  refine ⟨1335472353322070905305709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7122519217717711494963781 1335472353322070905305709)
                  ·
                    refine ⟨500802132495776589489641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335472353322070905305709 500802132495776589489641)
                    ·
                      rfl

theorem cell22_1462963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 3].length) (baseStart_1462963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462963 prefixEnd_1462963 := by exact prefixLift 1462963
  have htrace : WordTrace (prefixWord ++ tailWord_1462963) baseStart_1462963 baseEnd_1462963 := by
    simpa [prefixWord, tailWord_1462963, baseEnd_1462963] using wordTrace_append hprefix tailTrace_1462963
  have hstable : (prefixWord ++ tailWord_1462963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462963).length < 2 ^ (prefixWord ++ tailWord_1462963).sum := by decide
  have hdescent : baseEnd_1462963 < baseStart_1462963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462976 : List Nat := [2, 1, 1, 2, 4, 2, 10]
def baseStart_1462976 : Nat := 118140960795 + 1462976 * 2 ^ 59
def prefixEnd_1462976 : Nat := 4983230072969 + 3 ^ 40 * 1462976 * 2
def baseEnd_1462976 : Nat := 18548391950424032922763

theorem tailTrace_1462976 : CollatzResearch.WordTrace tailWord_1462976 prefixEnd_1462976 18548391950424032922763 := by
  unfold tailWord_1462976
  simp only [CollatzResearch.WordTrace]
  refine ⟨26679559173947641626912391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35572745565263522169216521 26679559173947641626912391)
  ·
    refine ⟨40019338760921462440368587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26679559173947641626912391 40019338760921462440368587)
    ·
      refine ⟨60029008141382193660552881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40019338760921462440368587 60029008141382193660552881)
      ·
        refine ⟨45021756106036645245414661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60029008141382193660552881 45021756106036645245414661)
        ·
          refine ⟨8441579269881870983515249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45021756106036645245414661 8441579269881870983515249)
          ·
            refine ⟨6331184452411403237636437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8441579269881870983515249 6331184452411403237636437)
            ·
              refine ⟨18548391950424032922763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6331184452411403237636437 18548391950424032922763)
              ·
                rfl

theorem cell22_1462976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 10].length) (baseStart_1462976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462976 prefixEnd_1462976 := by exact prefixLift 1462976
  have htrace : WordTrace (prefixWord ++ tailWord_1462976) baseStart_1462976 baseEnd_1462976 := by
    simpa [prefixWord, tailWord_1462976, baseEnd_1462976] using wordTrace_append hprefix tailTrace_1462976
  have hstable : (prefixWord ++ tailWord_1462976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462976).length < 2 ^ (prefixWord ++ tailWord_1462976).sum := by decide
  have hdescent : baseEnd_1462976 < baseStart_1462976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1462980 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1462980 : Nat := 118140960795 + 1462980 * 2 ^ 59
def prefixEnd_1462980 : Nat := 4983230072969 + 3 ^ 40 * 1462980 * 2
def baseEnd_1462980 : Nat := 500807951943194211814589

theorem tailTrace_1462980 : CollatzResearch.WordTrace tailWord_1462980 prefixEnd_1462980 500807951943194211814589 := by
  unfold tailWord_1462980
  simp only [CollatzResearch.WordTrace]
  refine ⟨26679632119940395968485197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35572842826587194624646929 26679632119940395968485197)
  ·
    refine ⟨10004862044977648488181949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26679632119940395968485197 10004862044977648488181949)
    ·
      refine ⟨3751823266866618183068231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10004862044977648488181949 3751823266866618183068231)
      ·
        refine ⟨5627734900299927274602347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751823266866618183068231 5627734900299927274602347)
        ·
          refine ⟨8441602350449890911903521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627734900299927274602347 8441602350449890911903521)
          ·
            refine ⟨6331201762837418183927641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8441602350449890911903521 6331201762837418183927641)
            ·
              refine ⟨4748401322128063637945731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6331201762837418183927641 4748401322128063637945731)
              ·
                refine ⟨7122601983192095456918597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4748401322128063637945731 7122601983192095456918597)
                ·
                  refine ⟨1335487871848517898172237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7122601983192095456918597 1335487871848517898172237)
                  ·
                    refine ⟨500807951943194211814589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335487871848517898172237 500807951943194211814589)
                    ·
                      rfl

theorem cell22_1462980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1462980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1462980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1462980 prefixEnd_1462980 := by exact prefixLift 1462980
  have htrace : WordTrace (prefixWord ++ tailWord_1462980) baseStart_1462980 baseEnd_1462980 := by
    simpa [prefixWord, tailWord_1462980, baseEnd_1462980] using wordTrace_append hprefix tailTrace_1462980
  have hstable : (prefixWord ++ tailWord_1462980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1462980).length < 2 ^ (prefixWord ++ tailWord_1462980).sum := by decide
  have hdescent : baseEnd_1462980 < baseStart_1462980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1462980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463008 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 5, 3]
def baseStart_1463008 : Nat := 118140960795 + 1463008 * 2 ^ 59
def prefixEnd_1463008 : Nat := 4983230072969 + 3 ^ 40 * 1463008 * 2
def baseEnd_1463008 : Nat := 500817536915411472114503

theorem tailTrace_1463008 : CollatzResearch.WordTrace tailWord_1463008 prefixEnd_1463008 500817536915411472114503 := by
  unfold tailWord_1463008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26680142741889676359494839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35573523655852901812659785 26680142741889676359494839)
  ·
    refine ⟨40020214112834514539242259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26680142741889676359494839 40020214112834514539242259)
    ·
      refine ⟨60030321169251771808863389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40020214112834514539242259 60030321169251771808863389)
      ·
        refine ⟨22511370438469414428323771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60030321169251771808863389 22511370438469414428323771)
        ·
          refine ⟨33767055657704121642485657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22511370438469414428323771 33767055657704121642485657)
          ·
            refine ⟨25325291743278091231864243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33767055657704121642485657 25325291743278091231864243)
            ·
              refine ⟨37987937614917136847796365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25325291743278091231864243 37987937614917136847796365)
              ·
                refine ⟨14245476605593926317923637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37987937614917136847796365 14245476605593926317923637)
                ·
                  refine ⟨1335513431774430592305341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14245476605593926317923637 1335513431774430592305341)
                  ·
                    refine ⟨500817536915411472114503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335513431774430592305341 500817536915411472114503)
                    ·
                      rfl

theorem cell22_1463008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_1463008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463008 prefixEnd_1463008 := by exact prefixLift 1463008
  have htrace : WordTrace (prefixWord ++ tailWord_1463008) baseStart_1463008 baseEnd_1463008 := by
    simpa [prefixWord, tailWord_1463008, baseEnd_1463008] using wordTrace_append hprefix tailTrace_1463008
  have hstable : (prefixWord ++ tailWord_1463008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463008).length < 2 ^ (prefixWord ++ tailWord_1463008).sum := by decide
  have hdescent : baseEnd_1463008 < baseStart_1463008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463113 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_1463113 : Nat := 118140960795 + 1463113 * 2 ^ 59
def prefixEnd_1463113 : Nat := 4983230072969 + 3 ^ 40 * 1463113 * 2
def baseEnd_1463113 : Nat := 500853480561226198239181

theorem tailTrace_1463113 : CollatzResearch.WordTrace tailWord_1463113 prefixEnd_1463113 500853480561226198239181 := by
  unfold tailWord_1463113
  simp only [CollatzResearch.WordTrace]
  refine ⟨53364115148398955651561993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35576076765599303767707995 53364115148398955651561993)
  ·
    refine ⟨40023086361299216738671495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53364115148398955651561993 40023086361299216738671495)
    ·
      refine ⟨60034629541948825108007243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40023086361299216738671495 60034629541948825108007243)
      ·
        refine ⟨90051944312923237662010865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60034629541948825108007243 90051944312923237662010865)
        ·
          refine ⟨67538958234692428246508149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90051944312923237662010865 67538958234692428246508149)
          ·
            refine ⟨6331777334502415148110139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67538958234692428246508149 6331777334502415148110139)
            ·
              refine ⟨9497666001753622722165209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6331777334502415148110139 9497666001753622722165209)
              ·
                refine ⟨7123249501315217041623907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9497666001753622722165209 7123249501315217041623907)
                ·
                  refine ⟨10684874251972825562435861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7123249501315217041623907 10684874251972825562435861)
                  ·
                    refine ⟨500853480561226198239181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10684874251972825562435861 500853480561226198239181)
                    ·
                      rfl

theorem cell22_1463113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_1463113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463113 prefixEnd_1463113 := by exact prefixLift 1463113
  have htrace : WordTrace (prefixWord ++ tailWord_1463113) baseStart_1463113 baseEnd_1463113 := by
    simpa [prefixWord, tailWord_1463113, baseEnd_1463113] using wordTrace_append hprefix tailTrace_1463113
  have hstable : (prefixWord ++ tailWord_1463113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463113).length < 2 ^ (prefixWord ++ tailWord_1463113).sum := by decide
  have hdescent : baseEnd_1463113 < baseStart_1463113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463132 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1463132 : Nat := 118140960795 + 1463132 * 2 ^ 59
def prefixEnd_1463132 : Nat := 4983230072969 + 3 ^ 40 * 1463132 * 2
def baseEnd_1463132 : Nat := 500859984649516482014123

theorem tailTrace_1463132 : CollatzResearch.WordTrace tailWord_1463132 prefixEnd_1463132 500859984649516482014123 := by
  unfold tailWord_1463132
  simp only [CollatzResearch.WordTrace]
  refine ⟨26682404067665060948251825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35576538756886747931002433 26682404067665060948251825)
  ·
    refine ⟨20011803050748795711188869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26682404067665060948251825 20011803050748795711188869)
    ·
      refine ⟨3752213072015399195847913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20011803050748795711188869 3752213072015399195847913)
      ·
        refine ⟨2814159804011549396885935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3752213072015399195847913 2814159804011549396885935)
        ·
          refine ⟨4221239706017324095328903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814159804011549396885935 4221239706017324095328903)
          ·
            refine ⟨6331859559025986142993355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221239706017324095328903 6331859559025986142993355)
            ·
              refine ⟨9497789338538979214490033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6331859559025986142993355 9497789338538979214490033)
              ·
                refine ⟨7123342003904234410867525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9497789338538979214490033 7123342003904234410867525)
                ·
                  refine ⟨1335626625732043952037661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7123342003904234410867525 1335626625732043952037661)
                  ·
                    refine ⟨500859984649516482014123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335626625732043952037661 500859984649516482014123)
                    ·
                      rfl

theorem cell22_1463132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1463132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463132 prefixEnd_1463132 := by exact prefixLift 1463132
  have htrace : WordTrace (prefixWord ++ tailWord_1463132) baseStart_1463132 baseEnd_1463132 := by
    simpa [prefixWord, tailWord_1463132, baseEnd_1463132] using wordTrace_append hprefix tailTrace_1463132
  have hstable : (prefixWord ++ tailWord_1463132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463132).length < 2 ^ (prefixWord ++ tailWord_1463132).sum := by decide
  have hdescent : baseEnd_1463132 < baseStart_1463132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463160 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 3, 3]
def baseStart_1463160 : Nat := 118140960795 + 1463160 * 2 ^ 59
def prefixEnd_1463160 : Nat := 4983230072969 + 3 ^ 40 * 1463160 * 2
def baseEnd_1463160 : Nat := 500869569621733742314037

theorem tailTrace_1463160 : CollatzResearch.WordTrace tailWord_1463160 prefixEnd_1463160 500869569621733742314037 := by
  unfold tailWord_1463160
  simp only [CollatzResearch.WordTrace]
  refine ⟨26682914689614341339261467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35577219586152455119015289 26682914689614341339261467)
  ·
    refine ⟨40024372034421512008892201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26682914689614341339261467 40024372034421512008892201)
    ·
      refine ⟨30018279025816134006669151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40024372034421512008892201 30018279025816134006669151)
      ·
        refine ⟨45027418538724201010003727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30018279025816134006669151 45027418538724201010003727)
        ·
          refine ⟨67541127808086301515005591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45027418538724201010003727 67541127808086301515005591)
          ·
            refine ⟨101311691712129452272508387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67541127808086301515005591 101311691712129452272508387)
            ·
              refine ⟨151967537568194178408762581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101311691712129452272508387 151967537568194178408762581)
              ·
                refine ⟨3561739161754551056455373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151967537568194178408762581 3561739161754551056455373)
                ·
                  refine ⟨1335652185657956646170765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3561739161754551056455373 1335652185657956646170765)
                  ·
                    refine ⟨500869569621733742314037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335652185657956646170765 500869569621733742314037)
                    ·
                      rfl

theorem cell22_1463160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_1463160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463160 prefixEnd_1463160 := by exact prefixLift 1463160
  have htrace : WordTrace (prefixWord ++ tailWord_1463160) baseStart_1463160 baseEnd_1463160 := by
    simpa [prefixWord, tailWord_1463160, baseEnd_1463160] using wordTrace_append hprefix tailTrace_1463160
  have hstable : (prefixWord ++ tailWord_1463160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463160).length < 2 ^ (prefixWord ++ tailWord_1463160).sum := by decide
  have hdescent : baseEnd_1463160 < baseStart_1463160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463166 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1463166 : Nat := 118140960795 + 1463166 * 2 ^ 59
def prefixEnd_1463166 : Nat := 4983230072969 + 3 ^ 40 * 1463166 * 2
def baseEnd_1463166 : Nat := 500871623544351726664019

theorem tailTrace_1463166 : CollatzResearch.WordTrace tailWord_1463166 prefixEnd_1463166 500871623544351726664019 := by
  unfold tailWord_1463166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6670756027150868212905169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35577365478137963802160901 6670756027150868212905169)
  ·
    refine ⟨5003067020363151159678877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6670756027150868212905169 5003067020363151159678877)
    ·
      refine ⟨1876150132636181684879579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5003067020363151159678877 1876150132636181684879579)
      ·
        refine ⟨2814225198954272527319369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876150132636181684879579 2814225198954272527319369)
        ·
          refine ⟨2110668899215704395489527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2814225198954272527319369 2110668899215704395489527)
          ·
            refine ⟨3166003348823556593234291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110668899215704395489527 3166003348823556593234291)
            ·
              refine ⟨4749005023235334889851437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166003348823556593234291 4749005023235334889851437)
              ·
                refine ⟨1780876883713250583694289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4749005023235334889851437 1780876883713250583694289)
                ·
                  refine ⟨1335657662784937937770717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1780876883713250583694289 1335657662784937937770717)
                  ·
                    refine ⟨500871623544351726664019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335657662784937937770717 500871623544351726664019)
                    ·
                      rfl

theorem cell22_1463166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1463166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463166 prefixEnd_1463166 := by exact prefixLift 1463166
  have htrace : WordTrace (prefixWord ++ tailWord_1463166) baseStart_1463166 baseEnd_1463166 := by
    simpa [prefixWord, tailWord_1463166, baseEnd_1463166] using wordTrace_append hprefix tailTrace_1463166
  have hstable : (prefixWord ++ tailWord_1463166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463166).length < 2 ^ (prefixWord ++ tailWord_1463166).sum := by decide
  have hdescent : baseEnd_1463166 < baseStart_1463166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463265 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1463265 : Nat := 118140960795 + 1463265 * 2 ^ 59
def prefixEnd_1463265 : Nat := 4983230072969 + 3 ^ 40 * 1463265 * 2
def baseEnd_1463265 : Nat := 500905513267548468438715

theorem tailTrace_1463265 : CollatzResearch.WordTrace tailWord_1463265 prefixEnd_1463265 500905513267548468438715 := by
  unfold tailWord_1463265
  simp only [CollatzResearch.WordTrace]
  refine ⟨53369659043848285611095249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35579772695898857074063499 53369659043848285611095249)
  ·
    refine ⟨40027244282886214208321437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53369659043848285611095249 40027244282886214208321437)
    ·
      refine ⟨15010216606082330328120539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40027244282886214208321437 15010216606082330328120539)
      ·
        refine ⟨22515324909123495492180809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15010216606082330328120539 22515324909123495492180809)
        ·
          refine ⟨16886493681842621619135607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22515324909123495492180809 16886493681842621619135607)
          ·
            refine ⟨25329740522763932428703411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16886493681842621619135607 25329740522763932428703411)
            ·
              refine ⟨37994610784145898643055117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25329740522763932428703411 37994610784145898643055117)
              ·
                refine ⟨14247979044054711991145669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37994610784145898643055117 14247979044054711991145669)
                ·
                  refine ⟨2671496070760258498339813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14247979044054711991145669 2671496070760258498339813)
                  ·
                    refine ⟨500905513267548468438715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2671496070760258498339813 500905513267548468438715)
                    ·
                      rfl

theorem cell22_1463265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1463265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463265 prefixEnd_1463265 := by exact prefixLift 1463265
  have htrace : WordTrace (prefixWord ++ tailWord_1463265) baseStart_1463265 baseEnd_1463265 := by
    simpa [prefixWord, tailWord_1463265, baseEnd_1463265] using wordTrace_append hprefix tailTrace_1463265
  have hstable : (prefixWord ++ tailWord_1463265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463265).length < 2 ^ (prefixWord ++ tailWord_1463265).sum := by decide
  have hdescent : baseEnd_1463265 < baseStart_1463265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463267 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 4, 3]
def baseStart_1463267 : Nat := 118140960795 + 1463267 * 2 ^ 59
def prefixEnd_1463267 : Nat := 4983230072969 + 3 ^ 40 * 1463267 * 2
def baseEnd_1463267 : Nat := 500906197908421129888709

theorem tailTrace_1463267 : CollatzResearch.WordTrace tailWord_1463267 prefixEnd_1463267 500906197908421129888709 := by
  unfold tailWord_1463267
  simp only [CollatzResearch.WordTrace]
  refine ⟨53369731989841039952668055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35579821326560693301778703 53369731989841039952668055)
  ·
    refine ⟨80054597984761559929002083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53369731989841039952668055 80054597984761559929002083)
    ·
      refine ⟨120081896977142339893503125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80054597984761559929002083 120081896977142339893503125)
      ·
        refine ⟨5628838920803547182507959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120081896977142339893503125 5628838920803547182507959)
        ·
          refine ⟨8443258381205320773761939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628838920803547182507959 8443258381205320773761939)
          ·
            refine ⟨12664887571807981160642909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443258381205320773761939 12664887571807981160642909)
            ·
              refine ⟨4749332839427992935241091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12664887571807981160642909 4749332839427992935241091)
              ·
                refine ⟨7123999259141989402861637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4749332839427992935241091 7123999259141989402861637)
                ·
                  refine ⟨1335749861089123013036557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7123999259141989402861637 1335749861089123013036557)
                  ·
                    refine ⟨500906197908421129888709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335749861089123013036557 500906197908421129888709)
                    ·
                      rfl

theorem cell22_1463267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 3].length) (baseStart_1463267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463267 prefixEnd_1463267 := by exact prefixLift 1463267
  have htrace : WordTrace (prefixWord ++ tailWord_1463267) baseStart_1463267 baseEnd_1463267 := by
    simpa [prefixWord, tailWord_1463267, baseEnd_1463267] using wordTrace_append hprefix tailTrace_1463267
  have hstable : (prefixWord ++ tailWord_1463267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463267).length < 2 ^ (prefixWord ++ tailWord_1463267).sum := by decide
  have hdescent : baseEnd_1463267 < baseStart_1463267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463269 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 6]
def baseStart_1463269 : Nat := 118140960795 + 1463269 * 2 ^ 59
def prefixEnd_1463269 : Nat := 4983230072969 + 3 ^ 40 * 1463269 * 2
def baseEnd_1463269 : Nat := 166968960849764597112901

theorem tailTrace_1463269 : CollatzResearch.WordTrace tailWord_1463269 prefixEnd_1463269 166968960849764597112901 := by
  unfold tailWord_1463269
  simp only [CollatzResearch.WordTrace]
  refine ⟨53369804935833794294240861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35579869957222529529493907 53369804935833794294240861)
  ·
    refine ⟨20013676850937672860340323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53369804935833794294240861 20013676850937672860340323)
    ·
      refine ⟨30020515276406509290510485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20013676850937672860340323 30020515276406509290510485)
      ·
        refine ⟨1407211653581555122992679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30020515276406509290510485 1407211653581555122992679)
        ·
          refine ⟨2110817480372332684489019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407211653581555122992679 2110817480372332684489019)
          ·
            refine ⟨3166226220558499026733529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2110817480372332684489019 3166226220558499026733529)
            ·
              refine ⟨2374669665418874270050147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3166226220558499026733529 2374669665418874270050147)
              ·
                refine ⟨3562004498128311405075221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374669665418874270050147 3562004498128311405075221)
                ·
                  refine ⟨166968960849764597112901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3562004498128311405075221 166968960849764597112901)
                  ·
                    rfl

theorem cell22_1463269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_1463269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463269 prefixEnd_1463269 := by exact prefixLift 1463269
  have htrace : WordTrace (prefixWord ++ tailWord_1463269) baseStart_1463269 baseEnd_1463269 := by
    simpa [prefixWord, tailWord_1463269, baseEnd_1463269] using wordTrace_append hprefix tailTrace_1463269
  have hstable : (prefixWord ++ tailWord_1463269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463269).length < 2 ^ (prefixWord ++ tailWord_1463269).sum := by decide
  have hdescent : baseEnd_1463269 < baseStart_1463269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463297 : List Nat := [1, 2, 4, 1, 2, 2, 4, 6]
def baseStart_1463297 : Nat := 118140960795 + 1463297 * 2 ^ 59
def prefixEnd_1463297 : Nat := 4983230072969 + 3 ^ 40 * 1463297 * 2
def baseEnd_1463297 : Nat := 55657385280167894626513

theorem tailTrace_1463297 : CollatzResearch.WordTrace tailWord_1463297 prefixEnd_1463297 55657385280167894626513 := by
  unfold tailWord_1463297
  simp only [CollatzResearch.WordTrace]
  refine ⟨53370826179732355076260145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35580550786488236717506763 53370826179732355076260145)
  ·
    refine ⟨40028119634799266307195109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53370826179732355076260145 40028119634799266307195109)
    ·
      refine ⟨7505272431524862432599083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40028119634799266307195109 7505272431524862432599083)
      ·
        refine ⟨11257908647287293648898625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505272431524862432599083 11257908647287293648898625)
        ·
          refine ⟨8443431485465470236673969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11257908647287293648898625 8443431485465470236673969)
          ·
            refine ⟨6332573614099102677505477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8443431485465470236673969 6332573614099102677505477)
            ·
              refine ⟨1187357552643581752032277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6332573614099102677505477 1187357552643581752032277)
              ·
                refine ⟨55657385280167894626513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1187357552643581752032277 55657385280167894626513)
                ·
                  rfl

theorem cell22_1463297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 6].length) (baseStart_1463297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463297 prefixEnd_1463297 := by exact prefixLift 1463297
  have htrace : WordTrace (prefixWord ++ tailWord_1463297) baseStart_1463297 baseEnd_1463297 := by
    simpa [prefixWord, tailWord_1463297, baseEnd_1463297] using wordTrace_append hprefix tailTrace_1463297
  have hstable : (prefixWord ++ tailWord_1463297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463297).length < 2 ^ (prefixWord ++ tailWord_1463297).sum := by decide
  have hdescent : baseEnd_1463297 < baseStart_1463297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463329 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 3, 3]
def baseStart_1463329 : Nat := 118140960795 + 1463329 * 2 ^ 59
def prefixEnd_1463329 : Nat := 4983230072969 + 3 ^ 40 * 1463329 * 2
def baseEnd_1463329 : Nat := 500927421775473634838519

theorem tailTrace_1463329 : CollatzResearch.WordTrace tailWord_1463329 prefixEnd_1463329 500927421775473634838519 := by
  unfold tailWord_1463329
  simp only [CollatzResearch.WordTrace]
  refine ⟨53371993315616424541425041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35581328877077616360950027 53371993315616424541425041)
  ·
    refine ⟨40028994986712318406068781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53371993315616424541425041 40028994986712318406068781)
    ·
      refine ⟨15010873120017119402275793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40028994986712318406068781 15010873120017119402275793)
      ·
        refine ⟨11258154840012839551706845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15010873120017119402275793 11258154840012839551706845)
        ·
          refine ⟨4221808065004814831890067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11258154840012839551706845 4221808065004814831890067)
          ·
            refine ⟨6332712097507222247835101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4221808065004814831890067 6332712097507222247835101)
            ·
              refine ⟨2374767036565208342938163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6332712097507222247835101 2374767036565208342938163)
              ·
                refine ⟨3562150554847812514407245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2374767036565208342938163 3562150554847812514407245)
                ·
                  refine ⟨1335806458067929692902717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3562150554847812514407245 1335806458067929692902717)
                  ·
                    refine ⟨500927421775473634838519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1335806458067929692902717 500927421775473634838519)
                    ·
                      rfl

theorem cell22_1463329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_1463329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463329 prefixEnd_1463329 := by exact prefixLift 1463329
  have htrace : WordTrace (prefixWord ++ tailWord_1463329) baseStart_1463329 baseEnd_1463329 := by
    simpa [prefixWord, tailWord_1463329, baseEnd_1463329] using wordTrace_append hprefix tailTrace_1463329
  have hstable : (prefixWord ++ tailWord_1463329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463329).length < 2 ^ (prefixWord ++ tailWord_1463329).sum := by decide
  have hdescent : baseEnd_1463329 < baseStart_1463329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463340 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1463340 : Nat := 118140960795 + 1463340 * 2 ^ 59
def prefixEnd_1463340 : Nat := 4983230072969 + 3 ^ 40 * 1463340 * 2
def baseEnd_1463340 : Nat := 500931187300273272813485

theorem tailTrace_1463340 : CollatzResearch.WordTrace tailWord_1463340 prefixEnd_1463340 500931187300273272813485 := by
  unfold tailWord_1463340
  simp only [CollatzResearch.WordTrace]
  refine ⟨26686197259288286710037737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35581596345717715613383649 26686197259288286710037737)
  ·
    refine ⟨20014647944466215032528303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26686197259288286710037737 20014647944466215032528303)
    ·
      refine ⟨30021971916699322548792455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20014647944466215032528303 30021971916699322548792455)
      ·
        refine ⟨45032957875048983823188683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30021971916699322548792455 45032957875048983823188683)
        ·
          refine ⟨67549436812573475734783025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45032957875048983823188683 67549436812573475734783025)
          ·
            refine ⟨50662077609430106801087269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67549436812573475734783025 50662077609430106801087269)
            ·
              refine ⟨9499139551768145025203863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50662077609430106801087269 9499139551768145025203863)
              ·
                refine ⟨14248709327652217537805795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9499139551768145025203863 14248709327652217537805795)
                ·
                  refine ⟨21373063991478326306708693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14248709327652217537805795 21373063991478326306708693)
                  ·
                    refine ⟨500931187300273272813485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21373063991478326306708693 500931187300273272813485)
                    ·
                      rfl

theorem cell22_1463340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1463340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463340 prefixEnd_1463340 := by exact prefixLift 1463340
  have htrace : WordTrace (prefixWord ++ tailWord_1463340) baseStart_1463340 baseEnd_1463340 := by
    simpa [prefixWord, tailWord_1463340, baseEnd_1463340] using wordTrace_append hprefix tailTrace_1463340
  have hstable : (prefixWord ++ tailWord_1463340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463340).length < 2 ^ (prefixWord ++ tailWord_1463340).sum := by decide
  have hdescent : baseEnd_1463340 < baseStart_1463340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463466 : List Nat := [3, 1, 5, 1, 1, 1, 4, 6]
def baseStart_1463466 : Nat := 118140960795 + 1463466 * 2 ^ 59
def prefixEnd_1463466 : Nat := 4983230072969 + 3 ^ 40 * 1463466 * 2
def baseEnd_1463466 : Nat := 55663813297250104907011

theorem tailTrace_1463466 : CollatzResearch.WordTrace tailWord_1463466 prefixEnd_1463466 55663813297250104907011 := by
  unfold tailWord_1463466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13344247529030024234790563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35584660077413397959441501 13344247529030024234790563)
  ·
    refine ⟨20016371293545036352185845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13344247529030024234790563 20016371293545036352185845)
    ·
      refine ⟨1876534808769847158017423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20016371293545036352185845 1876534808769847158017423)
      ·
        refine ⟨2814802213154770737026135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876534808769847158017423 2814802213154770737026135)
        ·
          refine ⟨4222203319732156105539203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814802213154770737026135 4222203319732156105539203)
          ·
            refine ⟨6333304979598234158308805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4222203319732156105539203 6333304979598234158308805)
            ·
              refine ⟨1187494683674668904682901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6333304979598234158308805 1187494683674668904682901)
              ·
                refine ⟨55663813297250104907011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1187494683674668904682901 55663813297250104907011)
                ·
                  rfl

theorem cell22_1463466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_1463466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463466 prefixEnd_1463466 := by exact prefixLift 1463466
  have htrace : WordTrace (prefixWord ++ tailWord_1463466) baseStart_1463466 baseEnd_1463466 := by
    simpa [prefixWord, tailWord_1463466, baseEnd_1463466] using wordTrace_append hprefix tailTrace_1463466
  have hstable : (prefixWord ++ tailWord_1463466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463466).length < 2 ^ (prefixWord ++ tailWord_1463466).sum := by decide
  have hdescent : baseEnd_1463466 < baseStart_1463466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463507 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 5, 4]
def baseStart_1463507 : Nat := 118140960795 + 1463507 * 2 ^ 59
def prefixEnd_1463507 : Nat := 4983230072969 + 3 ^ 40 * 1463507 * 2
def baseEnd_1463507 : Nat := 500988354813140503887973

theorem tailTrace_1463507 : CollatzResearch.WordTrace tailWord_1463507 prefixEnd_1463507 500988354813140503887973 := by
  unfold tailWord_1463507
  simp only [CollatzResearch.WordTrace]
  refine ⟨53378485508971560941404775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35585657005981040627603183 53378485508971560941404775)
  ·
    refine ⟨80067728263457341412107163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53378485508971560941404775 80067728263457341412107163)
    ·
      refine ⟨120101592395186012118160745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80067728263457341412107163 120101592395186012118160745)
      ·
        refine ⟨90076194296389509088620559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120101592395186012118160745 90076194296389509088620559)
        ·
          refine ⟨135114291444584263632930839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90076194296389509088620559 135114291444584263632930839)
          ·
            refine ⟨202671437166876395449396259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135114291444584263632930839 202671437166876395449396259)
            ·
              refine ⟨304007155750314593174094389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202671437166876395449396259 304007155750314593174094389)
              ·
                refine ⟨28500670851591993110071349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304007155750314593174094389 28500670851591993110071349)
                ·
                  refine ⟨2671937892336749354069189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28500670851591993110071349 2671937892336749354069189)
                  ·
                    refine ⟨500988354813140503887973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2671937892336749354069189 500988354813140503887973)
                    ·
                      rfl

theorem cell22_1463507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 4].length) (baseStart_1463507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463507 prefixEnd_1463507 := by exact prefixLift 1463507
  have htrace : WordTrace (prefixWord ++ tailWord_1463507) baseStart_1463507 baseEnd_1463507 := by
    simpa [prefixWord, tailWord_1463507, baseEnd_1463507] using wordTrace_append hprefix tailTrace_1463507
  have hstable : (prefixWord ++ tailWord_1463507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463507).length < 2 ^ (prefixWord ++ tailWord_1463507).sum := by decide
  have hdescent : baseEnd_1463507 < baseStart_1463507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463552 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_1463552 : Nat := 118140960795 + 1463552 * 2 ^ 59
def prefixEnd_1463552 : Nat := 4983230072969 + 3 ^ 40 * 1463552 * 2
def baseEnd_1463552 : Nat := 501003759232775386512835

theorem tailTrace_1463552 : CollatzResearch.WordTrace tailWord_1463552 prefixEnd_1463552 501003759232775386512835 := by
  unfold tailWord_1463552
  simp only [CollatzResearch.WordTrace]
  refine ⟨26690063396904266813396455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35586751195872355751195273 26690063396904266813396455)
  ·
    refine ⟨40035095095356400220094683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26690063396904266813396455 40035095095356400220094683)
    ·
      refine ⟨60052642643034600330142025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40035095095356400220094683 60052642643034600330142025)
      ·
        refine ⟨45039481982275950247606519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60052642643034600330142025 45039481982275950247606519)
        ·
          refine ⟨67559222973413925371409779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45039481982275950247606519 67559222973413925371409779)
          ·
            refine ⟨101338834460120888057114669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67559222973413925371409779 101338834460120888057114669)
            ·
              refine ⟨38002062922545333021418001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101338834460120888057114669 38002062922545333021418001)
              ·
                refine ⟨28501547191908999766063501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38002062922545333021418001 28501547191908999766063501)
                ·
                  refine ⟨10688080196965874912273813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28501547191908999766063501 10688080196965874912273813)
                  ·
                    refine ⟨501003759232775386512835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10688080196965874912273813 501003759232775386512835)
                    ·
                      rfl

theorem cell22_1463552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_1463552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463552 prefixEnd_1463552 := by exact prefixLift 1463552
  have htrace : WordTrace (prefixWord ++ tailWord_1463552) baseStart_1463552 baseEnd_1463552 := by
    simpa [prefixWord, tailWord_1463552, baseEnd_1463552] using wordTrace_append hprefix tailTrace_1463552
  have hstable : (prefixWord ++ tailWord_1463552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463552).length < 2 ^ (prefixWord ++ tailWord_1463552).sum := by decide
  have hdescent : baseEnd_1463552 < baseStart_1463552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463586 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1463586 : Nat := 118140960795 + 1463586 * 2 ^ 59
def prefixEnd_1463586 : Nat := 4983230072969 + 3 ^ 40 * 1463586 * 2
def baseEnd_1463586 : Nat := 501015398127610631162731

theorem tailTrace_1463586 : CollatzResearch.WordTrace tailWord_1463586 prefixEnd_1463586 501015398127610631162731 := by
  unfold tailWord_1463586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13345341718921339358382653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35587577917123571622353741 13345341718921339358382653)
  ·
    refine ⟨5004503144595502259393495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13345341718921339358382653 5004503144595502259393495)
    ·
      refine ⟨7506754716893253389090243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5004503144595502259393495 7506754716893253389090243)
      ·
        refine ⟨11260132075339880083635365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7506754716893253389090243 11260132075339880083635365)
        ·
          refine ⟨2111274764126227515681631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11260132075339880083635365 2111274764126227515681631)
          ·
            refine ⟨3166912146189341273522447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111274764126227515681631 3166912146189341273522447)
            ·
              refine ⟨4750368219284011910283671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3166912146189341273522447 4750368219284011910283671)
              ·
                refine ⟨7125552328926017865425507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750368219284011910283671 7125552328926017865425507)
                ·
                  refine ⟨10688328493389026798138261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7125552328926017865425507 10688328493389026798138261)
                  ·
                    refine ⟨501015398127610631162731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10688328493389026798138261 501015398127610631162731)
                    ·
                      rfl

theorem cell22_1463586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1463586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463586 prefixEnd_1463586 := by exact prefixLift 1463586
  have htrace : WordTrace (prefixWord ++ tailWord_1463586) baseStart_1463586 baseEnd_1463586 := by
    simpa [prefixWord, tailWord_1463586, baseEnd_1463586] using wordTrace_append hprefix tailTrace_1463586
  have hstable : (prefixWord ++ tailWord_1463586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463586).length < 2 ^ (prefixWord ++ tailWord_1463586).sum := by decide
  have hdescent : baseEnd_1463586 < baseStart_1463586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463599 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 7, 3]
def baseStart_1463599 : Nat := 118140960795 + 1463599 * 2 ^ 59
def prefixEnd_1463599 : Nat := 4983230072969 + 3 ^ 40 * 1463599 * 2
def baseEnd_1463599 : Nat := 501019848293282930587691

theorem tailTrace_1463599 : CollatzResearch.WordTrace tailWord_1463599 prefixEnd_1463599 501019848293282930587691 := by
  unfold tailWord_1463599
  simp only [CollatzResearch.WordTrace]
  refine ⟨53381841024638260653753851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35587894016425507102502567 53381841024638260653753851)
  ·
    refine ⟨80072761536957390980630777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53381841024638260653753851 80072761536957390980630777)
    ·
      refine ⟨60054571152718043235473083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80072761536957390980630777 60054571152718043235473083)
      ·
        refine ⟨90081856729077064853209625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60054571152718043235473083 90081856729077064853209625)
        ·
          refine ⟨67561392546807798639907219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90081856729077064853209625 67561392546807798639907219)
          ·
            refine ⟨101342088820211697959860829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67561392546807798639907219 101342088820211697959860829)
            ·
              refine ⟨38003283307579386734947811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101342088820211697959860829 38003283307579386734947811)
              ·
                refine ⟨57004924961369080102421717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38003283307579386734947811 57004924961369080102421717)
                ·
                  refine ⟨1336052928782087814900509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 57004924961369080102421717 1336052928782087814900509)
                  ·
                    refine ⟨501019848293282930587691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336052928782087814900509 501019848293282930587691)
                    ·
                      rfl

theorem cell22_1463599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_1463599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463599 prefixEnd_1463599 := by exact prefixLift 1463599
  have htrace : WordTrace (prefixWord ++ tailWord_1463599) baseStart_1463599 baseEnd_1463599 := by
    simpa [prefixWord, tailWord_1463599, baseEnd_1463599] using wordTrace_append hprefix tailTrace_1463599
  have hstable : (prefixWord ++ tailWord_1463599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463599).length < 2 ^ (prefixWord ++ tailWord_1463599).sum := by decide
  have hdescent : baseEnd_1463599 < baseStart_1463599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463616 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 3, 3]
def baseStart_1463616 : Nat := 118140960795 + 1463616 * 2 ^ 59
def prefixEnd_1463616 : Nat := 4983230072969 + 3 ^ 40 * 1463616 * 2
def baseEnd_1463616 : Nat := 501025667740700552912639

theorem tailTrace_1463616 : CollatzResearch.WordTrace tailWord_1463616 prefixEnd_1463616 501025667740700552912639 := by
  unfold tailWord_1463616
  simp only [CollatzResearch.WordTrace]
  refine ⟨26691230532788336278561351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35588307377051115038081801 26691230532788336278561351)
  ·
    refine ⟨40036845799182504417842027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26691230532788336278561351 40036845799182504417842027)
    ·
      refine ⟨60055268698773756626763041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40036845799182504417842027 60055268698773756626763041)
      ·
        refine ⟨45041451524080317470072281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60055268698773756626763041 45041451524080317470072281)
        ·
          refine ⟨33781088643060238102554211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45041451524080317470072281 33781088643060238102554211)
          ·
            refine ⟨50671632964590357153831317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33781088643060238102554211 50671632964590357153831317)
            ·
              refine ⟨2375232795215172991585843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50671632964590357153831317 2375232795215172991585843)
              ·
                refine ⟨3562849192822759487378765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375232795215172991585843 3562849192822759487378765)
                ·
                  refine ⟨1336068447308534807767037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3562849192822759487378765 1336068447308534807767037)
                  ·
                    refine ⟨501025667740700552912639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336068447308534807767037 501025667740700552912639)
                    ·
                      rfl

theorem cell22_1463616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_1463616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463616 prefixEnd_1463616 := by exact prefixLift 1463616
  have htrace : WordTrace (prefixWord ++ tailWord_1463616) baseStart_1463616 baseEnd_1463616 := by
    simpa [prefixWord, tailWord_1463616, baseEnd_1463616] using wordTrace_append hprefix tailTrace_1463616
  have hstable : (prefixWord ++ tailWord_1463616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463616).length < 2 ^ (prefixWord ++ tailWord_1463616).sum := by decide
  have hdescent : baseEnd_1463616 < baseStart_1463616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463622 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1463622 : Nat := 118140960795 + 1463622 * 2 ^ 59
def prefixEnd_1463622 : Nat := 4983230072969 + 3 ^ 40 * 1463622 * 2
def baseEnd_1463622 : Nat := 501027721663318537262621

theorem tailTrace_1463622 : CollatzResearch.WordTrace tailWord_1463622 prefixEnd_1463622 501027721663318537262621 := by
  unfold tailWord_1463622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668208746986091736932535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35588453269036623721227413 1668208746986091736932535)
  ·
    refine ⟨2502313120479137605398803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1668208746986091736932535 2502313120479137605398803)
    ·
      refine ⟨3753469680718706408098205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502313120479137605398803 3753469680718706408098205)
      ·
        refine ⟨1407551130269514903036827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3753469680718706408098205 1407551130269514903036827)
        ·
          refine ⟨2111326695404272354555241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407551130269514903036827 2111326695404272354555241)
          ·
            refine ⟨1583495021553204265916431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2111326695404272354555241 1583495021553204265916431)
            ·
              refine ⟨2375242532329806398874647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583495021553204265916431 2375242532329806398874647)
              ·
                refine ⟨3562863798494709598311971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375242532329806398874647 3562863798494709598311971)
                ·
                  refine ⟨5344295697742064397467957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3562863798494709598311971 5344295697742064397467957)
                  ·
                    refine ⟨501027721663318537262621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5344295697742064397467957 501027721663318537262621)
                    ·
                      rfl

theorem cell22_1463622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1463622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463622 prefixEnd_1463622 := by exact prefixLift 1463622
  have htrace : WordTrace (prefixWord ++ tailWord_1463622) baseStart_1463622 baseEnd_1463622 := by
    simpa [prefixWord, tailWord_1463622, baseEnd_1463622] using wordTrace_append hprefix tailTrace_1463622
  have hstable : (prefixWord ++ tailWord_1463622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463622).length < 2 ^ (prefixWord ++ tailWord_1463622).sum := by decide
  have hdescent : baseEnd_1463622 < baseStart_1463622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463706 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_1463706 : Nat := 118140960795 + 1463706 * 2 ^ 59
def prefixEnd_1463706 : Nat := 4983230072969 + 3 ^ 40 * 1463706 * 2
def baseEnd_1463706 : Nat := 501056476579970318162363

theorem tailTrace_1463706 : CollatzResearch.WordTrace tailWord_1463706 prefixEnd_1463706 501056476579970318162363 := by
  unfold tailWord_1463706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13346435908812654481974743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35590495756833745285265981 13346435908812654481974743)
  ·
    refine ⟨20019653863218981722962115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13346435908812654481974743 20019653863218981722962115)
    ·
      refine ⟨30029480794828472584443173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20019653863218981722962115 30029480794828472584443173)
      ·
        refine ⟨5630527649030338609583095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30029480794828472584443173 5630527649030338609583095)
        ·
          refine ⟨8445791473545507914374643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5630527649030338609583095 8445791473545507914374643)
          ·
            refine ⟨12668687210318261871561965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8445791473545507914374643 12668687210318261871561965)
            ·
              refine ⟨4750757703869348201835737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12668687210318261871561965 4750757703869348201835737)
              ·
                refine ⟨3563068277902011151376803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4750757703869348201835737 3563068277902011151376803)
                ·
                  refine ⟨5344602416853016727065205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563068277902011151376803 5344602416853016727065205)
                  ·
                    refine ⟨501056476579970318162363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5344602416853016727065205 501056476579970318162363)
                    ·
                      rfl

theorem cell22_1463706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_1463706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463706 prefixEnd_1463706 := by exact prefixLift 1463706
  have htrace : WordTrace (prefixWord ++ tailWord_1463706) baseStart_1463706 baseEnd_1463706 := by
    simpa [prefixWord, tailWord_1463706, baseEnd_1463706] using wordTrace_append hprefix tailTrace_1463706
  have hstable : (prefixWord ++ tailWord_1463706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463706).length < 2 ^ (prefixWord ++ tailWord_1463706).sum := by decide
  have hdescent : baseEnd_1463706 < baseStart_1463706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463725 : List Nat := [1, 5, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1463725 : Nat := 118140960795 + 1463725 * 2 ^ 59
def prefixEnd_1463725 : Nat := 4983230072969 + 3 ^ 40 * 1463725 * 2
def baseEnd_1463725 : Nat := 167020993556086867312435

theorem tailTrace_1463725 : CollatzResearch.WordTrace tailWord_1463725 prefixEnd_1463725 167020993556086867312435 := by
  unfold tailWord_1463725
  simp only [CollatzResearch.WordTrace]
  refine ⟨53386436622181784172840629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35590957748121189448560419 53386436622181784172840629)
  ·
    refine ⟨5004978433329542266203809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53386436622181784172840629 5004978433329542266203809)
    ·
      refine ⟨3753733824997156699652857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5004978433329542266203809 3753733824997156699652857)
      ·
        refine ⟨2815300368747867524739643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3753733824997156699652857 2815300368747867524739643)
        ·
          refine ⟨4222950553121801287109465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815300368747867524739643 4222950553121801287109465)
          ·
            refine ⟨3167212914841350965332099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4222950553121801287109465 3167212914841350965332099)
            ·
              refine ⟨4750819372262026447998149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167212914841350965332099 4750819372262026447998149)
              ·
                refine ⟨890778632299129958999653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4750819372262026447998149 890778632299129958999653)
                ·
                  refine ⟨167020993556086867312435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 890778632299129958999653 167020993556086867312435)
                  ·
                    rfl

theorem cell22_1463725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1463725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463725 prefixEnd_1463725 := by exact prefixLift 1463725
  have htrace : WordTrace (prefixWord ++ tailWord_1463725) baseStart_1463725 baseEnd_1463725 := by
    simpa [prefixWord, tailWord_1463725, baseEnd_1463725] using wordTrace_append hprefix tailTrace_1463725
  have hstable : (prefixWord ++ tailWord_1463725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463725).length < 2 ^ (prefixWord ++ tailWord_1463725).sum := by decide
  have hdescent : baseEnd_1463725 < baseStart_1463725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463819 : List Nat := [1, 1, 1, 1, 9, 1, 1, 3, 1, 3]
def baseStart_1463819 : Nat := 118140960795 + 1463819 * 2 ^ 59
def prefixEnd_1463819 : Nat := 4983230072969 + 3 ^ 40 * 1463819 * 2
def baseEnd_1463819 : Nat := 501095158789275690087017

theorem tailTrace_1463819 : CollatzResearch.WordTrace tailWord_1463819 prefixEnd_1463819 501095158789275690087017 := by
  unfold tailWord_1463819
  simp only [CollatzResearch.WordTrace]
  refine ⟨53389865083841238226762511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35593243389227492151175007 53389865083841238226762511)
  ·
    refine ⟨80084797625761857340143767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53389865083841238226762511 80084797625761857340143767)
    ·
      refine ⟨120127196438642786010215651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80084797625761857340143767 120127196438642786010215651)
      ·
        refine ⟨180190794657964179015323477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120127196438642786010215651 180190794657964179015323477)
        ·
          refine ⟨1055805437449008861417911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 180190794657964179015323477 1055805437449008861417911)
          ·
            refine ⟨1583708156173513292126867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055805437449008861417911 1583708156173513292126867)
            ·
              refine ⟨2375562234260269938190301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583708156173513292126867 2375562234260269938190301)
              ·
                refine ⟨890835837847601226821363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2375562234260269938190301 890835837847601226821363)
                ·
                  refine ⟨1336253756771401840232045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890835837847601226821363 1336253756771401840232045)
                  ·
                    refine ⟨501095158789275690087017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336253756771401840232045 501095158789275690087017)
                    ·
                      rfl

theorem cell22_1463819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 3].length) (baseStart_1463819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463819 prefixEnd_1463819 := by exact prefixLift 1463819
  have htrace : WordTrace (prefixWord ++ tailWord_1463819) baseStart_1463819 baseEnd_1463819 := by
    simpa [prefixWord, tailWord_1463819, baseEnd_1463819] using wordTrace_append hprefix tailTrace_1463819
  have hstable : (prefixWord ++ tailWord_1463819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463819).length < 2 ^ (prefixWord ++ tailWord_1463819).sum := by decide
  have hdescent : baseEnd_1463819 < baseStart_1463819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463856 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_1463856 : Nat := 118140960795 + 1463856 * 2 ^ 59
def prefixEnd_1463856 : Nat := 4983230072969 + 3 ^ 40 * 1463856 * 2
def baseEnd_1463856 : Nat := 501107824645419926911903

theorem tailTrace_1463856 : CollatzResearch.WordTrace tailWord_1463856 prefixEnd_1463856 501107824645419926911903 := by
  unfold tailWord_1463856
  simp only [CollatzResearch.WordTrace]
  refine ⟨26695607292353596772929711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35594143056471462363906281 26695607292353596772929711)
  ·
    refine ⟨40043410938530395159394567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26695607292353596772929711 40043410938530395159394567)
    ·
      refine ⟨60065116407795592739091851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40043410938530395159394567 60065116407795592739091851)
      ·
        refine ⟨90097674611693389108637777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60065116407795592739091851 90097674611693389108637777)
        ·
          refine ⟨67573255958770041831478333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90097674611693389108637777 67573255958770041831478333)
          ·
            refine ⟨25339970984538765686804375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67573255958770041831478333 25339970984538765686804375)
            ·
              refine ⟨38009956476808148530206563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25339970984538765686804375 38009956476808148530206563)
              ·
                refine ⟨57014934715212222795309845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38009956476808148530206563 57014934715212222795309845)
                ·
                  refine ⟨2672575064775572943530149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57014934715212222795309845 2672575064775572943530149)
                  ·
                    refine ⟨501107824645419926911903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2672575064775572943530149 501107824645419926911903)
                    ·
                      rfl

theorem cell22_1463856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_1463856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463856 prefixEnd_1463856 := by exact prefixLift 1463856
  have htrace : WordTrace (prefixWord ++ tailWord_1463856) baseStart_1463856 baseEnd_1463856 := by
    simpa [prefixWord, tailWord_1463856, baseEnd_1463856] using wordTrace_append hprefix tailTrace_1463856
  have hstable : (prefixWord ++ tailWord_1463856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463856).length < 2 ^ (prefixWord ++ tailWord_1463856).sum := by decide
  have hdescent : baseEnd_1463856 < baseStart_1463856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463871 : List Nat := [1, 1, 2, 2, 3, 3, 2, 8]
def baseStart_1463871 : Nat := 118140960795 + 1463871 * 2 ^ 59
def prefixEnd_1463871 : Nat := 4983230072969 + 3 ^ 40 * 1463871 * 2
def baseEnd_1463871 : Nat := 55679217716884987531873

theorem tailTrace_1463871 : CollatzResearch.WordTrace tailWord_1463871 prefixEnd_1463871 55679217716884987531873 := by
  unfold tailWord_1463871
  simp only [CollatzResearch.WordTrace]
  refine ⟨53391761679652851107655467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35594507786435234071770311 53391761679652851107655467)
  ·
    refine ⟨80087642519479276661483201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53391761679652851107655467 80087642519479276661483201)
    ·
      refine ⟨60065731889609457496112401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80087642519479276661483201 60065731889609457496112401)
      ·
        refine ⟨45049298917207093122084301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60065731889609457496112401 45049298917207093122084301)
        ·
          refine ⟨16893487093952659920781613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45049298917207093122084301 16893487093952659920781613)
          ·
            refine ⟨6335057660232247470293105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16893487093952659920781613 6335057660232247470293105)
            ·
              refine ⟨4751293245174185602719829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335057660232247470293105 4751293245174185602719829)
              ·
                refine ⟨55679217716884987531873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4751293245174185602719829 55679217716884987531873)
                ·
                  rfl

theorem cell22_1463871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 8].length) (baseStart_1463871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463871 prefixEnd_1463871 := by exact prefixLift 1463871
  have htrace : WordTrace (prefixWord ++ tailWord_1463871) baseStart_1463871 baseEnd_1463871 := by
    simpa [prefixWord, tailWord_1463871, baseEnd_1463871] using wordTrace_append hprefix tailTrace_1463871
  have hstable : (prefixWord ++ tailWord_1463871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463871).length < 2 ^ (prefixWord ++ tailWord_1463871).sum := by decide
  have hdescent : baseEnd_1463871 < baseStart_1463871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463916 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 9]
def baseStart_1463916 : Nat := 118140960795 + 1463916 * 2 ^ 59
def prefixEnd_1463916 : Nat := 4983230072969 + 3 ^ 40 * 1463916 * 2
def baseEnd_1463916 : Nat := 167042787957199923470573

theorem tailTrace_1463916 : CollatzResearch.WordTrace tailWord_1463916 prefixEnd_1463916 167042787957199923470573 := by
  unfold tailWord_1463916
  simp only [CollatzResearch.WordTrace]
  refine ⟨26696701482244911896521801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35595601976326549195362401 26696701482244911896521801)
  ·
    refine ⟨20022526111683683922391351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26696701482244911896521801 20022526111683683922391351)
    ·
      refine ⟨30033789167525525883587027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20022526111683683922391351 30033789167525525883587027)
      ·
        refine ⟨45050683751288288825380541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30033789167525525883587027 45050683751288288825380541)
        ·
          refine ⟨16894006406733108309517703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45050683751288288825380541 16894006406733108309517703)
          ·
            refine ⟨25341009610099662464276555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16894006406733108309517703 25341009610099662464276555)
            ·
              refine ⟨38011514415149493696414833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25341009610099662464276555 38011514415149493696414833)
              ·
                refine ⟨28508635811362120272311125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38011514415149493696414833 28508635811362120272311125)
                ·
                  refine ⟨167042787957199923470573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28508635811362120272311125 167042787957199923470573)
                  ·
                    rfl

theorem cell22_1463916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_1463916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463916 prefixEnd_1463916 := by exact prefixLift 1463916
  have htrace : WordTrace (prefixWord ++ tailWord_1463916) baseStart_1463916 baseEnd_1463916 := by
    simpa [prefixWord, tailWord_1463916, baseEnd_1463916] using wordTrace_append hprefix tailTrace_1463916
  have hstable : (prefixWord ++ tailWord_1463916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463916).length < 2 ^ (prefixWord ++ tailWord_1463916).sum := by decide
  have hdescent : baseEnd_1463916 < baseStart_1463916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463920 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 3, 3]
def baseStart_1463920 : Nat := 118140960795 + 1463920 * 2 ^ 59
def prefixEnd_1463920 : Nat := 4983230072969 + 3 ^ 40 * 1463920 * 2
def baseEnd_1463920 : Nat := 501129733153345093311707

theorem tailTrace_1463920 : CollatzResearch.WordTrace tailWord_1463920 prefixEnd_1463920 501129733153345093311707 := by
  unfold tailWord_1463920
  simp only [CollatzResearch.WordTrace]
  refine ⟨26696774428237666238094607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35595699237650221650792809 26696774428237666238094607)
  ·
    refine ⟨40045161642356499357141911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26696774428237666238094607 40045161642356499357141911)
    ·
      refine ⟨60067742463534749035712867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40045161642356499357141911 60067742463534749035712867)
      ·
        refine ⟨90101613695302123553569301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60067742463534749035712867 90101613695302123553569301)
        ·
          refine ⟨4223513141967287041573561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90101613695302123553569301 4223513141967287041573561)
          ·
            refine ⟨3167634856475465281180171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4223513141967287041573561 3167634856475465281180171)
            ·
              refine ⟨4751452284713197921770257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167634856475465281180171 4751452284713197921770257)
              ·
                refine ⟨3563589213534898441327693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4751452284713197921770257 3563589213534898441327693)
                ·
                  refine ⟨1336345955075586915497885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3563589213534898441327693 1336345955075586915497885)
                  ·
                    refine ⟨501129733153345093311707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336345955075586915497885 501129733153345093311707)
                    ·
                      rfl

theorem cell22_1463920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_1463920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463920 prefixEnd_1463920 := by exact prefixLift 1463920
  have htrace : WordTrace (prefixWord ++ tailWord_1463920) baseStart_1463920 baseEnd_1463920 := by
    simpa [prefixWord, tailWord_1463920, baseEnd_1463920] using wordTrace_append hprefix tailTrace_1463920
  have hstable : (prefixWord ++ tailWord_1463920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463920).length < 2 ^ (prefixWord ++ tailWord_1463920).sum := by decide
  have hdescent : baseEnd_1463920 < baseStart_1463920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463931 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 1, 7]
def baseStart_1463931 : Nat := 118140960795 + 1463931 * 2 ^ 59
def prefixEnd_1463931 : Nat := 4983230072969 + 3 ^ 40 * 1463931 * 2
def baseEnd_1463931 : Nat := 501133498678144731286673

theorem tailTrace_1463931 : CollatzResearch.WordTrace tailWord_1463931 prefixEnd_1463931 501133498678144731286673 := by
  unfold tailWord_1463931
  simp only [CollatzResearch.WordTrace]
  refine ⟨53393950059435481354839647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35595966706290320903226431 53393950059435481354839647)
  ·
    refine ⟨80090925089153222032259471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53393950059435481354839647 80090925089153222032259471)
    ·
      refine ⟨120136387633729833048389207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80090925089153222032259471 120136387633729833048389207)
      ·
        refine ⟨180204581450594749572583811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120136387633729833048389207 180204581450594749572583811)
        ·
          refine ⟨270306872175892124358875717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180204581450594749572583811 270306872175892124358875717)
          ·
            refine ⟨50682538532979773317289197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270306872175892124358875717 50682538532979773317289197)
            ·
              refine ⟨19005951949867414993983449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50682538532979773317289197 19005951949867414993983449)
              ·
                refine ⟨14254463962400561245487587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19005951949867414993983449 14254463962400561245487587)
                ·
                  refine ⟨21381695943600841868231381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14254463962400561245487587 21381695943600841868231381)
                  ·
                    refine ⟨501133498678144731286673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21381695943600841868231381 501133498678144731286673)
                    ·
                      rfl

theorem cell22_1463931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_1463931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463931 prefixEnd_1463931 := by exact prefixLift 1463931
  have htrace : WordTrace (prefixWord ++ tailWord_1463931) baseStart_1463931 baseEnd_1463931 := by
    simpa [prefixWord, tailWord_1463931, baseEnd_1463931] using wordTrace_append hprefix tailTrace_1463931
  have hstable : (prefixWord ++ tailWord_1463931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463931).length < 2 ^ (prefixWord ++ tailWord_1463931).sum := by decide
  have hdescent : baseEnd_1463931 < baseStart_1463931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463937 : List Nat := [1, 2, 4, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1463937 : Nat := 118140960795 + 1463937 * 2 ^ 59
def prefixEnd_1463937 : Nat := 4983230072969 + 3 ^ 40 * 1463937 * 2
def baseEnd_1463937 : Nat := 501135552600762715636655

theorem tailTrace_1463937 : CollatzResearch.WordTrace tailWord_1463937 prefixEnd_1463937 501135552600762715636655 := by
  unfold tailWord_1463937
  simp only [CollatzResearch.WordTrace]
  refine ⟨53394168897413744379558065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35596112598275829586372043 53394168897413744379558065)
  ·
    refine ⟨40045626673060308284668549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53394168897413744379558065 40045626673060308284668549)
    ·
      refine ⟨7508555001198807803375353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40045626673060308284668549 7508555001198807803375353)
      ·
        refine ⟨5631416250899105852531515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7508555001198807803375353 5631416250899105852531515)
        ·
          refine ⟨8447124376348658778797273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631416250899105852531515 8447124376348658778797273)
          ·
            refine ⟨6335343282261494084097955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8447124376348658778797273 6335343282261494084097955)
            ·
              refine ⟨9503014923392241126146933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335343282261494084097955 9503014923392241126146933)
              ·
                refine ⟨890907649068022605576275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9503014923392241126146933 890907649068022605576275)
                ·
                  refine ⟨1336361473602033908364413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 890907649068022605576275 1336361473602033908364413)
                  ·
                    refine ⟨501135552600762715636655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336361473602033908364413 501135552600762715636655)
                    ·
                      rfl

theorem cell22_1463937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1463937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463937 prefixEnd_1463937 := by exact prefixLift 1463937
  have htrace : WordTrace (prefixWord ++ tailWord_1463937) baseStart_1463937 baseEnd_1463937 := by
    simpa [prefixWord, tailWord_1463937, baseEnd_1463937] using wordTrace_append hprefix tailTrace_1463937
  have hstable : (prefixWord ++ tailWord_1463937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463937).length < 2 ^ (prefixWord ++ tailWord_1463937).sum := by decide
  have hdescent : baseEnd_1463937 < baseStart_1463937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463950 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_1463950 : Nat := 118140960795 + 1463950 * 2 ^ 59
def prefixEnd_1463950 : Nat := 4983230072969 + 3 ^ 40 * 1463950 * 2
def baseEnd_1463950 : Nat := 167046667588811671687205

theorem tailTrace_1463950 : CollatzResearch.WordTrace tailWord_1463950 prefixEnd_1463950 167046667588811671687205 := by
  unfold tailWord_1463950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674330380795830949972663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35596428697577765066520869 6674330380795830949972663)
  ·
    refine ⟨10011495571193746424958995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6674330380795830949972663 10011495571193746424958995)
    ·
      refine ⟨15017243356790619637438493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10011495571193746424958995 15017243356790619637438493)
      ·
        refine ⟨5631466258796482364039435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15017243356790619637438493 5631466258796482364039435)
        ·
          refine ⟨8447199388194723546059153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631466258796482364039435 8447199388194723546059153)
          ·
            refine ⟨6335399541146042659544365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8447199388194723546059153 6335399541146042659544365)
            ·
              refine ⟨2375774827929765997329137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6335399541146042659544365 2375774827929765997329137)
              ·
                refine ⟨1781831120947324497996853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2375774827929765997329137 1781831120947324497996853)
                ·
                  refine ⟨167046667588811671687205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1781831120947324497996853 167046667588811671687205)
                  ·
                    rfl

theorem cell22_1463950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_1463950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463950 prefixEnd_1463950 := by exact prefixLift 1463950
  have htrace : WordTrace (prefixWord ++ tailWord_1463950) baseStart_1463950 baseEnd_1463950 := by
    simpa [prefixWord, tailWord_1463950, baseEnd_1463950] using wordTrace_append hprefix tailTrace_1463950
  have hstable : (prefixWord ++ tailWord_1463950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463950).length < 2 ^ (prefixWord ++ tailWord_1463950).sum := by decide
  have hdescent : baseEnd_1463950 < baseStart_1463950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1463993 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_1463993 : Nat := 118140960795 + 1463993 * 2 ^ 59
def prefixEnd_1463993 : Nat := 4983230072969 + 3 ^ 40 * 1463993 * 2
def baseEnd_1463993 : Nat := 501154722545197236236483

theorem tailTrace_1463993 : CollatzResearch.WordTrace tailWord_1463993 prefixEnd_1463993 501154722545197236236483 := by
  unfold tailWord_1463993
  simp only [CollatzResearch.WordTrace]
  refine ⟨53396211385210865943596633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35597474256807243962397755 53396211385210865943596633)
  ·
    refine ⟨40047158538908149457697475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53396211385210865943596633 40047158538908149457697475)
    ·
      refine ⟨60070737808362224186546213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40047158538908149457697475 60070737808362224186546213)
      ·
        refine ⟨11263263339067917034977415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60070737808362224186546213 11263263339067917034977415)
        ·
          refine ⟨16894895008601875552466123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11263263339067917034977415 16894895008601875552466123)
          ·
            refine ⟨25342342512902813328699185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16894895008601875552466123 25342342512902813328699185)
            ·
              refine ⟨19006756884677109996524389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25342342512902813328699185 19006756884677109996524389)
              ·
                refine ⟨3563766915876958124348323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19006756884677109996524389 3563766915876958124348323)
                ·
                  refine ⟨5345650373815437186522485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563766915876958124348323 5345650373815437186522485)
                  ·
                    refine ⟨501154722545197236236483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5345650373815437186522485 501154722545197236236483)
                    ·
                      rfl

theorem cell22_1463993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_1463993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1463993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1463993 prefixEnd_1463993 := by exact prefixLift 1463993
  have htrace : WordTrace (prefixWord ++ tailWord_1463993) baseStart_1463993 baseEnd_1463993 := by
    simpa [prefixWord, tailWord_1463993, baseEnd_1463993] using wordTrace_append hprefix tailTrace_1463993
  have hstable : (prefixWord ++ tailWord_1463993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1463993).length < 2 ^ (prefixWord ++ tailWord_1463993).sum := by decide
  have hdescent : baseEnd_1463993 < baseStart_1463993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1463993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464012 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 6]
def baseStart_1464012 : Nat := 118140960795 + 1464012 * 2 ^ 59
def prefixEnd_1464012 : Nat := 4983230072969 + 3 ^ 40 * 1464012 * 2
def baseEnd_1464012 : Nat := 167053742211162506670475

theorem tailTrace_1464012 : CollatzResearch.WordTrace tailWord_1464012 prefixEnd_1464012 167053742211162506670475 := by
  unfold tailWord_1464012
  simp only [CollatzResearch.WordTrace]
  refine ⟨26698452186071016094269145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35597936248094688125692193 26698452186071016094269145)
  ·
    refine ⟨20023839139553262070701859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26698452186071016094269145 20023839139553262070701859)
    ·
      refine ⟨30035758709329893106052789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20023839139553262070701859 30035758709329893106052789)
      ·
        refine ⟨2815852378999677478692449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30035758709329893106052789 2815852378999677478692449)
        ·
          refine ⟨2111889284249758109019337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2815852378999677478692449 2111889284249758109019337)
          ·
            refine ⟨1583916963187318581764503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2111889284249758109019337 1583916963187318581764503)
            ·
              refine ⟨2375875444780977872646755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583916963187318581764503 2375875444780977872646755)
              ·
                refine ⟨3563813167171466808970133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2375875444780977872646755 3563813167171466808970133)
                ·
                  refine ⟨167053742211162506670475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3563813167171466808970133 167053742211162506670475)
                  ·
                    rfl

theorem cell22_1464012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_1464012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464012 prefixEnd_1464012 := by exact prefixLift 1464012
  have htrace : WordTrace (prefixWord ++ tailWord_1464012) baseStart_1464012 baseEnd_1464012 := by
    simpa [prefixWord, tailWord_1464012, baseEnd_1464012] using wordTrace_append hprefix tailTrace_1464012
  have hstable : (prefixWord ++ tailWord_1464012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464012).length < 2 ^ (prefixWord ++ tailWord_1464012).sum := by decide
  have hdescent : baseEnd_1464012 < baseStart_1464012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464023 : List Nat := [1, 1, 3, 2, 1, 3, 4, 7]
def baseStart_1464023 : Nat := 118140960795 + 1464023 * 2 ^ 59
def prefixEnd_1464023 : Nat := 4983230072969 + 3 ^ 40 * 1464023 * 2
def baseEnd_1464023 : Nat := 55684999128698573109599

theorem tailTrace_1464023 : CollatzResearch.WordTrace tailWord_1464023 prefixEnd_1464023 55684999128698573109599 := by
  unfold tailWord_1464023
  simp only [CollatzResearch.WordTrace]
  refine ⟨53397305575102181067188723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35598203716734787378125815 53397305575102181067188723)
  ·
    refine ⟨80095958362653271600783085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53397305575102181067188723 80095958362653271600783085)
    ·
      refine ⟨30035984385994976850293657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80095958362653271600783085 30035984385994976850293657)
      ·
        refine ⟨22526988289496232637720243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30035984385994976850293657 22526988289496232637720243)
        ·
          refine ⟨33790482434244348956580365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22526988289496232637720243 33790482434244348956580365)
          ·
            refine ⟨12671430912841630858717637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33790482434244348956580365 12671430912841630858717637)
            ·
              refine ⟨2375893296157805786009557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12671430912841630858717637 2375893296157805786009557)
              ·
                refine ⟨55684999128698573109599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2375893296157805786009557 55684999128698573109599)
                ·
                  rfl

theorem cell22_1464023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 7].length) (baseStart_1464023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464023 prefixEnd_1464023 := by exact prefixLift 1464023
  have htrace : WordTrace (prefixWord ++ tailWord_1464023) baseStart_1464023 baseEnd_1464023 := by
    simpa [prefixWord, tailWord_1464023, baseEnd_1464023] using wordTrace_append hprefix tailTrace_1464023
  have hstable : (prefixWord ++ tailWord_1464023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464023).length < 2 ^ (prefixWord ++ tailWord_1464023).sum := by decide
  have hdescent : baseEnd_1464023 < baseStart_1464023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464085 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 5]
def baseStart_1464085 : Nat := 118140960795 + 1464085 * 2 ^ 59
def prefixEnd_1464085 : Nat := 4983230072969 + 3 ^ 40 * 1464085 * 2
def baseEnd_1464085 : Nat := 167062072008446554312067

theorem tailTrace_1464085 : CollatzResearch.WordTrace tailWord_1464085 prefixEnd_1464085 167062072008446554312067 := by
  unfold tailWord_1464085
  simp only [CollatzResearch.WordTrace]
  refine ⟨53399566900877565655945709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35599711267251710437297139 53399566900877565655945709)
  ·
    refine ⟨20024837587829087120979641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53399566900877565655945709 20024837587829087120979641)
    ·
      refine ⟨15018628190871815340734731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20024837587829087120979641 15018628190871815340734731)
      ·
        refine ⟨22527942286307723011102097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15018628190871815340734731 22527942286307723011102097)
        ·
          refine ⟨16895956714730792258326573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22527942286307723011102097 16895956714730792258326573)
          ·
            refine ⟨6335983768024047096872465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16895956714730792258326573 6335983768024047096872465)
            ·
              refine ⟨4751987826018035322654349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335983768024047096872465 4751987826018035322654349)
              ·
                refine ⟨1781995434756763245995381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4751987826018035322654349 1781995434756763245995381)
                ·
                  refine ⟨167062072008446554312067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1781995434756763245995381 167062072008446554312067)
                  ·
                    rfl

theorem cell22_1464085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_1464085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464085 prefixEnd_1464085 := by exact prefixLift 1464085
  have htrace : WordTrace (prefixWord ++ tailWord_1464085) baseStart_1464085 baseEnd_1464085 := by
    simpa [prefixWord, tailWord_1464085, baseEnd_1464085] using wordTrace_append hprefix tailTrace_1464085
  have hstable : (prefixWord ++ tailWord_1464085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464085).length < 2 ^ (prefixWord ++ tailWord_1464085).sum := by decide
  have hdescent : baseEnd_1464085 < baseStart_1464085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464128 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_1464128 : Nat := 118140960795 + 1464128 * 2 ^ 59
def prefixEnd_1464128 : Nat := 4983230072969 + 3 ^ 40 * 1464128 * 2
def baseEnd_1464128 : Nat := 501200935804101884111069

theorem tailTrace_1464128 : CollatzResearch.WordTrace tailWord_1464128 prefixEnd_1464128 501200935804101884111069 := by
  unfold tailWord_1464128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26700567619860891999880519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35600756826481189333174025 26700567619860891999880519)
  ·
    refine ⟨40050851429791337999820779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26700567619860891999880519 40050851429791337999820779)
    ·
      refine ⟨60076277144687006999731169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40050851429791337999820779 60076277144687006999731169)
      ·
        refine ⟨45057207858515255249798377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60076277144687006999731169 45057207858515255249798377)
        ·
          refine ⟨33792905893886441437348783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45057207858515255249798377 33792905893886441437348783)
          ·
            refine ⟨50689358840829662156023175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33792905893886441437348783 50689358840829662156023175)
            ·
              refine ⟨76034038261244493234034763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50689358840829662156023175 76034038261244493234034763)
              ·
                refine ⟨114051057391866739851052145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76034038261244493234034763 114051057391866739851052145)
                ·
                  refine ⟨85538293043900054888289109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114051057391866739851052145 85538293043900054888289109)
                  ·
                    refine ⟨501200935804101884111069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 85538293043900054888289109 501200935804101884111069)
                    ·
                      rfl

theorem cell22_1464128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_1464128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464128 prefixEnd_1464128 := by exact prefixLift 1464128
  have htrace : WordTrace (prefixWord ++ tailWord_1464128) baseStart_1464128 baseEnd_1464128 := by
    simpa [prefixWord, tailWord_1464128, baseEnd_1464128] using wordTrace_append hprefix tailTrace_1464128
  have hstable : (prefixWord ++ tailWord_1464128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464128).length < 2 ^ (prefixWord ++ tailWord_1464128).sum := by decide
  have hdescent : baseEnd_1464128 < baseStart_1464128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464134 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1464134 : Nat := 118140960795 + 1464134 * 2 ^ 59
def prefixEnd_1464134 : Nat := 4983230072969 + 3 ^ 40 * 1464134 * 2
def baseEnd_1464134 : Nat := 501202989726719868461051

theorem tailTrace_1464134 : CollatzResearch.WordTrace tailWord_1464134 prefixEnd_1464134 501202989726719868461051 := by
  unfold tailWord_1464134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668792314928126469514983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35600902718466698016319637 1668792314928126469514983)
  ·
    refine ⟨2503188472392189704272475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1668792314928126469514983 2503188472392189704272475)
    ·
      refine ⟨3754782708588284556408713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2503188472392189704272475 3754782708588284556408713)
      ·
        refine ⟨2816087031441213417306535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3754782708588284556408713 2816087031441213417306535)
        ·
          refine ⟨4224130547161820125959803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816087031441213417306535 4224130547161820125959803)
          ·
            refine ⟨6336195820742730188939705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224130547161820125959803 6336195820742730188939705)
            ·
              refine ⟨4752146865557047641704779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6336195820742730188939705 4752146865557047641704779)
              ·
                refine ⟨7128220298335571462557169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4752146865557047641704779 7128220298335571462557169)
                ·
                  refine ⟨5346165223751678596917877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7128220298335571462557169 5346165223751678596917877)
                  ·
                    refine ⟨501202989726719868461051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5346165223751678596917877 501202989726719868461051)
                    ·
                      rfl

theorem cell22_1464134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1464134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464134 prefixEnd_1464134 := by exact prefixLift 1464134
  have htrace : WordTrace (prefixWord ++ tailWord_1464134) baseStart_1464134 baseEnd_1464134 := by
    simpa [prefixWord, tailWord_1464134, baseEnd_1464134] using wordTrace_append hprefix tailTrace_1464134
  have hstable : (prefixWord ++ tailWord_1464134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464134).length < 2 ^ (prefixWord ++ tailWord_1464134).sum := by decide
  have hdescent : baseEnd_1464134 < baseStart_1464134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464160 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_1464160 : Nat := 118140960795 + 1464160 * 2 ^ 59
def prefixEnd_1464160 : Nat := 4983230072969 + 3 ^ 40 * 1464160 * 2
def baseEnd_1464160 : Nat := 501211890058064467310971

theorem tailTrace_1464160 : CollatzResearch.WordTrace tailWord_1464160 prefixEnd_1464160 501211890058064467310971 := by
  unfold tailWord_1464160
  simp only [CollatzResearch.WordTrace]
  refine ⟨26701151187802926732462967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35601534917070568976617289 26701151187802926732462967)
  ·
    refine ⟨40051726781704390098694451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26701151187802926732462967 40051726781704390098694451)
    ·
      refine ⟨60077590172556585148041677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40051726781704390098694451 60077590172556585148041677)
      ·
        refine ⟨22529096314708719430515629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60077590172556585148041677 22529096314708719430515629)
        ·
          refine ⟨8448411118015769786443361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22529096314708719430515629 8448411118015769786443361)
          ·
            refine ⟨6336308338511827339832521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8448411118015769786443361 6336308338511827339832521)
            ·
              refine ⟨4752231253883870504874391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6336308338511827339832521 4752231253883870504874391)
              ·
                refine ⟨7128346880825805757311587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4752231253883870504874391 7128346880825805757311587)
                ·
                  refine ⟨10692520321238708635967381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7128346880825805757311587 10692520321238708635967381)
                  ·
                    refine ⟨501211890058064467310971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10692520321238708635967381 501211890058064467310971)
                    ·
                      rfl

theorem cell22_1464160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_1464160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464160 prefixEnd_1464160 := by exact prefixLift 1464160
  have htrace : WordTrace (prefixWord ++ tailWord_1464160) baseStart_1464160 baseEnd_1464160 := by
    simpa [prefixWord, tailWord_1464160, baseEnd_1464160] using wordTrace_append hprefix tailTrace_1464160
  have hstable : (prefixWord ++ tailWord_1464160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464160).length < 2 ^ (prefixWord ++ tailWord_1464160).sum := by decide
  have hdescent : baseEnd_1464160 < baseStart_1464160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464224 : List Nat := [2, 1, 1, 4, 1, 1, 1, 7, 1, 3]
def baseStart_1464224 : Nat := 118140960795 + 1464224 * 2 ^ 59
def prefixEnd_1464224 : Nat := 4983230072969 + 3 ^ 40 * 1464224 * 2
def baseEnd_1464224 : Nat := 501233798565989633710775

theorem tailTrace_1464224 : CollatzResearch.WordTrace tailWord_1464224 prefixEnd_1464224 501233798565989633710775 := by
  unfold tailWord_1464224
  simp only [CollatzResearch.WordTrace]
  refine ⟨26702318323686996197627863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35603091098249328263503817 26702318323686996197627863)
  ·
    refine ⟨40053477485530494296441795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26702318323686996197627863 40053477485530494296441795)
    ·
      refine ⟨60080216228295741444662693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40053477485530494296441795 60080216228295741444662693)
      ·
        refine ⟨11265040542805451520874255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60080216228295741444662693 11265040542805451520874255)
        ·
          refine ⟨16897560814208177281311383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11265040542805451520874255 16897560814208177281311383)
          ·
            refine ⟨25346341221312265921967075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16897560814208177281311383 25346341221312265921967075)
            ·
              refine ⟨38019511831968398882950613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25346341221312265921967075 38019511831968398882950613)
              ·
                refine ⟨891082308561759348819155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38019511831968398882950613 891082308561759348819155)
                ·
                  refine ⟨1336623462842639023228733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891082308561759348819155 1336623462842639023228733)
                  ·
                    refine ⟨501233798565989633710775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336623462842639023228733 501233798565989633710775)
                    ·
                      rfl

theorem cell22_1464224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 3].length) (baseStart_1464224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464224 prefixEnd_1464224 := by exact prefixLift 1464224
  have htrace : WordTrace (prefixWord ++ tailWord_1464224) baseStart_1464224 baseEnd_1464224 := by
    simpa [prefixWord, tailWord_1464224, baseEnd_1464224] using wordTrace_append hprefix tailTrace_1464224
  have hstable : (prefixWord ++ tailWord_1464224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464224).length < 2 ^ (prefixWord ++ tailWord_1464224).sum := by decide
  have hdescent : baseEnd_1464224 < baseStart_1464224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464241 : List Nat := [1, 2, 2, 4, 2, 2, 1, 4, 1, 3]
def baseStart_1464241 : Nat := 118140960795 + 1464241 * 2 ^ 59
def prefixEnd_1464241 : Nat := 4983230072969 + 3 ^ 40 * 1464241 * 2
def baseEnd_1464241 : Nat := 501239618013407256035723

theorem tailTrace_1464241 : CollatzResearch.WordTrace tailWord_1464241 prefixEnd_1464241 501239618013407256035723 := by
  unfold tailWord_1464241
  simp only [CollatzResearch.WordTrace]
  refine ⟨53405256688312404298624577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35603504458874936199083051 53405256688312404298624577)
  ·
    refine ⟨40053942516234303223968433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53405256688312404298624577 40053942516234303223968433)
    ·
      refine ⟨30040456887175727417976325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40053942516234303223968433 30040456887175727417976325)
      ·
        refine ⟨5632585666345448890870561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30040456887175727417976325 5632585666345448890870561)
        ·
          refine ⟨4224439249759086668152921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5632585666345448890870561 4224439249759086668152921)
          ·
            refine ⟨3168329437319315001114691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4224439249759086668152921 3168329437319315001114691)
            ·
              refine ⟨4752494155978972501672037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168329437319315001114691 4752494155978972501672037)
              ·
                refine ⟨891092654246057344063507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4752494155978972501672037 891092654246057344063507)
                ·
                  refine ⟨1336638981369086016095261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891092654246057344063507 1336638981369086016095261)
                  ·
                    refine ⟨501239618013407256035723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336638981369086016095261 501239618013407256035723)
                    ·
                      rfl

theorem cell22_1464241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_1464241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464241 prefixEnd_1464241 := by exact prefixLift 1464241
  have htrace : WordTrace (prefixWord ++ tailWord_1464241) baseStart_1464241 baseEnd_1464241 := by
    simpa [prefixWord, tailWord_1464241, baseEnd_1464241] using wordTrace_append hprefix tailTrace_1464241
  have hstable : (prefixWord ++ tailWord_1464241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464241).length < 2 ^ (prefixWord ++ tailWord_1464241).sum := by decide
  have hdescent : baseEnd_1464241 < baseStart_1464241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464265 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 6]
def baseStart_1464265 : Nat := 118140960795 + 1464265 * 2 ^ 59
def prefixEnd_1464265 : Nat := 4983230072969 + 3 ^ 40 * 1464265 * 2
def baseEnd_1464265 : Nat := 167082611234626397811883

theorem tailTrace_1464265 : CollatzResearch.WordTrace tailWord_1464265 prefixEnd_1464265 167082611234626397811883 := by
  unfold tailWord_1464265
  simp only [CollatzResearch.WordTrace]
  refine ⟨53406132040225456397498249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35604088026816970931665499 53406132040225456397498249)
  ·
    refine ⟨40054599030169092298123687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53406132040225456397498249 40054599030169092298123687)
    ·
      refine ⟨60081898545253638447185531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40054599030169092298123687 60081898545253638447185531)
      ·
        refine ⟨90122847817880457670778297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60081898545253638447185531 90122847817880457670778297)
        ·
          refine ⟨67592135863410343253083723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90122847817880457670778297 67592135863410343253083723)
          ·
            refine ⟨101388203795115514879625585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67592135863410343253083723 101388203795115514879625585)
            ·
              refine ⟨76041152846336636159719189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101388203795115514879625585 76041152846336636159719189)
              ·
                refine ⟨3564429039672029819986837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76041152846336636159719189 3564429039672029819986837)
                ·
                  refine ⟨167082611234626397811883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3564429039672029819986837 167082611234626397811883)
                  ·
                    rfl

theorem cell22_1464265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_1464265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464265 prefixEnd_1464265 := by exact prefixLift 1464265
  have htrace : WordTrace (prefixWord ++ tailWord_1464265) baseStart_1464265 baseEnd_1464265 := by
    simpa [prefixWord, tailWord_1464265, baseEnd_1464265] using wordTrace_append hprefix tailTrace_1464265
  have hstable : (prefixWord ++ tailWord_1464265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464265).length < 2 ^ (prefixWord ++ tailWord_1464265).sum := by decide
  have hdescent : baseEnd_1464265 < baseStart_1464265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464267 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 1, 4]
def baseStart_1464267 : Nat := 118140960795 + 1464267 * 2 ^ 59
def prefixEnd_1464267 : Nat := 4983230072969 + 3 ^ 40 * 1464267 * 2
def baseEnd_1464267 : Nat := 501248518344751854885643

theorem tailTrace_1464267 : CollatzResearch.WordTrace tailWord_1464267 prefixEnd_1464267 501248518344751854885643 := by
  unfold tailWord_1464267
  simp only [CollatzResearch.WordTrace]
  refine ⟨53406204986218210739071055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35604136657478807159380703 53406204986218210739071055)
  ·
    refine ⟨80109307479327316108606583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53406204986218210739071055 80109307479327316108606583)
    ·
      refine ⟨120163961218990974162909875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80109307479327316108606583 120163961218990974162909875)
      ·
        refine ⟨180245941828486461244364813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120163961218990974162909875 180245941828486461244364813)
        ·
          refine ⟨67592228185682422966636805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180245941828486461244364813 67592228185682422966636805)
          ·
            refine ⟨12673542784815454306244401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67592228185682422966636805 12673542784815454306244401)
            ·
              refine ⟨9505157088611590729683301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12673542784815454306244401 9505157088611590729683301)
              ·
                refine ⟨1782216954114673261815619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9505157088611590729683301 1782216954114673261815619)
                ·
                  refine ⟨2673325431172009892723429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782216954114673261815619 2673325431172009892723429)
                  ·
                    refine ⟨501248518344751854885643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2673325431172009892723429 501248518344751854885643)
                    ·
                      rfl

theorem cell22_1464267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 4].length) (baseStart_1464267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464267 prefixEnd_1464267 := by exact prefixLift 1464267
  have htrace : WordTrace (prefixWord ++ tailWord_1464267) baseStart_1464267 baseEnd_1464267 := by
    simpa [prefixWord, tailWord_1464267, baseEnd_1464267] using wordTrace_append hprefix tailTrace_1464267
  have hstable : (prefixWord ++ tailWord_1464267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464267).length < 2 ^ (prefixWord ++ tailWord_1464267).sum := by decide
  have hdescent : baseEnd_1464267 < baseStart_1464267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464326 : List Nat := [6, 2, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1464326 : Nat := 118140960795 + 1464326 * 2 ^ 59
def prefixEnd_1464326 : Nat := 4983230072969 + 3 ^ 40 * 1464326 * 2
def baseEnd_1464326 : Nat := 501268715250495367660463

theorem tailTrace_1464326 : CollatzResearch.WordTrace tailWord_1464326 prefixEnd_1464326 501268715250495367660463 := by
  unfold tailWord_1464326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669011152906389494233401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35605571262002975876979221 1669011152906389494233401)
  ·
    refine ⟨1251758364679792120675051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1669011152906389494233401 1251758364679792120675051)
    ·
      refine ⟨1877637547019688181012577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251758364679792120675051 1877637547019688181012577)
      ·
        refine ⟨1408228160264766135759433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1877637547019688181012577 1408228160264766135759433)
        ·
          refine ⟨1056171120198574601819575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408228160264766135759433 1056171120198574601819575)
          ·
            refine ⟨1584256680297861902729363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056171120198574601819575 1584256680297861902729363)
            ·
              refine ⟨2376385020446792854094045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584256680297861902729363 2376385020446792854094045)
              ·
                refine ⟨891144382667547320285267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2376385020446792854094045 891144382667547320285267)
                ·
                  refine ⟨1336716574001320980427901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891144382667547320285267 1336716574001320980427901)
                  ·
                    refine ⟨501268715250495367660463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336716574001320980427901 501268715250495367660463)
                    ·
                      rfl

theorem cell22_1464326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1464326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464326 prefixEnd_1464326 := by exact prefixLift 1464326
  have htrace : WordTrace (prefixWord ++ tailWord_1464326) baseStart_1464326 baseEnd_1464326 := by
    simpa [prefixWord, tailWord_1464326, baseEnd_1464326] using wordTrace_append hprefix tailTrace_1464326
  have hstable : (prefixWord ++ tailWord_1464326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464326).length < 2 ^ (prefixWord ++ tailWord_1464326).sum := by decide
  have hdescent : baseEnd_1464326 < baseStart_1464326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464327 : List Nat := [1, 1, 4, 3, 1, 3, 1, 8]
def baseStart_1464327 : Nat := 118140960795 + 1464327 * 2 ^ 59
def prefixEnd_1464327 : Nat := 4983230072969 + 3 ^ 40 * 1464327 * 2
def baseEnd_1464327 : Nat := 55696561952325744265051

theorem tailTrace_1464327 : CollatzResearch.WordTrace tailWord_1464327 prefixEnd_1464327 55696561952325744265051 := by
  unfold tailWord_1464327
  simp only [CollatzResearch.WordTrace]
  refine ⟨53408393366000840986255235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35605595577333893990836823 53408393366000840986255235)
  ·
    refine ⟨80112590049001261479382853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53408393366000840986255235 80112590049001261479382853)
    ·
      refine ⟨15021110634187736527384285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80112590049001261479382853 15021110634187736527384285)
      ·
        refine ⟨5632916487820401197769107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15021110634187736527384285 5632916487820401197769107)
        ·
          refine ⟨8449374731730601796653661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5632916487820401197769107 8449374731730601796653661)
          ·
            refine ⟨3168515524398975673745123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8449374731730601796653661 3168515524398975673745123)
            ·
              refine ⟨4752773286598463510617685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168515524398975673745123 4752773286598463510617685)
              ·
                refine ⟨55696561952325744265051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4752773286598463510617685 55696561952325744265051)
                ·
                  rfl

theorem cell22_1464327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 8].length) (baseStart_1464327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464327 prefixEnd_1464327 := by exact prefixLift 1464327
  have htrace : WordTrace (prefixWord ++ tailWord_1464327) baseStart_1464327 baseEnd_1464327 := by
    simpa [prefixWord, tailWord_1464327, baseEnd_1464327] using wordTrace_append hprefix tailTrace_1464327
  have hstable : (prefixWord ++ tailWord_1464327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464327).length < 2 ^ (prefixWord ++ tailWord_1464327).sum := by decide
  have hdescent : baseEnd_1464327 < baseStart_1464327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464417 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 6]
def baseStart_1464417 : Nat := 118140960795 + 1464417 * 2 ^ 59
def prefixEnd_1464417 : Nat := 4983230072969 + 3 ^ 40 * 1464417 * 2
def baseEnd_1464417 : Nat := 167099955470067154545061

theorem tailTrace_1464417 : CollatzResearch.WordTrace tailWord_1464417 prefixEnd_1464417 167099955470067154545061 := by
  unfold tailWord_1464417
  simp only [CollatzResearch.WordTrace]
  refine ⟨53411675935674786357031505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35607783957116524238021003 53411675935674786357031505)
  ·
    refine ⟨40058756951756089767773629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53411675935674786357031505 40058756951756089767773629)
    ·
      refine ⟨15022033856908533662915111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40058756951756089767773629 15022033856908533662915111)
      ·
        refine ⟨22533050785362800494372667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15022033856908533662915111 22533050785362800494372667)
        ·
          refine ⟨33799576178044200741559001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22533050785362800494372667 33799576178044200741559001)
          ·
            refine ⟨25349682133533150556169251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33799576178044200741559001 25349682133533150556169251)
            ·
              refine ⟨38024523200299725834253877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25349682133533150556169251 38024523200299725834253877)
              ·
                refine ⟨3564799050028099296961301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38024523200299725834253877 3564799050028099296961301)
                ·
                  refine ⟨167099955470067154545061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3564799050028099296961301 167099955470067154545061)
                  ·
                    rfl

theorem cell22_1464417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_1464417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464417 prefixEnd_1464417 := by exact prefixLift 1464417
  have htrace : WordTrace (prefixWord ++ tailWord_1464417) baseStart_1464417 baseEnd_1464417 := by
    simpa [prefixWord, tailWord_1464417, baseEnd_1464417] using wordTrace_append hprefix tailTrace_1464417
  have hstable : (prefixWord ++ tailWord_1464417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464417).length < 2 ^ (prefixWord ++ tailWord_1464417).sum := by decide
  have hdescent : baseEnd_1464417 < baseStart_1464417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464434 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1464434 : Nat := 118140960795 + 1464434 * 2 ^ 59
def prefixEnd_1464434 : Nat := 4983230072969 + 3 ^ 40 * 1464434 * 2
def baseEnd_1464434 : Nat := 167101895285873028653377

theorem tailTrace_1464434 : CollatzResearch.WordTrace tailWord_1464434 prefixEnd_1464434 167101895285873028653377 := by
  unfold tailWord_1464434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13353073994153299565100089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35608197317742132173600237 13353073994153299565100089)
  ·
    refine ⟨10014805495614974673825067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13353073994153299565100089 10014805495614974673825067)
    ·
      refine ⟨15022208243422462010737601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10014805495614974673825067 15022208243422462010737601)
      ·
        refine ⟨11266656182566846508053201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15022208243422462010737601 11266656182566846508053201)
        ·
          refine ⟨8449992136925134881039901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11266656182566846508053201 8449992136925134881039901)
          ·
            refine ⟨3168747051346925580389963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8449992136925134881039901 3168747051346925580389963)
            ·
              refine ⟨4753120577020388370584945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3168747051346925580389963 4753120577020388370584945)
              ·
                refine ⟨3564840432765291277938709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4753120577020388370584945 3564840432765291277938709)
                ·
                  refine ⟨167101895285873028653377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3564840432765291277938709 167101895285873028653377)
                  ·
                    rfl

theorem cell22_1464434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1464434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464434 prefixEnd_1464434 := by exact prefixLift 1464434
  have htrace : WordTrace (prefixWord ++ tailWord_1464434) baseStart_1464434 baseEnd_1464434 := by
    simpa [prefixWord, tailWord_1464434, baseEnd_1464434] using wordTrace_append hprefix tailTrace_1464434
  have hstable : (prefixWord ++ tailWord_1464434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464434).length < 2 ^ (prefixWord ++ tailWord_1464434).sum := by decide
  have hdescent : baseEnd_1464434 < baseStart_1464434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464451 : List Nat := [1, 1, 1, 3, 3, 4, 2, 3, 4]
def baseStart_1464451 : Nat := 118140960795 + 1464451 * 2 ^ 59
def prefixEnd_1464451 : Nat := 4983230072969 + 3 ^ 40 * 1464451 * 2
def baseEnd_1464451 : Nat := 167103835101678902761693

theorem tailTrace_1464451 : CollatzResearch.WordTrace tailWord_1464451 prefixEnd_1464451 167103835101678902761693 := by
  unfold tailWord_1464451
  simp only [CollatzResearch.WordTrace]
  refine ⟨53412916017551610163769207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35608610678367740109179471 53412916017551610163769207)
  ·
    refine ⟨80119374026327415245653811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53412916017551610163769207 80119374026327415245653811)
    ·
      refine ⟨120179061039491122868480717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80119374026327415245653811 120179061039491122868480717)
      ·
        refine ⟨45067147889809171075680269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120179061039491122868480717 45067147889809171075680269)
        ·
          refine ⟨16900180458678439153380101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45067147889809171075680269 16900180458678439153380101)
          ·
            refine ⟨3168783836002207341258769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16900180458678439153380101 3168783836002207341258769)
            ·
              refine ⟨2376587877001655505944077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168783836002207341258769 2376587877001655505944077)
              ·
                refine ⟨891220453875620814729029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2376587877001655505944077 891220453875620814729029)
                ·
                  refine ⟨167103835101678902761693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891220453875620814729029 167103835101678902761693)
                  ·
                    rfl

theorem cell22_1464451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 4].length) (baseStart_1464451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464451 prefixEnd_1464451 := by exact prefixLift 1464451
  have htrace : WordTrace (prefixWord ++ tailWord_1464451) baseStart_1464451 baseEnd_1464451 := by
    simpa [prefixWord, tailWord_1464451, baseEnd_1464451] using wordTrace_append hprefix tailTrace_1464451
  have hstable : (prefixWord ++ tailWord_1464451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464451).length < 2 ^ (prefixWord ++ tailWord_1464451).sum := by decide
  have hdescent : baseEnd_1464451 < baseStart_1464451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464453 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_1464453 : Nat := 118140960795 + 1464453 * 2 ^ 59
def prefixEnd_1464453 : Nat := 4983230072969 + 3 ^ 40 * 1464453 * 2
def baseEnd_1464453 : Nat := 501312189945909369735073

theorem tailTrace_1464453 : CollatzResearch.WordTrace tailWord_1464453 prefixEnd_1464453 501312189945909369735073 := by
  unfold tailWord_1464453
  simp only [CollatzResearch.WordTrace]
  refine ⟨53412988963544364505342013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35608659309029576336894675 53412988963544364505342013)
  ·
    refine ⟨20029870861329136689503255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53412988963544364505342013 20029870861329136689503255)
    ·
      refine ⟨30044806291993705034254883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20029870861329136689503255 30044806291993705034254883)
      ·
        refine ⟨45067209437990557551382325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30044806291993705034254883 45067209437990557551382325)
        ·
          refine ⟨4225050884811614770442093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45067209437990557551382325 4225050884811614770442093)
          ·
            refine ⟨1584394081804355538915785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4225050884811614770442093 1584394081804355538915785)
            ·
              refine ⟨1188295561353266654186839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584394081804355538915785 1188295561353266654186839)
              ·
                refine ⟨1782443342029899981280259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188295561353266654186839 1782443342029899981280259)
                ·
                  refine ⟨2673665013044849971920389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782443342029899981280259 2673665013044849971920389)
                  ·
                    refine ⟨501312189945909369735073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2673665013044849971920389 501312189945909369735073)
                    ·
                      rfl

theorem cell22_1464453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_1464453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464453 prefixEnd_1464453 := by exact prefixLift 1464453
  have htrace : WordTrace (prefixWord ++ tailWord_1464453) baseStart_1464453 baseEnd_1464453 := by
    simpa [prefixWord, tailWord_1464453, baseEnd_1464453] using wordTrace_append hprefix tailTrace_1464453
  have hstable : (prefixWord ++ tailWord_1464453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464453).length < 2 ^ (prefixWord ++ tailWord_1464453).sum := by decide
  have hdescent : baseEnd_1464453 < baseStart_1464453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464466 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1464466 : Nat := 118140960795 + 1464466 * 2 ^ 59
def prefixEnd_1464466 : Nat := 4983230072969 + 3 ^ 40 * 1464466 * 2
def baseEnd_1464466 : Nat := 501316640111581669160033

theorem tailTrace_1464466 : CollatzResearch.WordTrace tailWord_1464466 prefixEnd_1464466 501316640111581669160033 := by
  unfold tailWord_1464466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13353365778124316931391313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35608975408331511817043501 13353365778124316931391313)
  ·
    refine ⟨10015024333593237698543485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13353365778124316931391313 10015024333593237698543485)
    ·
      refine ⟨3755634125097464136953807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10015024333593237698543485 3755634125097464136953807)
      ·
        refine ⟨5633451187646196205430711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3755634125097464136953807 5633451187646196205430711)
        ·
          refine ⟨8450176781469294308146067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5633451187646196205430711 8450176781469294308146067)
          ·
            refine ⟨12675265172203941462219101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8450176781469294308146067 12675265172203941462219101)
            ·
              refine ⟨4753224439576478048332163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12675265172203941462219101 4753224439576478048332163)
              ·
                refine ⟨7129836659364717072498245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753224439576478048332163 7129836659364717072498245)
                ·
                  refine ⟨1336844373630884451093421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7129836659364717072498245 1336844373630884451093421)
                  ·
                    refine ⟨501316640111581669160033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1336844373630884451093421 501316640111581669160033)
                    ·
                      rfl

theorem cell22_1464466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1464466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464466 prefixEnd_1464466 := by exact prefixLift 1464466
  have htrace : WordTrace (prefixWord ++ tailWord_1464466) baseStart_1464466 baseEnd_1464466 := by
    simpa [prefixWord, tailWord_1464466, baseEnd_1464466] using wordTrace_append hprefix tailTrace_1464466
  have hstable : (prefixWord ++ tailWord_1464466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464466).length < 2 ^ (prefixWord ++ tailWord_1464466).sum := by decide
  have hdescent : baseEnd_1464466 < baseStart_1464466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464468 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 6]
def baseStart_1464468 : Nat := 118140960795 + 1464468 * 2 ^ 59
def prefixEnd_1464468 : Nat := 4983230072969 + 3 ^ 40 * 1464468 * 2
def baseEnd_1464468 : Nat := 167105774917484776870009

theorem tailTrace_1464468 : CollatzResearch.WordTrace tailWord_1464468 prefixEnd_1464468 167105774917484776870009 := by
  unfold tailWord_1464468
  simp only [CollatzResearch.WordTrace]
  refine ⟨26706768029245011033569029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35609024038993348044758705 26706768029245011033569029)
  ·
    refine ⟨5007519005483439568794193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26706768029245011033569029 5007519005483439568794193)
    ·
      refine ⟨3755639254112579676595645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5007519005483439568794193 3755639254112579676595645)
      ·
        refine ⟨1408364720292217378723367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3755639254112579676595645 1408364720292217378723367)
        ·
          refine ⟨2112547080438326068085051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408364720292217378723367 2112547080438326068085051)
          ·
            refine ⟨3168820620657489102127577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2112547080438326068085051 3168820620657489102127577)
            ·
              refine ⟨2376615465493116826595683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3168820620657489102127577 2376615465493116826595683)
              ·
                refine ⟨3564923198239675239893525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2376615465493116826595683 3564923198239675239893525)
                ·
                  refine ⟨167105774917484776870009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3564923198239675239893525 167105774917484776870009)
                  ·
                    rfl

theorem cell22_1464468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_1464468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464468 prefixEnd_1464468 := by exact prefixLift 1464468
  have htrace : WordTrace (prefixWord ++ tailWord_1464468) baseStart_1464468 baseEnd_1464468 := by
    simpa [prefixWord, tailWord_1464468, baseEnd_1464468] using wordTrace_append hprefix tailTrace_1464468
  have hstable : (prefixWord ++ tailWord_1464468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464468).length < 2 ^ (prefixWord ++ tailWord_1464468).sum := by decide
  have hdescent : baseEnd_1464468 < baseStart_1464468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464492 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1464492 : Nat := 118140960795 + 1464492 * 2 ^ 59
def prefixEnd_1464492 : Nat := 4983230072969 + 3 ^ 40 * 1464492 * 2
def baseEnd_1464492 : Nat := 501325540442926268009953

theorem tailTrace_1464492 : CollatzResearch.WordTrace tailWord_1464492 prefixEnd_1464492 501325540442926268009953 := by
  unfold tailWord_1464492
  simp only [CollatzResearch.WordTrace]
  refine ⟨26707205705201537083005865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35609607606935382777341153 26707205705201537083005865)
  ·
    refine ⟨20030404278901152812254399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26707205705201537083005865 20030404278901152812254399)
    ·
      refine ⟨30045606418351729218381599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20030404278901152812254399 30045606418351729218381599)
      ·
        refine ⟨45068409627527593827572399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30045606418351729218381599 45068409627527593827572399)
        ·
          refine ⟨67602614441291390741358599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45068409627527593827572399 67602614441291390741358599)
          ·
            refine ⟨101403921661937086112037899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67602614441291390741358599 101403921661937086112037899)
            ·
              refine ⟨152105882492905629168056849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101403921661937086112037899 152105882492905629168056849)
              ·
                refine ⟨114079411869679221876042637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152105882492905629168056849 114079411869679221876042637)
                ·
                  refine ⟨42779779451129708203515989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114079411869679221876042637 42779779451129708203515989)
                  ·
                    refine ⟨501325540442926268009953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42779779451129708203515989 501325540442926268009953)
                    ·
                      rfl

theorem cell22_1464492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1464492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464492 prefixEnd_1464492 := by exact prefixLift 1464492
  have htrace : WordTrace (prefixWord ++ tailWord_1464492) baseStart_1464492 baseEnd_1464492 := by
    simpa [prefixWord, tailWord_1464492, baseEnd_1464492] using wordTrace_append hprefix tailTrace_1464492
  have hstable : (prefixWord ++ tailWord_1464492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464492).length < 2 ^ (prefixWord ++ tailWord_1464492).sum := by decide
  have hdescent : baseEnd_1464492 < baseStart_1464492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464507 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 9]
def baseStart_1464507 : Nat := 118140960795 + 1464507 * 2 ^ 59
def prefixEnd_1464507 : Nat := 4983230072969 + 3 ^ 40 * 1464507 * 2
def baseEnd_1464507 : Nat := 167110225083157076294969

theorem tailTrace_1464507 : CollatzResearch.WordTrace tailWord_1464507 prefixEnd_1464507 167110225083157076294969 := by
  unfold tailWord_1464507
  simp only [CollatzResearch.WordTrace]
  refine ⟨53414958505348731727807775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35609972336899154485205183 53414958505348731727807775)
  ·
    refine ⟨80122437758023097591711663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53414958505348731727807775 80122437758023097591711663)
    ·
      refine ⟨120183656637034646387567495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80122437758023097591711663 120183656637034646387567495)
      ·
        refine ⟨180275484955551969581351243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120183656637034646387567495 180275484955551969581351243)
        ·
          refine ⟨270413227433327954372026865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180275484955551969581351243 270413227433327954372026865)
          ·
            refine ⟨202809920574995965779020149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270413227433327954372026865 202809920574995965779020149)
            ·
              refine ⟨19013430053905871791783139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202809920574995965779020149 19013430053905871791783139)
              ·
                refine ⟨28520145080858807687674709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19013430053905871791783139 28520145080858807687674709)
                ·
                  refine ⟨167110225083157076294969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28520145080858807687674709 167110225083157076294969)
                  ·
                    rfl

theorem cell22_1464507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 9].length) (baseStart_1464507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464507 prefixEnd_1464507 := by exact prefixLift 1464507
  have htrace : WordTrace (prefixWord ++ tailWord_1464507) baseStart_1464507 baseEnd_1464507 := by
    simpa [prefixWord, tailWord_1464507, baseEnd_1464507] using wordTrace_append hprefix tailTrace_1464507
  have hstable : (prefixWord ++ tailWord_1464507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464507).length < 2 ^ (prefixWord ++ tailWord_1464507).sum := by decide
  have hdescent : baseEnd_1464507 < baseStart_1464507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464513 : List Nat := [1, 2, 6, 1, 3, 1, 8]
def baseStart_1464513 : Nat := 118140960795 + 1464513 * 2 ^ 59
def prefixEnd_1464513 : Nat := 4983230072969 + 3 ^ 40 * 1464513 * 2
def baseEnd_1464513 : Nat := 18567878858225526416107

theorem tailTrace_1464513 : CollatzResearch.WordTrace tailWord_1464513 prefixEnd_1464513 18567878858225526416107 := by
  unfold tailWord_1464513
  simp only [CollatzResearch.WordTrace]
  refine ⟨53415177343326994752526193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35610118228884663168350795 53415177343326994752526193)
  ·
    refine ⟨40061383007495246064394645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53415177343326994752526193 40061383007495246064394645)
    ·
      refine ⟨1877877328476339659268499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40061383007495246064394645 1877877328476339659268499)
      ·
        refine ⟨2816815992714509488902749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877877328476339659268499 2816815992714509488902749)
        ·
          refine ⟨1056305997267941058338531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2816815992714509488902749 1056305997267941058338531)
          ·
            refine ⟨1584458995901911587507797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056305997267941058338531 1584458995901911587507797)
            ·
              refine ⟨18567878858225526416107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1584458995901911587507797 18567878858225526416107)
              ·
                rfl

theorem cell22_1464513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 8].length) (baseStart_1464513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464513 prefixEnd_1464513 := by exact prefixLift 1464513
  have htrace : WordTrace (prefixWord ++ tailWord_1464513) baseStart_1464513 baseEnd_1464513 := by
    simpa [prefixWord, tailWord_1464513, baseEnd_1464513] using wordTrace_append hprefix tailTrace_1464513
  have hstable : (prefixWord ++ tailWord_1464513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464513).length < 2 ^ (prefixWord ++ tailWord_1464513).sum := by decide
  have hdescent : baseEnd_1464513 < baseStart_1464513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464736 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_1464736 : Nat := 118140960795 + 1464736 * 2 ^ 59
def prefixEnd_1464736 : Nat := 4983230072969 + 3 ^ 40 * 1464736 * 2
def baseEnd_1464736 : Nat := 501409066629390964909205

theorem tailTrace_1464736 : CollatzResearch.WordTrace tailWord_1464736 prefixEnd_1464736 501409066629390964909205 := by
  unfold tailWord_1464736
  simp only [CollatzResearch.WordTrace]
  refine ⟨26711655410759551918947031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35615540547679402558596041 26711655410759551918947031)
  ·
    refine ⟨40067483116139327878420547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26711655410759551918947031 40067483116139327878420547)
    ·
      refine ⟨60101224674208991817630821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40067483116139327878420547 60101224674208991817630821)
      ·
        refine ⟨11268979626414185965805779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60101224674208991817630821 11268979626414185965805779)
        ·
          refine ⟨16903469439621278948708669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11268979626414185965805779 16903469439621278948708669)
          ·
            refine ⟨6338801039857979605765751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16903469439621278948708669 6338801039857979605765751)
            ·
              refine ⟨9508201559786969408648627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6338801039857979605765751 9508201559786969408648627)
              ·
                refine ⟨14262302339680454112972941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9508201559786969408648627 14262302339680454112972941)
                ·
                  refine ⟨5348363377380170292364853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14262302339680454112972941 5348363377380170292364853)
                  ·
                    refine ⟨501409066629390964909205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5348363377380170292364853 501409066629390964909205)
                    ·
                      rfl

theorem cell22_1464736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_1464736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464736 prefixEnd_1464736 := by exact prefixLift 1464736
  have htrace : WordTrace (prefixWord ++ tailWord_1464736) baseStart_1464736 baseEnd_1464736 := by
    simpa [prefixWord, tailWord_1464736, baseEnd_1464736] using wordTrace_append hprefix tailTrace_1464736
  have hstable : (prefixWord ++ tailWord_1464736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464736).length < 2 ^ (prefixWord ++ tailWord_1464736).sum := by decide
  have hdescent : baseEnd_1464736 < baseStart_1464736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464811 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 7]
def baseStart_1464811 : Nat := 118140960795 + 1464811 * 2 ^ 59
def prefixEnd_1464811 : Nat := 4983230072969 + 3 ^ 40 * 1464811 * 2
def baseEnd_1464811 : Nat := 167144913554038589761325

theorem tailTrace_1464811 : CollatzResearch.WordTrace tailWord_1464811 prefixEnd_1464811 167144913554038589761325 := by
  unfold tailWord_1464811
  simp only [CollatzResearch.WordTrace]
  refine ⟨53426046296247391646874287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35617364197498261097916191 53426046296247391646874287)
  ·
    refine ⟨80139069444371087470311431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53426046296247391646874287 80139069444371087470311431)
    ·
      refine ⟨120208604166556631205467147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80139069444371087470311431 120208604166556631205467147)
      ·
        refine ⟨180312906249834946808200721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120208604166556631205467147 180312906249834946808200721)
        ·
          refine ⟨135234679687376210106150541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180312906249834946808200721 135234679687376210106150541)
          ·
            refine ⟨50713004882766078789806453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135234679687376210106150541 50713004882766078789806453)
            ·
              refine ⟨4754344207759319886544355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50713004882766078789806453 4754344207759319886544355)
              ·
                refine ⟨7131516311638979829816533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4754344207759319886544355 7131516311638979829816533)
                ·
                  refine ⟨167144913554038589761325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7131516311638979829816533 167144913554038589761325)
                  ·
                    rfl

theorem cell22_1464811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 7].length) (baseStart_1464811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464811 prefixEnd_1464811 := by exact prefixLift 1464811
  have htrace : WordTrace (prefixWord ++ tailWord_1464811) baseStart_1464811 baseEnd_1464811 := by
    simpa [prefixWord, tailWord_1464811, baseEnd_1464811] using wordTrace_append hprefix tailTrace_1464811
  have hstable : (prefixWord ++ tailWord_1464811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464811).length < 2 ^ (prefixWord ++ tailWord_1464811).sum := by decide
  have hdescent : baseEnd_1464811 < baseStart_1464811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464826 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1464826 : Nat := 118140960795 + 1464826 * 2 ^ 59
def prefixEnd_1464826 : Nat := 4983230072969 + 3 ^ 40 * 1464826 * 2
def baseEnd_1464826 : Nat := 501439875468660730158929

theorem tailTrace_1464826 : CollatzResearch.WordTrace tailWord_1464826 prefixEnd_1464826 501439875468660730158929 := by
  unfold tailWord_1464826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13356648347798262302167583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35617728927462032805780221 13356648347798262302167583)
  ·
    refine ⟨20034972521697393453251375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13356648347798262302167583 20034972521697393453251375)
    ·
      refine ⟨30052458782546090179877063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20034972521697393453251375 30052458782546090179877063)
      ·
        refine ⟨45078688173819135269815595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30052458782546090179877063 45078688173819135269815595)
        ·
          refine ⟨67618032260728702904723393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45078688173819135269815595 67618032260728702904723393)
          ·
            refine ⟨50713524195546527178542545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67618032260728702904723393 50713524195546527178542545)
            ·
              refine ⟨38035143146659895383906909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50713524195546527178542545 38035143146659895383906909)
              ·
                refine ⟨14263178679997460768965091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38035143146659895383906909 14263178679997460768965091)
                ·
                  refine ⟨21394768019996191153447637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14263178679997460768965091 21394768019996191153447637)
                  ·
                    refine ⟨501439875468660730158929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21394768019996191153447637 501439875468660730158929)
                    ·
                      rfl

theorem cell22_1464826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1464826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464826 prefixEnd_1464826 := by exact prefixLift 1464826
  have htrace : WordTrace (prefixWord ++ tailWord_1464826) baseStart_1464826 baseEnd_1464826 := by
    simpa [prefixWord, tailWord_1464826, baseEnd_1464826] using wordTrace_append hprefix tailTrace_1464826
  have hstable : (prefixWord ++ tailWord_1464826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464826).length < 2 ^ (prefixWord ++ tailWord_1464826).sum := by decide
  have hdescent : baseEnd_1464826 < baseStart_1464826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464834 : List Nat := [3, 4, 1, 2, 3, 1, 2, 6]
def baseStart_1464834 : Nat := 118140960795 + 1464834 * 2 ^ 59
def prefixEnd_1464834 : Nat := 4983230072969 + 3 ^ 40 * 1464834 * 2
def baseEnd_1464834 : Nat := 55715846003572375106545

theorem tailTrace_1464834 : CollatzResearch.WordTrace tailWord_1464834 prefixEnd_1464834 55715846003572375106545 := by
  unfold tailWord_1464834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13356721293791016643740389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35617923450109377716641037 13356721293791016643740389)
  ·
    refine ⟨2504385242585815620701323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13356721293791016643740389 2504385242585815620701323)
    ·
      refine ⟨3756577863878723431051985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2504385242585815620701323 3756577863878723431051985)
      ·
        refine ⟨2817433397909042573288989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3756577863878723431051985 2817433397909042573288989)
        ·
          refine ⟨1056537524215890964983371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2817433397909042573288989 1056537524215890964983371)
          ·
            refine ⟨1584806286323836447475057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056537524215890964983371 1584806286323836447475057)
            ·
              refine ⟨1188604714742877335606293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1584806286323836447475057 1188604714742877335606293)
              ·
                refine ⟨55715846003572375106545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1188604714742877335606293 55715846003572375106545)
                ·
                  rfl

theorem cell22_1464834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_1464834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464834 prefixEnd_1464834 := by exact prefixLift 1464834
  have htrace : WordTrace (prefixWord ++ tailWord_1464834) baseStart_1464834 baseEnd_1464834 := by
    simpa [prefixWord, tailWord_1464834, baseEnd_1464834] using wordTrace_append hprefix tailTrace_1464834
  have hstable : (prefixWord ++ tailWord_1464834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464834).length < 2 ^ (prefixWord ++ tailWord_1464834).sum := by decide
  have hdescent : baseEnd_1464834 < baseStart_1464834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464888 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_1464888 : Nat := 118140960795 + 1464888 * 2 ^ 59
def prefixEnd_1464888 : Nat := 4983230072969 + 3 ^ 40 * 1464888 * 2
def baseEnd_1464888 : Nat := 501461099335713235108739

theorem tailTrace_1464888 : CollatzResearch.WordTrace tailWord_1464888 prefixEnd_1464888 501461099335713235108739 := by
  unfold tailWord_1464888
  simp only [CollatzResearch.WordTrace]
  refine ⟨26714427358484216898713659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35619236477978955864951545 26714427358484216898713659)
  ·
    refine ⟨40071641037726325348070489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26714427358484216898713659 40071641037726325348070489)
    ·
      refine ⟨30053730778294744011052867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40071641037726325348070489 30053730778294744011052867)
      ·
        refine ⟨45080596167442116016579301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30053730778294744011052867 45080596167442116016579301)
        ·
          refine ⟨8452611781395396753108619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45080596167442116016579301 8452611781395396753108619)
          ·
            refine ⟨12678917672093095129662929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8452611781395396753108619 12678917672093095129662929)
            ·
              refine ⟨9509188254069821347247197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12678917672093095129662929 9509188254069821347247197)
              ·
                refine ⟨3565945595276183005217699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9509188254069821347247197 3565945595276183005217699)
                ·
                  refine ⟨5348918392914274507826549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3565945595276183005217699 5348918392914274507826549)
                  ·
                    refine ⟨501461099335713235108739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5348918392914274507826549 501461099335713235108739)
                    ·
                      rfl

theorem cell22_1464888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_1464888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464888 prefixEnd_1464888 := by exact prefixLift 1464888
  have htrace : WordTrace (prefixWord ++ tailWord_1464888) baseStart_1464888 baseEnd_1464888 := by
    simpa [prefixWord, tailWord_1464888, baseEnd_1464888] using wordTrace_append hprefix tailTrace_1464888
  have hstable : (prefixWord ++ tailWord_1464888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464888).length < 2 ^ (prefixWord ++ tailWord_1464888).sum := by decide
  have hdescent : baseEnd_1464888 < baseStart_1464888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464892 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_1464892 : Nat := 118140960795 + 1464892 * 2 ^ 59
def prefixEnd_1464892 : Nat := 4983230072969 + 3 ^ 40 * 1464892 * 2
def baseEnd_1464892 : Nat := 501462468617458558008727

theorem tailTrace_1464892 : CollatzResearch.WordTrace tailWord_1464892 prefixEnd_1464892 501462468617458558008727 := by
  unfold tailWord_1464892
  simp only [CollatzResearch.WordTrace]
  refine ⟨26714500304476971240286465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35619333739302628320381953 26714500304476971240286465)
  ·
    refine ⟨20035875228357728430214849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26714500304476971240286465 20035875228357728430214849)
    ·
      refine ⟨15026906421268296322661137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20035875228357728430214849 15026906421268296322661137)
      ·
        refine ⟨11270179815951222241995853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15026906421268296322661137 11270179815951222241995853)
        ·
          refine ⟨4226317430981708340748445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11270179815951222241995853 4226317430981708340748445)
          ·
            refine ⟨1584869036618140627780667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4226317430981708340748445 1584869036618140627780667)
            ·
              refine ⟨2377303554927210941671001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584869036618140627780667 2377303554927210941671001)
              ·
                refine ⟨1782977666195408206253251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2377303554927210941671001 1782977666195408206253251)
                ·
                  refine ⟨2674466499293112309379877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782977666195408206253251 2674466499293112309379877)
                  ·
                    refine ⟨501462468617458558008727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674466499293112309379877 501462468617458558008727)
                    ·
                      rfl

theorem cell22_1464892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_1464892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464892 prefixEnd_1464892 := by exact prefixLift 1464892
  have htrace : WordTrace (prefixWord ++ tailWord_1464892) baseStart_1464892 baseEnd_1464892 := by
    simpa [prefixWord, tailWord_1464892, baseEnd_1464892] using wordTrace_append hprefix tailTrace_1464892
  have hstable : (prefixWord ++ tailWord_1464892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464892).length < 2 ^ (prefixWord ++ tailWord_1464892).sum := by decide
  have hdescent : baseEnd_1464892 < baseStart_1464892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1464909 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1464909 : Nat := 118140960795 + 1464909 * 2 ^ 59
def prefixEnd_1464909 : Nat := 4983230072969 + 3 ^ 40 * 1464909 * 2
def baseEnd_1464909 : Nat := 501468288064876180333675

theorem tailTrace_1464909 : CollatzResearch.WordTrace tailWord_1464909 prefixEnd_1464909 501468288064876180333675 := by
  unfold tailWord_1464909
  simp only [CollatzResearch.WordTrace]
  refine ⟨53429620649892354383941781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35619747099928236255961187 53429620649892354383941781)
  ·
    refine ⟨2504513467963704111747271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53429620649892354383941781 2504513467963704111747271)
    ·
      refine ⟨3756770201945556167620907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2504513467963704111747271 3756770201945556167620907)
      ·
        refine ⟨5635155302918334251431361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3756770201945556167620907 5635155302918334251431361)
        ·
          refine ⟨4226366477188750688573521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5635155302918334251431361 4226366477188750688573521)
          ·
            refine ⟨3169774857891563016430141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4226366477188750688573521 3169774857891563016430141)
            ·
              refine ⟨1188665571709336131161303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3169774857891563016430141 1188665571709336131161303)
              ·
                refine ⟨1782998357564004196741955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188665571709336131161303 1782998357564004196741955)
                ·
                  refine ⟨2674497536346006295112933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782998357564004196741955 2674497536346006295112933)
                  ·
                    refine ⟨501468288064876180333675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2674497536346006295112933 501468288064876180333675)
                    ·
                      rfl

theorem cell22_1464909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1464909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1464909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1464909 prefixEnd_1464909 := by exact prefixLift 1464909
  have htrace : WordTrace (prefixWord ++ tailWord_1464909) baseStart_1464909 baseEnd_1464909 := by
    simpa [prefixWord, tailWord_1464909, baseEnd_1464909] using wordTrace_append hprefix tailTrace_1464909
  have hstable : (prefixWord ++ tailWord_1464909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1464909).length < 2 ^ (prefixWord ++ tailWord_1464909).sum := by decide
  have hdescent : baseEnd_1464909 < baseStart_1464909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1464909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465070 : List Nat := [4, 1, 2, 1, 1, 3, 2, 8]
def baseStart_1465070 : Nat := 118140960795 + 1465070 * 2 ^ 59
def prefixEnd_1465070 : Nat := 4983230072969 + 3 ^ 40 * 1465070 * 2
def baseEnd_1465070 : Nat := 55724822406125047450909

theorem tailTrace_1465070 : CollatzResearch.WordTrace tailWord_1465070 prefixEnd_1465070 55724822406125047450909 := by
  unfold tailWord_1465070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679436600288634860069083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35623661868206052587035109 6679436600288634860069083)
  ·
    refine ⟨10019154900432952290103625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6679436600288634860069083 10019154900432952290103625)
    ·
      refine ⟨7514366175324714217577719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10019154900432952290103625 7514366175324714217577719)
      ·
        refine ⟨11271549262987071326366579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7514366175324714217577719 11271549262987071326366579)
        ·
          refine ⟨16907323894480606989549869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11271549262987071326366579 16907323894480606989549869)
          ·
            refine ⟨6340246460430227621081201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16907323894480606989549869 6340246460430227621081201)
            ·
              refine ⟨4755184845322670715810901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340246460430227621081201 4755184845322670715810901)
              ·
                refine ⟨55724822406125047450909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4755184845322670715810901 55724822406125047450909)
                ·
                  rfl

theorem cell22_1465070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_1465070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465070 prefixEnd_1465070 := by exact prefixLift 1465070
  have htrace : WordTrace (prefixWord ++ tailWord_1465070) baseStart_1465070 baseEnd_1465070 := by
    simpa [prefixWord, tailWord_1465070, baseEnd_1465070] using wordTrace_append hprefix tailTrace_1465070
  have hstable : (prefixWord ++ tailWord_1465070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465070).length < 2 ^ (prefixWord ++ tailWord_1465070).sum := by decide
  have hdescent : baseEnd_1465070 < baseStart_1465070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465102 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1465102 : Nat := 118140960795 + 1465102 * 2 ^ 59
def prefixEnd_1465102 : Nat := 4983230072969 + 3 ^ 40 * 1465102 * 2
def baseEnd_1465102 : Nat := 501534355909088010258083

theorem tailTrace_1465102 : CollatzResearch.WordTrace tailWord_1465102 prefixEnd_1465102 501534355909088010258083 := by
  unfold tailWord_1465102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679582492274143543214695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35624439958795432230478373 6679582492274143543214695)
  ·
    refine ⟨10019373738411215314822043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6679582492274143543214695 10019373738411215314822043)
    ·
      refine ⟨15029060607616822972233065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10019373738411215314822043 15029060607616822972233065)
      ·
        refine ⟨11271795455712617229174799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15029060607616822972233065 11271795455712617229174799)
        ·
          refine ⟨16907693183568925843762199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11271795455712617229174799 16907693183568925843762199)
          ·
            refine ⟨25361539775353388765643299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16907693183568925843762199 25361539775353388765643299)
            ·
              refine ⟨38042309663030083148464949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25361539775353388765643299 38042309663030083148464949)
              ·
                refine ⟨3566466530909070295168589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38042309663030083148464949 3566466530909070295168589)
                ·
                  refine ⟨1337424949090901360688221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3566466530909070295168589 1337424949090901360688221)
                  ·
                    refine ⟨501534355909088010258083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1337424949090901360688221 501534355909088010258083)
                    ·
                      rfl

theorem cell22_1465102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1465102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465102 prefixEnd_1465102 := by exact prefixLift 1465102
  have htrace : WordTrace (prefixWord ++ tailWord_1465102) baseStart_1465102 baseEnd_1465102 := by
    simpa [prefixWord, tailWord_1465102, baseEnd_1465102] using wordTrace_append hprefix tailTrace_1465102
  have hstable : (prefixWord ++ tailWord_1465102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465102).length < 2 ^ (prefixWord ++ tailWord_1465102).sum := by decide
  have hdescent : baseEnd_1465102 < baseStart_1465102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465226 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_1465226 : Nat := 118140960795 + 1465226 * 2 ^ 59
def prefixEnd_1465226 : Nat := 4983230072969 + 3 ^ 40 * 1465226 * 2
def baseEnd_1465226 : Nat := 501576803643193020157703

theorem tailTrace_1465226 : CollatzResearch.WordTrace tailWord_1465226 prefixEnd_1465226 501576803643193020157703 := by
  unfold tailWord_1465226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360295647435979380807883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35627455059829278348821021 13360295647435979380807883)
  ·
    refine ⟨20040443471153969071211825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13360295647435979380807883 20040443471153969071211825)
    ·
      refine ⟨15030332603365476803408869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20040443471153969071211825 15030332603365476803408869)
      ·
        refine ⟨2818187363131026900639163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15030332603365476803408869 2818187363131026900639163)
        ·
          refine ⟨4227281044696540350958745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818187363131026900639163 4227281044696540350958745)
          ·
            refine ⟨3170460783522405263219059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4227281044696540350958745 3170460783522405263219059)
            ·
              refine ⟨4755691175283607894828589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3170460783522405263219059 4755691175283607894828589)
              ·
                refine ⟨1783384190731352960560721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4755691175283607894828589 1783384190731352960560721)
                ·
                  refine ⟨1337538143048514720420541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1783384190731352960560721 1337538143048514720420541)
                  ·
                    refine ⟨501576803643193020157703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1337538143048514720420541 501576803643193020157703)
                    ·
                      rfl

theorem cell22_1465226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_1465226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465226 prefixEnd_1465226 := by exact prefixLift 1465226
  have htrace : WordTrace (prefixWord ++ tailWord_1465226) baseStart_1465226 baseEnd_1465226 := by
    simpa [prefixWord, tailWord_1465226, baseEnd_1465226] using wordTrace_append hprefix tailTrace_1465226
  have hstable : (prefixWord ++ tailWord_1465226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465226).length < 2 ^ (prefixWord ++ tailWord_1465226).sum := by decide
  have hdescent : baseEnd_1465226 < baseStart_1465226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465235 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 4, 6]
def baseStart_1465235 : Nat := 118140960795 + 1465235 * 2 ^ 59
def prefixEnd_1465235 : Nat := 4983230072969 + 3 ^ 40 * 1465235 * 2
def baseEnd_1465235 : Nat := 501579884527119996682675

theorem tailTrace_1465235 : CollatzResearch.WordTrace tailWord_1465235 prefixEnd_1465235 501579884527119996682675 := by
  unfold tailWord_1465235
  simp only [CollatzResearch.WordTrace]
  refine ⟨53441510846711312060309159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35627673897807541373539439 53441510846711312060309159)
  ·
    refine ⟨80162266270066968090463739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53441510846711312060309159 80162266270066968090463739)
    ·
      refine ⟨120243399405100452135695609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80162266270066968090463739 120243399405100452135695609)
      ·
        refine ⟨90182549553825339101771707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120243399405100452135695609 90182549553825339101771707)
        ·
          refine ⟨135273824330738008652657561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90182549553825339101771707 135273824330738008652657561)
          ·
            refine ⟨101455368248053506489493171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135273824330738008652657561 101455368248053506489493171)
            ·
              refine ⟨152183052372080259734239757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101455368248053506489493171 152183052372080259734239757)
              ·
                refine ⟨57068644639530097400339909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152183052372080259734239757 57068644639530097400339909)
                ·
                  refine ⟨10700370869911893262563733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57068644639530097400339909 10700370869911893262563733)
                  ·
                    refine ⟨501579884527119996682675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10700370869911893262563733 501579884527119996682675)
                    ·
                      rfl

theorem cell22_1465235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_1465235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465235 prefixEnd_1465235 := by exact prefixLift 1465235
  have htrace : WordTrace (prefixWord ++ tailWord_1465235) baseStart_1465235 baseEnd_1465235 := by
    simpa [prefixWord, tailWord_1465235, baseEnd_1465235] using wordTrace_append hprefix tailTrace_1465235
  have hstable : (prefixWord ++ tailWord_1465235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465235).length < 2 ^ (prefixWord ++ tailWord_1465235).sum := by decide
  have hdescent : baseEnd_1465235 < baseStart_1465235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465297 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_1465297 : Nat := 118140960795 + 1465297 * 2 ^ 59
def prefixEnd_1465297 : Nat := 4983230072969 + 3 ^ 40 * 1465297 * 2
def baseEnd_1465297 : Nat := 501601108394172501632485

theorem tailTrace_1465297 : CollatzResearch.WordTrace tailWord_1465297 prefixEnd_1465297 501601108394172501632485 := by
  unfold tailWord_1465297
  simp only [CollatzResearch.WordTrace]
  refine ⟨53443772172486696649066145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35629181448324464432710763 53443772172486696649066145)
  ·
    refine ⟨40082829129365022486799609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53443772172486696649066145 40082829129365022486799609)
    ·
      refine ⟨30062121847023766865099707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40082829129365022486799609 30062121847023766865099707)
      ·
        refine ⟨45093182770535650297649561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30062121847023766865099707 45093182770535650297649561)
        ·
          refine ⟨33819887077901737723237171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45093182770535650297649561 33819887077901737723237171)
          ·
            refine ⟨50729830616852606584855757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33819887077901737723237171 50729830616852606584855757)
            ·
              refine ⟨19023686481319727469320909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50729830616852606584855757 19023686481319727469320909)
              ·
                refine ⟨7133882430494897800995341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19023686481319727469320909 7133882430494897800995341)
                ·
                  refine ⟨2675205911435586675373253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7133882430494897800995341 2675205911435586675373253)
                  ·
                    refine ⟨501601108394172501632485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675205911435586675373253 501601108394172501632485)
                    ·
                      rfl

theorem cell22_1465297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_1465297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465297 prefixEnd_1465297 := by exact prefixLift 1465297
  have htrace : WordTrace (prefixWord ++ tailWord_1465297) baseStart_1465297 baseEnd_1465297 := by
    simpa [prefixWord, tailWord_1465297, baseEnd_1465297] using wordTrace_append hprefix tailTrace_1465297
  have hstable : (prefixWord ++ tailWord_1465297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465297).length < 2 ^ (prefixWord ++ tailWord_1465297).sum := by decide
  have hdescent : baseEnd_1465297 < baseStart_1465297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465329 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 6]
def baseStart_1465329 : Nat := 118140960795 + 1465329 * 2 ^ 59
def prefixEnd_1465329 : Nat := 4983230072969 + 3 ^ 40 * 1465329 * 2
def baseEnd_1465329 : Nat := 167204020882711694944129

theorem tailTrace_1465329 : CollatzResearch.WordTrace tailWord_1465329 prefixEnd_1465329 167204020882711694944129 := by
  unfold tailWord_1465329
  simp only [CollatzResearch.WordTrace]
  refine ⟨53444939308370766114231041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35629959538913844076154027 53444939308370766114231041)
  ·
    refine ⟨40083704481278074585673281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53444939308370766114231041 40083704481278074585673281)
    ·
      refine ⟨30062778360958555939254961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40083704481278074585673281 30062778360958555939254961)
      ·
        refine ⟨22547083770718916954441221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30062778360958555939254961 22547083770718916954441221)
        ·
          refine ⟨4227578207009796928957729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22547083770718916954441221 4227578207009796928957729)
          ·
            refine ⟨3170683655257347696718297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4227578207009796928957729 3170683655257347696718297)
            ·
              refine ⟨2378012741443010772538723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3170683655257347696718297 2378012741443010772538723)
              ·
                refine ⟨3567019112164516158808085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2378012741443010772538723 3567019112164516158808085)
                ·
                  refine ⟨167204020882711694944129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3567019112164516158808085 167204020882711694944129)
                  ·
                    rfl

theorem cell22_1465329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_1465329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465329 prefixEnd_1465329 := by exact prefixLift 1465329
  have htrace : WordTrace (prefixWord ++ tailWord_1465329) baseStart_1465329 baseEnd_1465329 := by
    simpa [prefixWord, tailWord_1465329, baseEnd_1465329] using wordTrace_append hprefix tailTrace_1465329
  have hstable : (prefixWord ++ tailWord_1465329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465329).length < 2 ^ (prefixWord ++ tailWord_1465329).sum := by decide
  have hdescent : baseEnd_1465329 < baseStart_1465329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465387 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 2, 6]
def baseStart_1465387 : Nat := 118140960795 + 1465387 * 2 ^ 59
def prefixEnd_1465387 : Nat := 4983230072969 + 3 ^ 40 * 1465387 * 2
def baseEnd_1465387 : Nat := 501631917233442266882209

theorem tailTrace_1465387 : CollatzResearch.WordTrace tailWord_1465387 prefixEnd_1465387 501631917233442266882209 := by
  unfold tailWord_1465387
  simp only [CollatzResearch.WordTrace]
  refine ⟨53447054742160642019842415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35631369828107094679894943 53447054742160642019842415)
  ·
    refine ⟨80170582113240963029763623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53447054742160642019842415 80170582113240963029763623)
    ·
      refine ⟨120255873169861444544645435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80170582113240963029763623 120255873169861444544645435)
      ·
        refine ⟨180383809754792166816968153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120255873169861444544645435 180383809754792166816968153)
        ·
          refine ⟨135287857316094125112726115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180383809754792166816968153 135287857316094125112726115)
          ·
            refine ⟨202931785974141187669089173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135287857316094125112726115 202931785974141187669089173)
            ·
              refine ⟨9512427467537868171988555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202931785974141187669089173 9512427467537868171988555)
              ·
                refine ⟨14268641201306802257982833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9512427467537868171988555 14268641201306802257982833)
                ·
                  refine ⟨10701480900980101693487125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14268641201306802257982833 10701480900980101693487125)
                  ·
                    refine ⟨501631917233442266882209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10701480900980101693487125 501631917233442266882209)
                    ·
                      rfl

theorem cell22_1465387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_1465387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465387 prefixEnd_1465387 := by exact prefixLift 1465387
  have htrace : WordTrace (prefixWord ++ tailWord_1465387) baseStart_1465387 baseEnd_1465387 := by
    simpa [prefixWord, tailWord_1465387, baseEnd_1465387] using wordTrace_append hprefix tailTrace_1465387
  have hstable : (prefixWord ++ tailWord_1465387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465387).length < 2 ^ (prefixWord ++ tailWord_1465387).sum := by decide
  have hdescent : baseEnd_1465387 < baseStart_1465387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465417 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_1465417 : Nat := 118140960795 + 1465417 * 2 ^ 59
def prefixEnd_1465417 : Nat := 4983230072969 + 3 ^ 40 * 1465417 * 2
def baseEnd_1465417 : Nat := 501642186846532188632117

theorem tailTrace_1465417 : CollatzResearch.WordTrace tailWord_1465417 prefixEnd_1465417 501642186846532188632117 := by
  unfold tailWord_1465417
  simp only [CollatzResearch.WordTrace]
  refine ⟨53448148932051957143434505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35632099288034638095623003 53448148932051957143434505)
  ·
    refine ⟨40086111699038967857575879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53448148932051957143434505 40086111699038967857575879)
    ·
      refine ⟨60129167548558451786363819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40086111699038967857575879 60129167548558451786363819)
      ·
        refine ⟨90193751322837677679545729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60129167548558451786363819 90193751322837677679545729)
        ·
          refine ⟨67645313492128258259659297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90193751322837677679545729 67645313492128258259659297)
          ·
            refine ⟨50733985119096193694744473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67645313492128258259659297 50733985119096193694744473)
            ·
              refine ⟨38050488839322145271058355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50733985119096193694744473 38050488839322145271058355)
              ·
                refine ⟨57075733258983217906587533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38050488839322145271058355 57075733258983217906587533)
                ·
                  refine ⟨21403399972118706714970325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57075733258983217906587533 21403399972118706714970325)
                  ·
                    refine ⟨501642186846532188632117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21403399972118706714970325 501642186846532188632117)
                    ·
                      rfl

theorem cell22_1465417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_1465417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465417 prefixEnd_1465417 := by exact prefixLift 1465417
  have htrace : WordTrace (prefixWord ++ tailWord_1465417) baseStart_1465417 baseEnd_1465417 := by
    simpa [prefixWord, tailWord_1465417, baseEnd_1465417] using wordTrace_append hprefix tailTrace_1465417
  have hstable : (prefixWord ++ tailWord_1465417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465417).length < 2 ^ (prefixWord ++ tailWord_1465417).sum := by decide
  have hdescent : baseEnd_1465417 < baseStart_1465417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465436 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 5]
def baseStart_1465436 : Nat := 118140960795 + 1465436 * 2 ^ 59
def prefixEnd_1465436 : Nat := 4983230072969 + 3 ^ 40 * 1465436 * 2
def baseEnd_1465436 : Nat := 167216230311607490802353

theorem tailTrace_1465436 : CollatzResearch.WordTrace tailWord_1465436 prefixEnd_1465436 167216230311607490802353 := by
  unfold tailWord_1465436
  simp only [CollatzResearch.WordTrace]
  refine ⟨26724420959491561694188081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35632561279322082258917441 26724420959491561694188081)
  ·
    refine ⟨20043315719618671270641061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26724420959491561694188081 20043315719618671270641061)
    ·
      refine ⟨3758121697428500863245199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20043315719618671270641061 3758121697428500863245199)
      ·
        refine ⟨5637182546142751294867799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758121697428500863245199 5637182546142751294867799)
        ·
          refine ⟨8455773819214126942301699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5637182546142751294867799 8455773819214126942301699)
          ·
            refine ⟨12683660728821190413452549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8455773819214126942301699 12683660728821190413452549)
            ·
              refine ⟨2378186386653973202522353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12683660728821190413452549 2378186386653973202522353)
              ·
                refine ⟨1783639789990479901891765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378186386653973202522353 1783639789990479901891765)
                ·
                  refine ⟨167216230311607490802353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1783639789990479901891765 167216230311607490802353)
                  ·
                    rfl

theorem cell22_1465436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_1465436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465436 prefixEnd_1465436 := by exact prefixLift 1465436
  have htrace : WordTrace (prefixWord ++ tailWord_1465436) baseStart_1465436 baseEnd_1465436 := by
    simpa [prefixWord, tailWord_1465436, baseEnd_1465436] using wordTrace_append hprefix tailTrace_1465436
  have hstable : (prefixWord ++ tailWord_1465436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465436).length < 2 ^ (prefixWord ++ tailWord_1465436).sum := by decide
  have hdescent : baseEnd_1465436 < baseStart_1465436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465438 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1465438 : Nat := 118140960795 + 1465438 * 2 ^ 59
def prefixEnd_1465438 : Nat := 4983230072969 + 3 ^ 40 * 1465438 * 2
def baseEnd_1465438 : Nat := 501649375575695133857053

theorem tailTrace_1465438 : CollatzResearch.WordTrace tailWord_1465438 prefixEnd_1465438 501649375575695133857053 := by
  unfold tailWord_1465438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6681114358121984716243621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35632609909983918486632645 6681114358121984716243621)
  ·
    refine ⟨1252708942147872134295679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6681114358121984716243621 1252708942147872134295679)
    ·
      refine ⟨1879063413221808201443519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252708942147872134295679 1879063413221808201443519)
      ·
        refine ⟨2818595119832712302165279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879063413221808201443519 2818595119832712302165279)
        ·
          refine ⟨4227892679749068453247919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818595119832712302165279 4227892679749068453247919)
          ·
            refine ⟨6341839019623602679871879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227892679749068453247919 6341839019623602679871879)
            ·
              refine ⟨9512758529435404019807819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341839019623602679871879 9512758529435404019807819)
              ·
                refine ⟨14269137794153106029711729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9512758529435404019807819 14269137794153106029711729)
                ·
                  refine ⟨10701853345614829522283797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14269137794153106029711729 10701853345614829522283797)
                  ·
                    refine ⟨501649375575695133857053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10701853345614829522283797 501649375575695133857053)
                    ·
                      rfl

theorem cell22_1465438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1465438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465438 prefixEnd_1465438 := by exact prefixLift 1465438
  have htrace : WordTrace (prefixWord ++ tailWord_1465438) baseStart_1465438 baseEnd_1465438 := by
    simpa [prefixWord, tailWord_1465438, baseEnd_1465438] using wordTrace_append hprefix tailTrace_1465438
  have hstable : (prefixWord ++ tailWord_1465438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465438).length < 2 ^ (prefixWord ++ tailWord_1465438).sum := by decide
  have hdescent : baseEnd_1465438 < baseStart_1465438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465449 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_1465449 : Nat := 118140960795 + 1465449 * 2 ^ 59
def prefixEnd_1465449 : Nat := 4983230072969 + 3 ^ 40 * 1465449 * 2
def baseEnd_1465449 : Nat := 501653141100494771832019

theorem tailTrace_1465449 : CollatzResearch.WordTrace tailWord_1465449 prefixEnd_1465449 501653141100494771832019 := by
  unfold tailWord_1465449
  simp only [CollatzResearch.WordTrace]
  refine ⟨53449316067936026608599401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35632877378624017739066267 53449316067936026608599401)
  ·
    refine ⟨40086987050952019956449551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53449316067936026608599401 40086987050952019956449551)
    ·
      refine ⟨60130480576428029934674327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40086987050952019956449551 60130480576428029934674327)
      ·
        refine ⟨90195720864642044902011491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60130480576428029934674327 90195720864642044902011491)
        ·
          refine ⟨135293581296963067353017237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90195720864642044902011491 135293581296963067353017237)
          ·
            refine ⟨6341886623295143782172683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135293581296963067353017237 6341886623295143782172683)
            ·
              refine ⟨9512829934942715673259025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341886623295143782172683 9512829934942715673259025)
              ·
                refine ⟨7134622451207036754944269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9512829934942715673259025 7134622451207036754944269)
                ·
                  refine ⟨2675483419202638783104101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7134622451207036754944269 2675483419202638783104101)
                  ·
                    refine ⟨501653141100494771832019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675483419202638783104101 501653141100494771832019)
                    ·
                      rfl

theorem cell22_1465449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_1465449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465449 prefixEnd_1465449 := by exact prefixLift 1465449
  have htrace : WordTrace (prefixWord ++ tailWord_1465449) baseStart_1465449 baseEnd_1465449 := by
    simpa [prefixWord, tailWord_1465449, baseEnd_1465449] using wordTrace_append hprefix tailTrace_1465449
  have hstable : (prefixWord ++ tailWord_1465449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465449).length < 2 ^ (prefixWord ++ tailWord_1465449).sum := by decide
  have hdescent : baseEnd_1465449 < baseStart_1465449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465481 : List Nat := [1, 2, 1, 1, 4, 3, 1, 5, 4]
def baseStart_1465481 : Nat := 118140960795 + 1465481 * 2 ^ 59
def prefixEnd_1465481 : Nat := 4983230072969 + 3 ^ 40 * 1465481 * 2
def baseEnd_1465481 : Nat := 167221365118152451677307

theorem tailTrace_1465481 : CollatzResearch.WordTrace tailWord_1465481 prefixEnd_1465481 167221365118152451677307 := by
  unfold tailWord_1465481
  simp only [CollatzResearch.WordTrace]
  refine ⟨53450483203820096073764297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35633655469213397382509531 53450483203820096073764297)
  ·
    refine ⟨40087862402865072055323223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53450483203820096073764297 40087862402865072055323223)
    ·
      refine ⟨60131793604297608082984835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40087862402865072055323223 60131793604297608082984835)
      ·
        refine ⟨90197690406446412124477253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60131793604297608082984835 90197690406446412124477253)
        ·
          refine ⟨16912066951208702273339485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90197690406446412124477253 16912066951208702273339485)
          ·
            refine ⟨6342025106703263352502307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16912066951208702273339485 6342025106703263352502307)
            ·
              refine ⟨9513037660054895028753461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342025106703263352502307 9513037660054895028753461)
              ·
                refine ⟨891847280630146408945637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9513037660054895028753461 891847280630146408945637)
                ·
                  refine ⟨167221365118152451677307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891847280630146408945637 167221365118152451677307)
                  ·
                    rfl

theorem cell22_1465481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 4].length) (baseStart_1465481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465481 prefixEnd_1465481 := by exact prefixLift 1465481
  have htrace : WordTrace (prefixWord ++ tailWord_1465481) baseStart_1465481 baseEnd_1465481 := by
    simpa [prefixWord, tailWord_1465481, baseEnd_1465481] using wordTrace_append hprefix tailTrace_1465481
  have hstable : (prefixWord ++ tailWord_1465481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465481).length < 2 ^ (prefixWord ++ tailWord_1465481).sum := by decide
  have hdescent : baseEnd_1465481 < baseStart_1465481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465498 : List Nat := [3, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_1465498 : Nat := 118140960795 + 1465498 * 2 ^ 59
def prefixEnd_1465498 : Nat := 4983230072969 + 3 ^ 40 * 1465498 * 2
def baseEnd_1465498 : Nat := 167223304933958325785623

theorem tailTrace_1465498 : CollatzResearch.WordTrace tailWord_1465498 prefixEnd_1465498 167223304933958325785623 := by
  unfold tailWord_1465498
  simp only [CollatzResearch.WordTrace]
  refine ⟨13362775811189626994283287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35634068829839005318088765 13362775811189626994283287)
  ·
    refine ⟨20044163716784440491424931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13362775811189626994283287 20044163716784440491424931)
    ·
      refine ⟨30066245575176660737137397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20044163716784440491424931 30066245575176660737137397)
      ·
        refine ⟨2818710522672811944106631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30066245575176660737137397 2818710522672811944106631)
        ·
          refine ⟨4228065784009217916159947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818710522672811944106631 4228065784009217916159947)
          ·
            refine ⟨6342098676013826874239921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228065784009217916159947 6342098676013826874239921)
            ·
              refine ⟨4756574007010370155679941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6342098676013826874239921 4756574007010370155679941)
              ·
                refine ⟨891857626314444404189989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4756574007010370155679941 891857626314444404189989)
                ·
                  refine ⟨167223304933958325785623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891857626314444404189989 167223304933958325785623)
                  ·
                    rfl

theorem cell22_1465498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_1465498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465498 prefixEnd_1465498 := by exact prefixLift 1465498
  have htrace : WordTrace (prefixWord ++ tailWord_1465498) baseStart_1465498 baseEnd_1465498 := by
    simpa [prefixWord, tailWord_1465498, baseEnd_1465498] using wordTrace_append hprefix tailTrace_1465498
  have hstable : (prefixWord ++ tailWord_1465498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465498).length < 2 ^ (prefixWord ++ tailWord_1465498).sum := by decide
  have hdescent : baseEnd_1465498 < baseStart_1465498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465511 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1465511 : Nat := 118140960795 + 1465511 * 2 ^ 59
def prefixEnd_1465511 : Nat := 4983230072969 + 3 ^ 40 * 1465511 * 2
def baseEnd_1465511 : Nat := 501674364967547276781829

theorem tailTrace_1465511 : CollatzResearch.WordTrace tailWord_1465511 prefixEnd_1465511 501674364967547276781829 := by
  unfold tailWord_1465511
  simp only [CollatzResearch.WordTrace]
  refine ⟨53451577393711411197356387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35634384929140940798237591 53451577393711411197356387)
  ·
    refine ⟨80177366090567116796034581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53451577393711411197356387 80177366090567116796034581)
    ·
      refine ⟨3758314035495333599814121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80177366090567116796034581 3758314035495333599814121)
      ·
        refine ⟨2818735526621500199860591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3758314035495333599814121 2818735526621500199860591)
        ·
          refine ⟨4228103289932250299790887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818735526621500199860591 4228103289932250299790887)
          ·
            refine ⟨6342154934898375449686331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228103289932250299790887 6342154934898375449686331)
            ·
              refine ⟨9513232402347563174529497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342154934898375449686331 9513232402347563174529497)
              ·
                refine ⟨7134924301760672380897123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9513232402347563174529497 7134924301760672380897123)
                ·
                  refine ⟨10702386452641008571345685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7134924301760672380897123 10702386452641008571345685)
                  ·
                    refine ⟨501674364967547276781829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10702386452641008571345685 501674364967547276781829)
                    ·
                      rfl

theorem cell22_1465511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1465511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465511 prefixEnd_1465511 := by exact prefixLift 1465511
  have htrace : WordTrace (prefixWord ++ tailWord_1465511) baseStart_1465511 baseEnd_1465511 := by
    simpa [prefixWord, tailWord_1465511, baseEnd_1465511] using wordTrace_append hprefix tailTrace_1465511
  have hstable : (prefixWord ++ tailWord_1465511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465511).length < 2 ^ (prefixWord ++ tailWord_1465511).sum := by decide
  have hdescent : baseEnd_1465511 < baseStart_1465511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465549 : List Nat := [1, 6, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1465549 : Nat := 118140960795 + 1465549 * 2 ^ 59
def prefixEnd_1465549 : Nat := 4983230072969 + 3 ^ 40 * 1465549 * 2
def baseEnd_1465549 : Nat := 167229124381375948110571

theorem tailTrace_1465549 : CollatzResearch.WordTrace tailWord_1465549 prefixEnd_1465549 167229124381375948110571 := by
  unfold tailWord_1465549
  simp only [CollatzResearch.WordTrace]
  refine ⟨53452963367573743687239701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35635308911715829124826467 53452963367573743687239701)
  ·
    refine ⟨2505607657855019235339361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53452963367573743687239701 2505607657855019235339361)
    ·
      refine ⟨1879205743391264426504521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2505607657855019235339361 1879205743391264426504521)
      ·
        refine ⟨1409404307543448319878391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1879205743391264426504521 1409404307543448319878391)
        ·
          refine ⟨2114106461315172479817587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409404307543448319878391 2114106461315172479817587)
          ·
            refine ⟨3171159691972758719726381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114106461315172479817587 3171159691972758719726381)
            ·
              refine ⟨1189184884489784519897393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3171159691972758719726381 1189184884489784519897393)
              ·
                refine ⟨891888663367338389923045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189184884489784519897393 891888663367338389923045)
                ·
                  refine ⟨167229124381375948110571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891888663367338389923045 167229124381375948110571)
                  ·
                    rfl

theorem cell22_1465549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1465549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465549 prefixEnd_1465549 := by exact prefixLift 1465549
  have htrace : WordTrace (prefixWord ++ tailWord_1465549) baseStart_1465549 baseEnd_1465549 := by
    simpa [prefixWord, tailWord_1465549, baseEnd_1465549] using wordTrace_append hprefix tailTrace_1465549
  have hstable : (prefixWord ++ tailWord_1465549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465549).length < 2 ^ (prefixWord ++ tailWord_1465549).sum := by decide
  have hdescent : baseEnd_1465549 < baseStart_1465549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465650 : List Nat := [3, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_1465650 : Nat := 118140960795 + 1465650 * 2 ^ 59
def prefixEnd_1465650 : Nat := 4983230072969 + 3 ^ 40 * 1465650 * 2
def baseEnd_1465650 : Nat := 167240649169399082518801

theorem tailTrace_1465650 : CollatzResearch.WordTrace tailWord_1465650 prefixEnd_1465650 167240649169399082518801 := by
  unfold tailWord_1465650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13364161785051959484166601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35637764760138558624444269 13364161785051959484166601)
  ·
    refine ⟨10023121338788969613124951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13364161785051959484166601 10023121338788969613124951)
    ·
      refine ⟨15034682008183454419687427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10023121338788969613124951 15034682008183454419687427)
      ·
        refine ⟨22552023012275181629531141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15034682008183454419687427 22552023012275181629531141)
        ·
          refine ⟨4228504314801596555537089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22552023012275181629531141 4228504314801596555537089)
          ·
            refine ⟨3171378236101197416652817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4228504314801596555537089 3171378236101197416652817)
            ·
              refine ⟨2378533677075898062489613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171378236101197416652817 2378533677075898062489613)
              ·
                refine ⟨891950128903461773433605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2378533677075898062489613 891950128903461773433605)
                ·
                  refine ⟨167240649169399082518801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 891950128903461773433605 167240649169399082518801)
                  ·
                    rfl

theorem cell22_1465650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_1465650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465650 prefixEnd_1465650 := by exact prefixLift 1465650
  have htrace : WordTrace (prefixWord ++ tailWord_1465650) baseStart_1465650 baseEnd_1465650 := by
    simpa [prefixWord, tailWord_1465650, baseEnd_1465650] using wordTrace_append hprefix tailTrace_1465650
  have hstable : (prefixWord ++ tailWord_1465650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465650).length < 2 ^ (prefixWord ++ tailWord_1465650).sum := by decide
  have hdescent : baseEnd_1465650 < baseStart_1465650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465665 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1465665 : Nat := 118140960795 + 1465665 * 2 ^ 59
def prefixEnd_1465665 : Nat := 4983230072969 + 3 ^ 40 * 1465665 * 2
def baseEnd_1465665 : Nat := 501727082314742208431357

theorem tailTrace_1465665 : CollatzResearch.WordTrace tailWord_1465665 prefixEnd_1465665 501727082314742208431357 := by
  unfold tailWord_1465665
  simp only [CollatzResearch.WordTrace]
  refine ⟨53457194235153495498462449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35638129490102330332308299 53457194235153495498462449)
  ·
    refine ⟨40092895676365121623846837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53457194235153495498462449 40092895676365121623846837)
    ·
      refine ⟨3758708969659230152235641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40092895676365121623846837 3758708969659230152235641)
      ·
        refine ⟨2819031727244422614176731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3758708969659230152235641 2819031727244422614176731)
        ·
          refine ⟨4228547590866633921265097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2819031727244422614176731 4228547590866633921265097)
          ·
            refine ⟨3171410693149975440948823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4228547590866633921265097 3171410693149975440948823)
            ·
              refine ⟨4757116039724963161423235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3171410693149975440948823 4757116039724963161423235)
              ·
                refine ⟨7135674059587444742134853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4757116039724963161423235 7135674059587444742134853)
                ·
                  refine ⟨1337938886172645889150285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7135674059587444742134853 1337938886172645889150285)
                  ·
                    refine ⟨501727082314742208431357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1337938886172645889150285 501727082314742208431357)
                    ·
                      rfl

theorem cell22_1465665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1465665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465665 prefixEnd_1465665 := by exact prefixLift 1465665
  have htrace : WordTrace (prefixWord ++ tailWord_1465665) baseStart_1465665 baseEnd_1465665 := by
    simpa [prefixWord, tailWord_1465665, baseEnd_1465665] using wordTrace_append hprefix tailTrace_1465665
  have hstable : (prefixWord ++ tailWord_1465665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465665).length < 2 ^ (prefixWord ++ tailWord_1465665).sum := by decide
  have hdescent : baseEnd_1465665 < baseStart_1465665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1465686 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1465686 : Nat := 118140960795 + 1465686 * 2 ^ 59
def prefixEnd_1465686 : Nat := 4983230072969 + 3 ^ 40 * 1465686 * 2
def baseEnd_1465686 : Nat := 501734271043905153656293

theorem tailTrace_1465686 : CollatzResearch.WordTrace tailWord_1465686 prefixEnd_1465686 501734271043905153656293 := by
  unfold tailWord_1465686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3341122510504838505311057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35638640112051610723317941 3341122510504838505311057)
  ·
    refine ⟨2505841882878628878983293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3341122510504838505311057 2505841882878628878983293)
    ·
      refine ⟨939690706079485829618735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2505841882878628878983293 939690706079485829618735)
      ·
        refine ⟨1409536059119228744428103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939690706079485829618735 1409536059119228744428103)
        ·
          refine ⟨2114304088678843116642155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409536059119228744428103 2114304088678843116642155)
          ·
            refine ⟨3171456133018264674963233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2114304088678843116642155 3171456133018264674963233)
            ·
              refine ⟨2378592099763698506222425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171456133018264674963233 2378592099763698506222425)
              ·
                refine ⟨1783944074822773879666819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378592099763698506222425 1783944074822773879666819)
                ·
                  refine ⟨2675916112234160819500229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783944074822773879666819 2675916112234160819500229)
                  ·
                    refine ⟨501734271043905153656293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675916112234160819500229 501734271043905153656293)
                    ·
                      rfl

theorem cell22_1465686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1465686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1465686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1465686 prefixEnd_1465686 := by exact prefixLift 1465686
  have htrace : WordTrace (prefixWord ++ tailWord_1465686) baseStart_1465686 baseEnd_1465686 := by
    simpa [prefixWord, tailWord_1465686, baseEnd_1465686] using wordTrace_append hprefix tailTrace_1465686
  have hstable : (prefixWord ++ tailWord_1465686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1465686).length < 2 ^ (prefixWord ++ tailWord_1465686).sum := by decide
  have hdescent : baseEnd_1465686 < baseStart_1465686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1465686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
