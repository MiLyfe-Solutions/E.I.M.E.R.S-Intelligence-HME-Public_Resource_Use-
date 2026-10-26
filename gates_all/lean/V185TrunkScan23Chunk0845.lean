import V185TrunkScan23Chunk0844

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5001626 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_5001626 : Nat := 118140960795 + 5001626 * 2 ^ 59
def prefixEnd_5001626 : Nat := 4983230072969 + 3 ^ 40 * 5001626 * 2
def baseEnd_5001626 : Nat := 856079397341584449657649

theorem tailTrace_5001626 : CollatzResearch.WordTrace tailWord_5001626 prefixEnd_5001626 856079397341584449657649 := by
  unfold tailWord_5001626
  simp only [CollatzResearch.WordTrace]
  refine ⟨45606071744492671639700183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121616191318647124372533821 45606071744492671639700183)
  ·
    refine ⟨68409107616739007459550275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45606071744492671639700183 68409107616739007459550275)
    ·
      refine ⟨102613661425108511189325413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68409107616739007459550275 102613661425108511189325413)
      ·
        refine ⟨19240061517207845847998515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102613661425108511189325413 19240061517207845847998515)
        ·
          refine ⟨28860092275811768771997773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19240061517207845847998515 28860092275811768771997773)
          ·
            refine ⟨10822534603429413289499165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28860092275811768771997773 10822534603429413289499165)
            ·
              refine ⟨4058450476286029983562187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10822534603429413289499165 4058450476286029983562187)
              ·
                refine ⟨6087675714429044975343281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058450476286029983562187 6087675714429044975343281)
                ·
                  refine ⟨4565756785821783731507461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6087675714429044975343281 4565756785821783731507461)
                  ·
                    refine ⟨856079397341584449657649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4565756785821783731507461 856079397341584449657649)
                    ·
                      rfl

theorem cell23_5001626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_5001626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001626 prefixEnd_5001626 := by exact prefixLift 5001626
  have htrace : WordTrace (prefixWord ++ tailWord_5001626) baseStart_5001626 baseEnd_5001626 := by
    simpa [prefixWord, tailWord_5001626, baseEnd_5001626] using wordTrace_append hprefix tailTrace_5001626
  have hstable : (prefixWord ++ tailWord_5001626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001626).length < 2 ^ (prefixWord ++ tailWord_5001626).sum := by decide
  have hdescent : baseEnd_5001626 < baseStart_5001626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001639 : List Nat := [1, 1, 6, 1, 1, 4, 2, 7]
def baseStart_5001639 : Nat := 118140960795 + 5001639 * 2 ^ 59
def prefixEnd_5001639 : Nat := 4983230072969 + 3 ^ 40 * 5001639 * 2
def baseEnd_5001639 : Nat := 95120180269380066596681

theorem tailTrace_5001639 : CollatzResearch.WordTrace tailWord_5001639 prefixEnd_5001639 95120180269380066596681 := by
  unfold tailWord_5001639
  simp only [CollatzResearch.WordTrace]
  refine ⟨182424761126923589779023971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121616507417949059852682647 182424761126923589779023971)
  ·
    refine ⟨273637141690385384668535957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182424761126923589779023971 273637141690385384668535957)
    ·
      refine ⟨12826741016736814906337623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 273637141690385384668535957 12826741016736814906337623)
      ·
        refine ⟨19240111525105222359506435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12826741016736814906337623 19240111525105222359506435)
        ·
          refine ⟨28860167287657833539259653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19240111525105222359506435 28860167287657833539259653)
          ·
            refine ⟨5411281366435843788611185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28860167287657833539259653 5411281366435843788611185)
            ·
              refine ⟨4058461024826882841458389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5411281366435843788611185 4058461024826882841458389)
              ·
                refine ⟨95120180269380066596681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4058461024826882841458389 95120180269380066596681)
                ·
                  rfl

theorem cell23_5001639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 7].length) (baseStart_5001639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001639 prefixEnd_5001639 := by exact prefixLift 5001639
  have htrace : WordTrace (prefixWord ++ tailWord_5001639) baseStart_5001639 baseEnd_5001639 := by
    simpa [prefixWord, tailWord_5001639, baseEnd_5001639] using wordTrace_append hprefix tailTrace_5001639
  have hstable : (prefixWord ++ tailWord_5001639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001639).length < 2 ^ (prefixWord ++ tailWord_5001639).sum := by decide
  have hdescent : baseEnd_5001639 < baseStart_5001639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001649 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_5001649 : Nat := 118140960795 + 5001649 * 2 ^ 59
def prefixEnd_5001649 : Nat := 4983230072969 + 3 ^ 40 * 5001649 * 2
def baseEnd_5001649 : Nat := 2568250002079806758985341

theorem tailTrace_5001649 : CollatzResearch.WordTrace tailWord_5001649 prefixEnd_5001649 2568250002079806758985341 := by
  unfold tailWord_5001649
  simp only [CollatzResearch.WordTrace]
  refine ⟨182425125856887361486888001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121616750571258240991258667 182425125856887361486888001)
  ·
    refine ⟨136818844392665521115166001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182425125856887361486888001 136818844392665521115166001)
    ·
      refine ⟨102614133294499140836374501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136818844392665521115166001 102614133294499140836374501)
      ·
        refine ⟨19240149992718588906820219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102614133294499140836374501 19240149992718588906820219)
        ·
          refine ⟨28860224989077883360230329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19240149992718588906820219 28860224989077883360230329)
          ·
            refine ⟨21645168741808412520172747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28860224989077883360230329 21645168741808412520172747)
            ·
              refine ⟨32467753112712618780259121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21645168741808412520172747 32467753112712618780259121)
              ·
                refine ⟨24350814834534464085194341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32467753112712618780259121 24350814834534464085194341)
                ·
                  refine ⟨4565777781475212015973939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24350814834534464085194341 4565777781475212015973939)
                  ·
                    refine ⟨6848666672212818023960909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4565777781475212015973939 6848666672212818023960909)
                    ·
                      refine ⟨2568250002079806758985341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6848666672212818023960909 2568250002079806758985341)
                      ·
                        rfl

theorem cell23_5001649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_5001649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001649 prefixEnd_5001649 := by exact prefixLift 5001649
  have htrace : WordTrace (prefixWord ++ tailWord_5001649) baseStart_5001649 baseEnd_5001649 := by
    simpa [prefixWord, tailWord_5001649, baseEnd_5001649] using wordTrace_append hprefix tailTrace_5001649
  have hstable : (prefixWord ++ tailWord_5001649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001649).length < 2 ^ (prefixWord ++ tailWord_5001649).sum := by decide
  have hdescent : baseEnd_5001649 < baseStart_5001649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001675 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 5]
def baseStart_5001675 : Nat := 118140960795 + 5001675 * 2 ^ 59
def prefixEnd_5001675 : Nat := 4983230072969 + 3 ^ 40 * 5001675 * 2
def baseEnd_5001675 : Nat := 2568263352576823657260221

theorem tailTrace_5001675 : CollatzResearch.WordTrace tailWord_5001675 prefixEnd_5001675 2568263352576823657260221 := by
  unfold tailWord_5001675
  simp only [CollatzResearch.WordTrace]
  refine ⟨182426074154793167927334479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121617382769862111951556319 182426074154793167927334479)
  ·
    refine ⟨273639111232189751891001719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182426074154793167927334479 273639111232189751891001719)
    ·
      refine ⟨410458666848284627836502579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273639111232189751891001719 410458666848284627836502579)
      ·
        refine ⟨615688000272426941754753869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410458666848284627836502579 615688000272426941754753869)
        ·
          refine ⟨230883000102160103158032701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 615688000272426941754753869 230883000102160103158032701)
          ·
            refine ⟨86581125038310038684262263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230883000102160103158032701 86581125038310038684262263)
            ·
              refine ⟨129871687557465058026393395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86581125038310038684262263 129871687557465058026393395)
              ·
                refine ⟨194807531336197587039590093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129871687557465058026393395 194807531336197587039590093)
                ·
                  refine ⟨73052824251074095139846285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194807531336197587039590093 73052824251074095139846285)
                  ·
                    refine ⟨27394809094152785677442357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73052824251074095139846285 27394809094152785677442357)
                    ·
                      refine ⟨2568263352576823657260221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27394809094152785677442357 2568263352576823657260221)
                      ·
                        rfl

theorem cell23_5001675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_5001675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001675 prefixEnd_5001675 := by exact prefixLift 5001675
  have htrace : WordTrace (prefixWord ++ tailWord_5001675) baseStart_5001675 baseEnd_5001675 := by
    simpa [prefixWord, tailWord_5001675, baseEnd_5001675] using wordTrace_append hprefix tailTrace_5001675
  have hstable : (prefixWord ++ tailWord_5001675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001675).length < 2 ^ (prefixWord ++ tailWord_5001675).sum := by decide
  have hdescent : baseEnd_5001675 < baseStart_5001675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001689 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 1, 4, 2]
def baseStart_5001689 : Nat := 118140960795 + 5001689 * 2 ^ 59
def prefixEnd_5001689 : Nat := 4983230072969 + 3 ^ 40 * 5001689 * 2
def baseEnd_5001689 : Nat := 2568270541305986602485157

theorem tailTrace_5001689 : CollatzResearch.WordTrace tailWord_5001689 prefixEnd_5001689 2568270541305986602485157 := by
  unfold tailWord_5001689
  simp only [CollatzResearch.WordTrace]
  refine ⟨182426584776742448318344121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121617723184494965545562747 182426584776742448318344121)
  ·
    refine ⟨136819938582556836238758091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182426584776742448318344121 136819938582556836238758091)
    ·
      refine ⟨205229907873835254358137137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136819938582556836238758091 205229907873835254358137137)
      ·
        refine ⟨153922430905376440768602853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205229907873835254358137137 153922430905376440768602853)
        ·
          refine ⟨28860455794758082644113035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153922430905376440768602853 28860455794758082644113035)
          ·
            refine ⟨43290683692137123966169553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28860455794758082644113035 43290683692137123966169553)
            ·
              refine ⟨32468012769102842974627165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43290683692137123966169553 32468012769102842974627165)
              ·
                refine ⟨12175504788413566115485187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32468012769102842974627165 12175504788413566115485187)
                ·
                  refine ⟨18263257182620349173227781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12175504788413566115485187 18263257182620349173227781)
                  ·
                    refine ⟨3424360721741315469980209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18263257182620349173227781 3424360721741315469980209)
                    ·
                      refine ⟨2568270541305986602485157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424360721741315469980209 2568270541305986602485157)
                      ·
                        rfl

theorem cell23_5001689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_5001689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001689 prefixEnd_5001689 := by exact prefixLift 5001689
  have htrace : WordTrace (prefixWord ++ tailWord_5001689) baseStart_5001689 baseEnd_5001689 := by
    simpa [prefixWord, tailWord_5001689, baseEnd_5001689] using wordTrace_append hprefix tailTrace_5001689
  have hstable : (prefixWord ++ tailWord_5001689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001689).length < 2 ^ (prefixWord ++ tailWord_5001689).sum := by decide
  have hdescent : baseEnd_5001689 < baseStart_5001689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001705 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_5001705 : Nat := 118140960795 + 5001705 * 2 ^ 59
def prefixEnd_5001705 : Nat := 4983230072969 + 3 ^ 40 * 5001705 * 2
def baseEnd_5001705 : Nat := 2568278756996458539885083

theorem tailTrace_5001705 : CollatzResearch.WordTrace tailWord_5001705 prefixEnd_5001705 2568278756996458539885083 := by
  unfold tailWord_5001705
  simp only [CollatzResearch.WordTrace]
  refine ⟨182427168344684483050926569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121618112229789655367284379 182427168344684483050926569)
  ·
    refine ⟨136820376258513362288194927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182427168344684483050926569 136820376258513362288194927)
    ·
      refine ⟨205230564387770043432292391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136820376258513362288194927 205230564387770043432292391)
      ·
        refine ⟨307845846581655065148438587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205230564387770043432292391 307845846581655065148438587)
        ·
          refine ⟨461768769872482597722657881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307845846581655065148438587 461768769872482597722657881)
          ·
            refine ⟨346326577404361948291993411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461768769872482597722657881 346326577404361948291993411)
            ·
              refine ⟨519489866106542922437990117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346326577404361948291993411 519489866106542922437990117)
              ·
                refine ⟨97404349894976797957123147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519489866106542922437990117 97404349894976797957123147)
                ·
                  refine ⟨146106524842465196935684721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97404349894976797957123147 146106524842465196935684721)
                  ·
                    refine ⟨109579893631848897701763541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146106524842465196935684721 109579893631848897701763541)
                    ·
                      refine ⟨2568278756996458539885083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109579893631848897701763541 2568278756996458539885083)
                      ·
                        rfl

theorem cell23_5001705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_5001705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001705 prefixEnd_5001705 := by exact prefixLift 5001705
  have htrace : WordTrace (prefixWord ++ tailWord_5001705) baseStart_5001705 baseEnd_5001705 := by
    simpa [prefixWord, tailWord_5001705, baseEnd_5001705] using wordTrace_append hprefix tailTrace_5001705
  have hstable : (prefixWord ++ tailWord_5001705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001705).length < 2 ^ (prefixWord ++ tailWord_5001705).sum := by decide
  have hdescent : baseEnd_5001705 < baseStart_5001705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001706 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_5001706 : Nat := 118140960795 + 5001706 * 2 ^ 59
def prefixEnd_5001706 : Nat := 4983230072969 + 3 ^ 40 * 5001706 * 2
def baseEnd_5001706 : Nat := 2568279270477113035972579

theorem tailTrace_5001706 : CollatzResearch.WordTrace tailWord_5001706 prefixEnd_5001706 2568279270477113035972579 := by
  unfold tailWord_5001706
  simp only [CollatzResearch.WordTrace]
  refine ⟨45606801204420215055428243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121618136545120573481141981 45606801204420215055428243)
  ·
    refine ⟨68410201806630322583142365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45606801204420215055428243 68410201806630322583142365)
    ·
      refine ⟨25653825677486370968678387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68410201806630322583142365 25653825677486370968678387)
      ·
        refine ⟨38480738516229556453017581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25653825677486370968678387 38480738516229556453017581)
        ·
          refine ⟨14430276943586083669881593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38480738516229556453017581 14430276943586083669881593)
          ·
            refine ⟨10822707707689562752411195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14430276943586083669881593 10822707707689562752411195)
            ·
              refine ⟨16234061561534344128616793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10822707707689562752411195 16234061561534344128616793)
              ·
                refine ⟨12175546171150758096462595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16234061561534344128616793 12175546171150758096462595)
                ·
                  refine ⟨18263319256726137144693893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12175546171150758096462595 18263319256726137144693893)
                  ·
                    refine ⟨3424372360636150714630105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18263319256726137144693893 3424372360636150714630105)
                    ·
                      refine ⟨2568279270477113035972579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424372360636150714630105 2568279270477113035972579)
                      ·
                        rfl

theorem cell23_5001706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_5001706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001706 prefixEnd_5001706 := by exact prefixLift 5001706
  have htrace : WordTrace (prefixWord ++ tailWord_5001706) baseStart_5001706 baseEnd_5001706 := by
    simpa [prefixWord, tailWord_5001706, baseEnd_5001706] using wordTrace_append hprefix tailTrace_5001706
  have hstable : (prefixWord ++ tailWord_5001706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001706).length < 2 ^ (prefixWord ++ tailWord_5001706).sum := by decide
  have hdescent : baseEnd_5001706 < baseStart_5001706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001709 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5001709 : Nat := 118140960795 + 5001709 * 2 ^ 59
def prefixEnd_5001709 : Nat := 4983230072969 + 3 ^ 40 * 5001709 * 2
def baseEnd_5001709 : Nat := 2568280810919076524235065

theorem tailTrace_5001709 : CollatzResearch.WordTrace tailWord_5001709 prefixEnd_5001709 2568280810919076524235065 := by
  unfold tailWord_5001709
  simp only [CollatzResearch.WordTrace]
  refine ⟨182427314236669991734072181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121618209491113327822714787 182427314236669991734072181)
  ·
    refine ⟨17102560709687811725069267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182427314236669991734072181 17102560709687811725069267)
    ·
      refine ⟨25653841064531717587603901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17102560709687811725069267 25653841064531717587603901)
      ·
        refine ⟨9620190399199394095351463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25653841064531717587603901 9620190399199394095351463)
        ·
          refine ⟨14430285598799091143027195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9620190399199394095351463 14430285598799091143027195)
          ·
            refine ⟨21645428398198636714540793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14430285598799091143027195 21645428398198636714540793)
            ·
              refine ⟨16234071298648977535905595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21645428398198636714540793 16234071298648977535905595)
              ·
                refine ⟨24351106947973466303858393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16234071298648977535905595 24351106947973466303858393)
                ·
                  refine ⟨18263330210980099727893795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24351106947973466303858393 18263330210980099727893795)
                  ·
                    refine ⟨27394995316470149591840693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18263330210980099727893795 27394995316470149591840693)
                    ·
                      refine ⟨2568280810919076524235065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27394995316470149591840693 2568280810919076524235065)
                      ·
                        rfl

theorem cell23_5001709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5001709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001709 prefixEnd_5001709 := by exact prefixLift 5001709
  have htrace : WordTrace (prefixWord ++ tailWord_5001709) baseStart_5001709 baseEnd_5001709 := by
    simpa [prefixWord, tailWord_5001709, baseEnd_5001709] using wordTrace_append hprefix tailTrace_5001709
  have hstable : (prefixWord ++ tailWord_5001709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001709).length < 2 ^ (prefixWord ++ tailWord_5001709).sum := by decide
  have hdescent : baseEnd_5001709 < baseStart_5001709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001739 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 3]
def baseStart_5001739 : Nat := 118140960795 + 5001739 * 2 ^ 59
def prefixEnd_5001739 : Nat := 4983230072969 + 3 ^ 40 * 5001739 * 2
def baseEnd_5001739 : Nat := 2568296215338711406859927

theorem tailTrace_5001739 : CollatzResearch.WordTrace tailWord_5001739 prefixEnd_5001739 2568296215338711406859927 := by
  unfold tailWord_5001739
  simp only [CollatzResearch.WordTrace]
  refine ⟨182428408426561306857664271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121618938951040871238442847 182428408426561306857664271)
  ·
    refine ⟨273642612639841960286496407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182428408426561306857664271 273642612639841960286496407)
    ·
      refine ⟨410463918959762940429744611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273642612639841960286496407 410463918959762940429744611)
      ·
        refine ⟨615695878439644410644616917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410463918959762940429744611 615695878439644410644616917)
        ·
          refine ⟨14430372150929165874483209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 615695878439644410644616917 14430372150929165874483209)
          ·
            refine ⟨10822779113196874405862407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14430372150929165874483209 10822779113196874405862407)
            ·
              refine ⟨16234168669795311608793611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10822779113196874405862407 16234168669795311608793611)
              ·
                refine ⟨24351253004692967413190417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16234168669795311608793611 24351253004692967413190417)
                ·
                  refine ⟨18263439753519725559892813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24351253004692967413190417 18263439753519725559892813)
                  ·
                    refine ⟨6848789907569897084959805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18263439753519725559892813 6848789907569897084959805)
                    ·
                      refine ⟨2568296215338711406859927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6848789907569897084959805 2568296215338711406859927)
                      ·
                        rfl

theorem cell23_5001739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 3].length) (baseStart_5001739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001739 prefixEnd_5001739 := by exact prefixLift 5001739
  have htrace : WordTrace (prefixWord ++ tailWord_5001739) baseStart_5001739 baseEnd_5001739 := by
    simpa [prefixWord, tailWord_5001739, baseEnd_5001739] using wordTrace_append hprefix tailTrace_5001739
  have hstable : (prefixWord ++ tailWord_5001739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001739).length < 2 ^ (prefixWord ++ tailWord_5001739).sum := by decide
  have hdescent : baseEnd_5001739 < baseStart_5001739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001749 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_5001749 : Nat := 118140960795 + 5001749 * 2 ^ 59
def prefixEnd_5001749 : Nat := 4983230072969 + 3 ^ 40 * 5001749 * 2
def baseEnd_5001749 : Nat := 2568301350145256367734881

theorem tailTrace_5001749 : CollatzResearch.WordTrace tailWord_5001749 prefixEnd_5001749 2568301350145256367734881 := by
  unfold tailWord_5001749
  simp only [CollatzResearch.WordTrace]
  refine ⟨182428773156525078565528301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121619182104350052377018867 182428773156525078565528301)
  ·
    refine ⟨68410789933696904462073113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182428773156525078565528301 68410789933696904462073113)
    ·
      refine ⟨51308092450272678346554835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68410789933696904462073113 51308092450272678346554835)
      ·
        refine ⟨76962138675409017519832253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51308092450272678346554835 76962138675409017519832253)
        ·
          refine ⟨28860802003278381569937095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76962138675409017519832253 28860802003278381569937095)
          ·
            refine ⟨43291203004917572354905643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28860802003278381569937095 43291203004917572354905643)
            ·
              refine ⟨64936804507376358532358465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43291203004917572354905643 64936804507376358532358465)
              ·
                refine ⟨48702603380532268899268849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64936804507376358532358465 48702603380532268899268849)
                ·
                  refine ⟨36526952535399201674451637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48702603380532268899268849 36526952535399201674451637)
                  ·
                    refine ⟨3424401800193675156979841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36526952535399201674451637 3424401800193675156979841)
                    ·
                      refine ⟨2568301350145256367734881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424401800193675156979841 2568301350145256367734881)
                      ·
                        rfl

theorem cell23_5001749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_5001749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001749 prefixEnd_5001749 := by exact prefixLift 5001749
  have htrace : WordTrace (prefixWord ++ tailWord_5001749) baseStart_5001749 baseEnd_5001749 := by
    simpa [prefixWord, tailWord_5001749, baseEnd_5001749] using wordTrace_append hprefix tailTrace_5001749
  have hstable : (prefixWord ++ tailWord_5001749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001749).length < 2 ^ (prefixWord ++ tailWord_5001749).sum := by decide
  have hdescent : baseEnd_5001749 < baseStart_5001749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001779 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 4, 4, 2]
def baseStart_5001779 : Nat := 118140960795 + 5001779 * 2 ^ 59
def prefixEnd_5001779 : Nat := 4983230072969 + 3 ^ 40 * 5001779 * 2
def baseEnd_5001779 : Nat := 2568316754564891250359743

theorem tailTrace_5001779 : CollatzResearch.WordTrace tailWord_5001779 prefixEnd_5001779 2568316754564891250359743 := by
  unfold tailWord_5001779
  simp only [CollatzResearch.WordTrace]
  refine ⟨182429867346416393689120391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121619911564277595792746927 182429867346416393689120391)
  ·
    refine ⟨273644801019624590533680587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182429867346416393689120391 273644801019624590533680587)
    ·
      refine ⟨410467201529436885800520881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273644801019624590533680587 410467201529436885800520881)
      ·
        refine ⟨307850401147077664350390661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410467201529436885800520881 307850401147077664350390661)
        ·
          refine ⟨57721950215077062065698249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307850401147077664350390661 57721950215077062065698249)
          ·
            refine ⟨43291462661307796549273687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57721950215077062065698249 43291462661307796549273687)
            ·
              refine ⟨64937193991961694823910531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43291462661307796549273687 64937193991961694823910531)
              ·
                refine ⟨97405790987942542235865797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64937193991961694823910531 97405790987942542235865797)
                ·
                  refine ⟨18263585810239226669224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97405790987942542235865797 18263585810239226669224837)
                  ·
                    refine ⟨3424422339419855000479657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18263585810239226669224837 3424422339419855000479657)
                    ·
                      refine ⟨2568316754564891250359743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424422339419855000479657 2568316754564891250359743)
                      ·
                        rfl

theorem cell23_5001779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 4, 2].length) (baseStart_5001779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001779 prefixEnd_5001779 := by exact prefixLift 5001779
  have htrace : WordTrace (prefixWord ++ tailWord_5001779) baseStart_5001779 baseEnd_5001779 := by
    simpa [prefixWord, tailWord_5001779, baseEnd_5001779] using wordTrace_append hprefix tailTrace_5001779
  have hstable : (prefixWord ++ tailWord_5001779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001779).length < 2 ^ (prefixWord ++ tailWord_5001779).sum := by decide
  have hdescent : baseEnd_5001779 < baseStart_5001779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001799 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_5001799 : Nat := 118140960795 + 5001799 * 2 ^ 59
def prefixEnd_5001799 : Nat := 4983230072969 + 3 ^ 40 * 5001799 * 2
def baseEnd_5001799 : Nat := 2568327024177981172109651

theorem tailTrace_5001799 : CollatzResearch.WordTrace tailWord_5001799 prefixEnd_5001799 2568327024177981172109651 := by
  unfold tailWord_5001799
  simp only [CollatzResearch.WordTrace]
  refine ⟨182430596806343937104848451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121620397870895958069898967 182430596806343937104848451)
  ·
    refine ⟨273645895209515905657272677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182430596806343937104848451 273645895209515905657272677)
    ·
      refine ⟨51308605351784232310738627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273645895209515905657272677 51308605351784232310738627)
      ·
        refine ⟨76962908027676348466107941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51308605351784232310738627 76962908027676348466107941)
        ·
          refine ⟨14430545255189315337395239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76962908027676348466107941 14430545255189315337395239)
          ·
            refine ⟨21645817882783973006092859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14430545255189315337395239 21645817882783973006092859)
            ·
              refine ⟨32468726824175959509139289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21645817882783973006092859 32468726824175959509139289)
              ·
                refine ⟨24351545118131969631854467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32468726824175959509139289 24351545118131969631854467)
                ·
                  refine ⟨36527317677197954447781701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24351545118131969631854467 36527317677197954447781701)
                  ·
                    refine ⟨6848872064474616458959069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36527317677197954447781701 6848872064474616458959069)
                    ·
                      refine ⟨2568327024177981172109651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6848872064474616458959069 2568327024177981172109651)
                      ·
                        rfl

theorem cell23_5001799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_5001799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001799 prefixEnd_5001799 := by exact prefixLift 5001799
  have htrace : WordTrace (prefixWord ++ tailWord_5001799) baseStart_5001799 baseEnd_5001799 := by
    simpa [prefixWord, tailWord_5001799, baseEnd_5001799] using wordTrace_append hprefix tailTrace_5001799
  have hstable : (prefixWord ++ tailWord_5001799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001799).length < 2 ^ (prefixWord ++ tailWord_5001799).sum := by decide
  have hdescent : baseEnd_5001799 < baseStart_5001799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001840 : List Nat := [2, 1, 1, 1, 7, 1, 3, 2, 1, 4]
def baseStart_5001840 : Nat := 118140960795 + 5001840 * 2 ^ 59
def prefixEnd_5001840 : Nat := 4983230072969 + 3 ^ 40 * 5001840 * 2
def baseEnd_5001840 : Nat := 856116025628271837232321

theorem tailTrace_5001840 : CollatzResearch.WordTrace tailWord_5001840 prefixEnd_5001840 856116025628271837232321 := by
  unfold tailWord_5001840
  simp only [CollatzResearch.WordTrace]
  refine ⟨91216046099597700553545487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121621394799463600738060649 91216046099597700553545487)
  ·
    refine ⟨136824069149396550830318231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91216046099597700553545487 136824069149396550830318231)
    ·
      refine ⟨205236103724094826245477347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136824069149396550830318231 205236103724094826245477347)
      ·
        refine ⟨307854155586142239368216021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205236103724094826245477347 307854155586142239368216021)
        ·
          refine ⟨7215331771550208735192563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 307854155586142239368216021 7215331771550208735192563)
          ·
            refine ⟨10822997657325313102788845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215331771550208735192563 10822997657325313102788845)
            ·
              refine ⟨4058624121496992413545817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10822997657325313102788845 4058624121496992413545817)
              ·
                refine ⟨3043968091122744310159363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4058624121496992413545817 3043968091122744310159363)
                ·
                  refine ⟨4565952136684116465239045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043968091122744310159363 4565952136684116465239045)
                  ·
                    refine ⟨856116025628271837232321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4565952136684116465239045 856116025628271837232321)
                    ·
                      rfl

theorem cell23_5001840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 4].length) (baseStart_5001840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001840 prefixEnd_5001840 := by exact prefixLift 5001840
  have htrace : WordTrace (prefixWord ++ tailWord_5001840) baseStart_5001840 baseEnd_5001840 := by
    simpa [prefixWord, tailWord_5001840, baseEnd_5001840] using wordTrace_append hprefix tailTrace_5001840
  have hstable : (prefixWord ++ tailWord_5001840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001840).length < 2 ^ (prefixWord ++ tailWord_5001840).sum := by decide
  have hdescent : baseEnd_5001840 < baseStart_5001840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001853 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 6]
def baseStart_5001853 : Nat := 118140960795 + 5001853 * 2 ^ 59
def prefixEnd_5001853 : Nat := 4983230072969 + 3 ^ 40 * 5001853 * 2
def baseEnd_5001853 : Nat := 285372750237035995648267

theorem tailTrace_5001853 : CollatzResearch.WordTrace tailWord_5001853 prefixEnd_5001853 285372750237035995648267 := by
  unfold tailWord_5001853
  simp only [CollatzResearch.WordTrace]
  refine ⟨182432566348148304327314213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121621710898765536218209475 182432566348148304327314213)
  ·
    refine ⟨34206106190277807061371415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182432566348148304327314213 34206106190277807061371415)
    ·
      refine ⟨51309159285416710592057123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34206106190277807061371415 51309159285416710592057123)
      ·
        refine ⟨76963738928125065888085685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51309159285416710592057123 76963738928125065888085685)
        ·
          refine ⟨7215350524511724927008033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76963738928125065888085685 7215350524511724927008033)
          ·
            refine ⟨5411512893383793695256025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7215350524511724927008033 5411512893383793695256025)
            ·
              refine ⟨4058634670037845271442019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5411512893383793695256025 4058634670037845271442019)
              ·
                refine ⟨6087952005056767907163029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058634670037845271442019 6087952005056767907163029)
                ·
                  refine ⟨285372750237035995648267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6087952005056767907163029 285372750237035995648267)
                  ·
                    rfl

theorem cell23_5001853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_5001853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001853 prefixEnd_5001853 := by exact prefixLift 5001853
  have htrace : WordTrace (prefixWord ++ tailWord_5001853) baseStart_5001853 baseEnd_5001853 := by
    simpa [prefixWord, tailWord_5001853, baseEnd_5001853] using wordTrace_append hprefix tailTrace_5001853
  have hstable : (prefixWord ++ tailWord_5001853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001853).length < 2 ^ (prefixWord ++ tailWord_5001853).sum := by decide
  have hdescent : baseEnd_5001853 < baseStart_5001853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001866 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_5001866 : Nat := 118140960795 + 5001866 * 2 ^ 59
def prefixEnd_5001866 : Nat := 4983230072969 + 3 ^ 40 * 5001866 * 2
def baseEnd_5001866 : Nat := 856120475793944136657281

theorem tailTrace_5001866 : CollatzResearch.WordTrace tailWord_5001866 prefixEnd_5001866 856120475793944136657281 := by
  unfold tailWord_5001866
  simp only [CollatzResearch.WordTrace]
  refine ⟨45608260124275301886884363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121622026998067471698358301 45608260124275301886884363)
  ·
    refine ⟨68412390186412952830326545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45608260124275301886884363 68412390186412952830326545)
    ·
      refine ⟨51309292639809714622744909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68412390186412952830326545 51309292639809714622744909)
      ·
        refine ⟨19240984739928642983529341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51309292639809714622744909 19240984739928642983529341)
        ·
          refine ⟨7215369277473241118823503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19240984739928642983529341 7215369277473241118823503)
          ·
            refine ⟨10823053916209861678235255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215369277473241118823503 10823053916209861678235255)
            ·
              refine ⟨16234580874314792517352883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10823053916209861678235255 16234580874314792517352883)
              ·
                refine ⟨24351871311472188776029325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16234580874314792517352883 24351871311472188776029325)
                ·
                  refine ⟨9131951741802070791010997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24351871311472188776029325 9131951741802070791010997)
                  ·
                    refine ⟨856120475793944136657281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9131951741802070791010997 856120475793944136657281)
                    ·
                      rfl

theorem cell23_5001866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_5001866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001866 prefixEnd_5001866 := by exact prefixLift 5001866
  have htrace : WordTrace (prefixWord ++ tailWord_5001866) baseStart_5001866 baseEnd_5001866 := by
    simpa [prefixWord, tailWord_5001866, baseEnd_5001866] using wordTrace_append hprefix tailTrace_5001866
  have hstable : (prefixWord ++ tailWord_5001866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001866).length < 2 ^ (prefixWord ++ tailWord_5001866).sum := by decide
  have hdescent : baseEnd_5001866 < baseStart_5001866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001872 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_5001872 : Nat := 118140960795 + 5001872 * 2 ^ 59
def prefixEnd_5001872 : Nat := 4983230072969 + 3 ^ 40 * 5001872 * 2
def baseEnd_5001872 : Nat := 2568364508265759386496815

theorem tailTrace_5001872 : CollatzResearch.WordTrace tailWord_5001872 prefixEnd_5001872 2568364508265759386496815 := by
  unfold tailWord_5001872
  simp only [CollatzResearch.WordTrace]
  refine ⟨91216629667539735286127935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121622172890052980381503913 91216629667539735286127935)
  ·
    refine ⟨136824944501309602929191903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91216629667539735286127935 136824944501309602929191903)
    ·
      refine ⟨205237416751964404393787855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136824944501309602929191903 205237416751964404393787855)
      ·
        refine ⟨307856125127946606590681783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205237416751964404393787855 307856125127946606590681783)
        ·
          refine ⟨461784187691919909886022675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307856125127946606590681783 461784187691919909886022675)
          ·
            refine ⟨692676281537879864829034013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461784187691919909886022675 692676281537879864829034013)
            ·
              refine ⟨259753605576704949310887755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 692676281537879864829034013 259753605576704949310887755)
              ·
                refine ⟨389630408365057423966331633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259753605576704949310887755 389630408365057423966331633)
                ·
                  refine ⟨292222806273793067974748725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389630408365057423966331633 292222806273793067974748725)
                  ·
                    refine ⟨27395888088168100122632693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 292222806273793067974748725 27395888088168100122632693)
                    ·
                      refine ⟨2568364508265759386496815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27395888088168100122632693 2568364508265759386496815)
                      ·
                        rfl

theorem cell23_5001872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_5001872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001872 prefixEnd_5001872 := by exact prefixLift 5001872
  have htrace : WordTrace (prefixWord ++ tailWord_5001872) baseStart_5001872 baseEnd_5001872 := by
    simpa [prefixWord, tailWord_5001872, baseEnd_5001872] using wordTrace_append hprefix tailTrace_5001872
  have hstable : (prefixWord ++ tailWord_5001872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001872).length < 2 ^ (prefixWord ++ tailWord_5001872).sum := by decide
  have hdescent : baseEnd_5001872 < baseStart_5001872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001879 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 1, 6]
def baseStart_5001879 : Nat := 118140960795 + 5001879 * 2 ^ 59
def prefixEnd_5001879 : Nat := 4983230072969 + 3 ^ 40 * 5001879 * 2
def baseEnd_5001879 : Nat := 856122700876780286369761

theorem tailTrace_5001879 : CollatzResearch.WordTrace tailWord_5001879 prefixEnd_5001879 856122700876780286369761 := by
  unfold tailWord_5001879
  simp only [CollatzResearch.WordTrace]
  refine ⟨182433514646054110767760691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121622343097369407178507127 182433514646054110767760691)
  ·
    refine ⟨273650271969081166151641037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182433514646054110767760691 273650271969081166151641037)
    ·
      refine ⟨102618851988405437306865389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273650271969081166151641037 102618851988405437306865389)
      ·
        refine ⟨38482069495652038990074521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102618851988405437306865389 38482069495652038990074521)
        ·
          refine ⟨28861552121739029242555891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38482069495652038990074521 28861552121739029242555891)
          ·
            refine ⟨43292328182608543863833837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28861552121739029242555891 43292328182608543863833837)
            ·
              refine ⟨16234623068478203948937689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43292328182608543863833837 16234623068478203948937689)
              ·
                refine ⟨12175967301358652961703267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16234623068478203948937689 12175967301358652961703267)
                ·
                  refine ⟨18263950952037979442554901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12175967301358652961703267 18263950952037979442554901)
                  ·
                    refine ⟨856122700876780286369761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18263950952037979442554901 856122700876780286369761)
                    ·
                      rfl

theorem cell23_5001879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_5001879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001879 prefixEnd_5001879 := by exact prefixLift 5001879
  have htrace : WordTrace (prefixWord ++ tailWord_5001879) baseStart_5001879 baseEnd_5001879 := by
    simpa [prefixWord, tailWord_5001879, baseEnd_5001879] using wordTrace_append hprefix tailTrace_5001879
  have hstable : (prefixWord ++ tailWord_5001879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001879).length < 2 ^ (prefixWord ++ tailWord_5001879).sum := by decide
  have hdescent : baseEnd_5001879 < baseStart_5001879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001916 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_5001916 : Nat := 118140960795 + 5001916 * 2 ^ 59
def prefixEnd_5001916 : Nat := 4983230072969 + 3 ^ 40 * 5001916 * 2
def baseEnd_5001916 : Nat := 2568387101414557214346613

theorem tailTrace_5001916 : CollatzResearch.WordTrace tailWord_5001916 prefixEnd_5001916 2568387101414557214346613 := by
  unfold tailWord_5001916
  simp only [CollatzResearch.WordTrace]
  refine ⟨91217432073460033043428801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121623242764613377391238401 91217432073460033043428801)
  ·
    refine ⟨68413074055095024782571601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91217432073460033043428801 68413074055095024782571601)
    ·
      refine ⟨51309805541321268586928701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68413074055095024782571601 51309805541321268586928701)
      ·
        refine ⟨19241177077995475720098263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51309805541321268586928701 19241177077995475720098263)
        ·
          refine ⟨28861765616993213580147395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19241177077995475720098263 28861765616993213580147395)
          ·
            refine ⟨43292648425489820370221093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28861765616993213580147395 43292648425489820370221093)
            ·
              refine ⟨8117371579779341319416455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43292648425489820370221093 8117371579779341319416455)
              ·
                refine ⟨12176057369669011979124683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8117371579779341319416455 12176057369669011979124683)
                ·
                  refine ⟨18264086054503517968687025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12176057369669011979124683 18264086054503517968687025)
                  ·
                    refine ⟨13698064540877638476515269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18264086054503517968687025 13698064540877638476515269)
                    ·
                      refine ⟨2568387101414557214346613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13698064540877638476515269 2568387101414557214346613)
                      ·
                        rfl

theorem cell23_5001916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_5001916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001916 prefixEnd_5001916 := by exact prefixLift 5001916
  have htrace : WordTrace (prefixWord ++ tailWord_5001916) baseStart_5001916 baseEnd_5001916 := by
    simpa [prefixWord, tailWord_5001916, baseEnd_5001916] using wordTrace_append hprefix tailTrace_5001916
  have hstable : (prefixWord ++ tailWord_5001916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001916).length < 2 ^ (prefixWord ++ tailWord_5001916).sum := by decide
  have hdescent : baseEnd_5001916 < baseStart_5001916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001940 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5001940 : Nat := 118140960795 + 5001940 * 2 ^ 59
def prefixEnd_5001940 : Nat := 4983230072969 + 3 ^ 40 * 5001940 * 2
def baseEnd_5001940 : Nat := 2568399424950265120446503

theorem tailTrace_5001940 : CollatzResearch.WordTrace tailWord_5001940 prefixEnd_5001940 2568399424950265120446503 := by
  unfold tailWord_5001940
  simp only [CollatzResearch.WordTrace]
  refine ⟨91217869749416559092865637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121623826332555412123820849 91217869749416559092865637)
  ·
    refine ⟨17103350578015604829912307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91217869749416559092865637 17103350578015604829912307)
    ·
      refine ⟨25655025867023407244868461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17103350578015604829912307 25655025867023407244868461)
      ·
        refine ⟨9620634700133777716825673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25655025867023407244868461 9620634700133777716825673)
        ·
          refine ⟨7215476025100333287619255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9620634700133777716825673 7215476025100333287619255)
          ·
            refine ⟨10823214037650499931428883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215476025100333287619255 10823214037650499931428883)
            ·
              refine ⟨16234821056475749897143325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10823214037650499931428883 16234821056475749897143325)
              ·
                refine ⟨6088057896178406211428747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16234821056475749897143325 6088057896178406211428747)
                ·
                  refine ⟨9132086844267609317143121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088057896178406211428747 9132086844267609317143121)
                  ·
                    refine ⟨6849065133200706987857341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9132086844267609317143121 6849065133200706987857341)
                    ·
                      refine ⟨2568399424950265120446503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849065133200706987857341 2568399424950265120446503)
                      ·
                        rfl

theorem cell23_5001940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5001940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001940 prefixEnd_5001940 := by exact prefixLift 5001940
  have htrace : WordTrace (prefixWord ++ tailWord_5001940) baseStart_5001940 baseEnd_5001940 := by
    simpa [prefixWord, tailWord_5001940, baseEnd_5001940] using wordTrace_append hprefix tailTrace_5001940
  have hstable : (prefixWord ++ tailWord_5001940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001940).length < 2 ^ (prefixWord ++ tailWord_5001940).sum := by decide
  have hdescent : baseEnd_5001940 < baseStart_5001940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001953 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_5001953 : Nat := 118140960795 + 5001953 * 2 ^ 59
def prefixEnd_5001953 : Nat := 4983230072969 + 3 ^ 40 * 5001953 * 2
def baseEnd_5001953 : Nat := 2568406100198773569583943

theorem tailTrace_5001953 : CollatzResearch.WordTrace tailWord_5001953 prefixEnd_5001953 2568406100198773569583943 := by
  unfold tailWord_5001953
  simp only [CollatzResearch.WordTrace]
  refine ⟨182436213647786021405954513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121624142431857347603969675 182436213647786021405954513)
  ·
    refine ⟨136827160235839516054465885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182436213647786021405954513 136827160235839516054465885)
    ·
      refine ⟨51310185088439818520424707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136827160235839516054465885 51310185088439818520424707)
      ·
        refine ⟨76965277632659727780637061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51310185088439818520424707 76965277632659727780637061)
        ·
          refine ⟨14430989556123698958869449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76965277632659727780637061 14430989556123698958869449)
          ·
            refine ⟨10823242167092774219152087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14430989556123698958869449 10823242167092774219152087)
            ·
              refine ⟨16234863250639161328728131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10823242167092774219152087 16234863250639161328728131)
              ·
                refine ⟨24352294875958741993092197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16234863250639161328728131 24352294875958741993092197)
                ·
                  refine ⟨4566055289242264123704787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24352294875958741993092197 4566055289242264123704787)
                  ·
                    refine ⟨6849082933863396185557181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566055289242264123704787 6849082933863396185557181)
                    ·
                      refine ⟨2568406100198773569583943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849082933863396185557181 2568406100198773569583943)
                      ·
                        rfl

theorem cell23_5001953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_5001953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001953 prefixEnd_5001953 := by exact prefixLift 5001953
  have htrace : WordTrace (prefixWord ++ tailWord_5001953) baseStart_5001953 baseEnd_5001953 := by
    simpa [prefixWord, tailWord_5001953, baseEnd_5001953] using wordTrace_append hprefix tailTrace_5001953
  have hstable : (prefixWord ++ tailWord_5001953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001953).length < 2 ^ (prefixWord ++ tailWord_5001953).sum := by decide
  have hdescent : baseEnd_5001953 < baseStart_5001953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001969 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 2, 6]
def baseStart_5001969 : Nat := 118140960795 + 5001969 * 2 ^ 59
def prefixEnd_5001969 : Nat := 4983230072969 + 3 ^ 40 * 5001969 * 2
def baseEnd_5001969 : Nat := 856138105296415168994623

theorem tailTrace_5001969 : CollatzResearch.WordTrace tailWord_5001969 prefixEnd_5001969 856138105296415168994623 := by
  unfold tailWord_5001969
  simp only [CollatzResearch.WordTrace]
  refine ⟨182436797215728056138536961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121624531477152037425691307 182436797215728056138536961)
  ·
    refine ⟨136827597911796042103902721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182436797215728056138536961 136827597911796042103902721)
    ·
      refine ⟨102620698433847031577927041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136827597911796042103902721 102620698433847031577927041)
      ·
        refine ⟨76965523825385273683445281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102620698433847031577927041 76965523825385273683445281)
        ·
          refine ⟨57724142869038955262583961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76965523825385273683445281 57724142869038955262583961)
          ·
            refine ⟨43293107151779216446937971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57724142869038955262583961 43293107151779216446937971)
            ·
              refine ⟨64939660727668824670406957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43293107151779216446937971 64939660727668824670406957)
              ·
                refine ⟨24352372772875809251402609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64939660727668824670406957 24352372772875809251402609)
                ·
                  refine ⟨18264279579656856938551957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24352372772875809251402609 18264279579656856938551957)
                  ·
                    refine ⟨856138105296415168994623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18264279579656856938551957 856138105296415168994623)
                    ·
                      rfl

theorem cell23_5001969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_5001969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001969 prefixEnd_5001969 := by exact prefixLift 5001969
  have htrace : WordTrace (prefixWord ++ tailWord_5001969) baseStart_5001969 baseEnd_5001969 := by
    simpa [prefixWord, tailWord_5001969, baseEnd_5001969] using wordTrace_append hprefix tailTrace_5001969
  have hstable : (prefixWord ++ tailWord_5001969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001969).length < 2 ^ (prefixWord ++ tailWord_5001969).sum := by decide
  have hdescent : baseEnd_5001969 < baseStart_5001969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001979 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 3]
def baseStart_5001979 : Nat := 118140960795 + 5001979 * 2 ^ 59
def prefixEnd_5001979 : Nat := 4983230072969 + 3 ^ 40 * 5001979 * 2
def baseEnd_5001979 : Nat := 2568419450695790467858823

theorem tailTrace_5001979 : CollatzResearch.WordTrace tailWord_5001979 prefixEnd_5001979 2568419450695790467858823 := by
  unfold tailWord_5001979
  simp only [CollatzResearch.WordTrace]
  refine ⟨182437161945691827846400991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121624774630461218564267327 182437161945691827846400991)
  ·
    refine ⟨273655742918537741769601487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182437161945691827846400991 273655742918537741769601487)
    ·
      refine ⟨410483614377806612654402231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273655742918537741769601487 410483614377806612654402231)
      ·
        refine ⟨615725421566709918981603347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410483614377806612654402231 615725421566709918981603347)
        ·
          refine ⟨923588132350064878472405021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615725421566709918981603347 923588132350064878472405021)
          ·
            refine ⟨346345549631274329427151883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 923588132350064878472405021 346345549631274329427151883)
            ·
              refine ⟨519518324446911494140727825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346345549631274329427151883 519518324446911494140727825)
              ·
                refine ⟨389638743335183620605545869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519518324446911494140727825 389638743335183620605545869)
                ·
                  refine ⟨146114528750693857727079701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389638743335183620605545869 146114528750693857727079701)
                  ·
                    refine ⟨6849118535188774580956861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 146114528750693857727079701 6849118535188774580956861)
                    ·
                      refine ⟨2568419450695790467858823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849118535188774580956861 2568419450695790467858823)
                      ·
                        rfl

theorem cell23_5001979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 3].length) (baseStart_5001979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001979 prefixEnd_5001979 := by exact prefixLift 5001979
  have htrace : WordTrace (prefixWord ++ tailWord_5001979) baseStart_5001979 baseEnd_5001979 := by
    simpa [prefixWord, tailWord_5001979, baseEnd_5001979] using wordTrace_append hprefix tailTrace_5001979
  have hstable : (prefixWord ++ tailWord_5001979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001979).length < 2 ^ (prefixWord ++ tailWord_5001979).sum := by decide
  have hdescent : baseEnd_5001979 < baseStart_5001979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001980 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_5001980 : Nat := 118140960795 + 5001980 * 2 ^ 59
def prefixEnd_5001980 : Nat := 4983230072969 + 3 ^ 40 * 5001980 * 2
def baseEnd_5001980 : Nat := 2568419964176444963946319

theorem tailTrace_5001980 : CollatzResearch.WordTrace tailWord_5001980 prefixEnd_5001980 2568419964176444963946319 := by
  unfold tailWord_5001980
  simp only [CollatzResearch.WordTrace]
  refine ⟨91218599209344102508593697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121624798945792136678124929 91218599209344102508593697)
  ·
    refine ⟨68413949407008076881445273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91218599209344102508593697 68413949407008076881445273)
    ·
      refine ⟨51310462055256057661083955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68413949407008076881445273 51310462055256057661083955)
      ·
        refine ⟨76965693082884086491625933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51310462055256057661083955 76965693082884086491625933)
        ·
          refine ⟨28862134906081532434359725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76965693082884086491625933 28862134906081532434359725)
          ·
            refine ⟨10823300589780574662884897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28862134906081532434359725 10823300589780574662884897)
            ·
              refine ⟨8117475442335430997163673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10823300589780574662884897 8117475442335430997163673)
              ·
                refine ⟨6088106581751573247872755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8117475442335430997163673 6088106581751573247872755)
                ·
                  refine ⟨9132159872627359871809133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088106581751573247872755 9132159872627359871809133)
                  ·
                    refine ⟨3424559952235259951928425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9132159872627359871809133 3424559952235259951928425)
                    ·
                      refine ⟨2568419964176444963946319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424559952235259951928425 2568419964176444963946319)
                      ·
                        rfl

theorem cell23_5001980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_5001980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001980 prefixEnd_5001980 := by exact prefixLift 5001980
  have htrace : WordTrace (prefixWord ++ tailWord_5001980) baseStart_5001980 baseEnd_5001980 := by
    simpa [prefixWord, tailWord_5001980, baseEnd_5001980] using wordTrace_append hprefix tailTrace_5001980
  have hstable : (prefixWord ++ tailWord_5001980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001980).length < 2 ^ (prefixWord ++ tailWord_5001980).sum := by decide
  have hdescent : baseEnd_5001980 < baseStart_5001980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001989 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_5001989 : Nat := 118140960795 + 5001989 * 2 ^ 59
def prefixEnd_5001989 : Nat := 4983230072969 + 3 ^ 40 * 5001989 * 2
def baseEnd_5001989 : Nat := 2568424585502335428733777

theorem tailTrace_5001989 : CollatzResearch.WordTrace tailWord_5001989 prefixEnd_5001989 2568424585502335428733777 := by
  unfold tailWord_5001989
  simp only [CollatzResearch.WordTrace]
  refine ⟨182437526675655599554265021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121625017783770399702843347 182437526675655599554265021)
  ·
    refine ⟨68414072503370849832849383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182437526675655599554265021 68414072503370849832849383)
    ·
      refine ⟨102621108755056274749274075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68414072503370849832849383 102621108755056274749274075)
      ·
        refine ⟨153931663132584412123911113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102621108755056274749274075 153931663132584412123911113)
        ·
          refine ⟨115448747349438309092933335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153931663132584412123911113 115448747349438309092933335)
          ·
            refine ⟨173173121024157463639400003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115448747349438309092933335 173173121024157463639400003)
            ·
              refine ⟨259759681536236195459100005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173173121024157463639400003 259759681536236195459100005)
              ·
                refine ⟨48704940288044286648581251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259759681536236195459100005 48704940288044286648581251)
                ·
                  refine ⟨73057410432066429972871877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48704940288044286648581251 73057410432066429972871877)
                  ·
                    refine ⟨13698264456012455619913477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73057410432066429972871877 13698264456012455619913477)
                    ·
                      refine ⟨2568424585502335428733777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13698264456012455619913477 2568424585502335428733777)
                      ·
                        rfl

theorem cell23_5001989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_5001989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001989 prefixEnd_5001989 := by exact prefixLift 5001989
  have htrace : WordTrace (prefixWord ++ tailWord_5001989) baseStart_5001989 baseEnd_5001989 := by
    simpa [prefixWord, tailWord_5001989, baseEnd_5001989] using wordTrace_append hprefix tailTrace_5001989
  have hstable : (prefixWord ++ tailWord_5001989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001989).length < 2 ^ (prefixWord ++ tailWord_5001989).sum := by decide
  have hdescent : baseEnd_5001989 < baseStart_5001989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001993 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 4, 2, 2]
def baseStart_5001993 : Nat := 118140960795 + 5001993 * 2 ^ 59
def prefixEnd_5001993 : Nat := 4983230072969 + 3 ^ 40 * 5001993 * 2
def baseEnd_5001993 : Nat := 2568426639424953413083759

theorem tailTrace_5001993 : CollatzResearch.WordTrace tailWord_5001993 prefixEnd_5001993 2568426639424953413083759 := by
  unfold tailWord_5001993
  simp only [CollatzResearch.WordTrace]
  refine ⟨182437672567641108237410633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121625115045094072158273755 182437672567641108237410633)
  ·
    refine ⟨136828254425730831178057975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182437672567641108237410633 136828254425730831178057975)
    ·
      refine ⟨205242381638596246767086963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136828254425730831178057975 205242381638596246767086963)
      ·
        refine ⟨307863572457894370150630445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205242381638596246767086963 307863572457894370150630445)
        ·
          refine ⟨115448839671710388806486417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307863572457894370150630445 115448839671710388806486417)
          ·
            refine ⟨86586629753782791604864813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115448839671710388806486417 86586629753782791604864813)
            ·
              refine ⟨32469986157668546851824305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86586629753782791604864813 32469986157668546851824305)
              ·
                refine ⟨24352489618251410138868229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32469986157668546851824305 24352489618251410138868229)
                ·
                  refine ⟨4566091803422139401037793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24352489618251410138868229 4566091803422139401037793)
                  ·
                    refine ⟨3424568852566604550778345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4566091803422139401037793 3424568852566604550778345)
                    ·
                      refine ⟨2568426639424953413083759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424568852566604550778345 2568426639424953413083759)
                      ·
                        rfl

theorem cell23_5001993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 2, 2].length) (baseStart_5001993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001993 prefixEnd_5001993 := by exact prefixLift 5001993
  have htrace : WordTrace (prefixWord ++ tailWord_5001993) baseStart_5001993 baseEnd_5001993 := by
    simpa [prefixWord, tailWord_5001993, baseEnd_5001993] using wordTrace_append hprefix tailTrace_5001993
  have hstable : (prefixWord ++ tailWord_5001993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001993).length < 2 ^ (prefixWord ++ tailWord_5001993).sum := by decide
  have hdescent : baseEnd_5001993 < baseStart_5001993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002010 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2]
def baseStart_5002010 : Nat := 118140960795 + 5002010 * 2 ^ 59
def prefixEnd_5002010 : Nat := 4983230072969 + 3 ^ 40 * 5002010 * 2
def baseEnd_5002010 : Nat := 2568435368596079846571181

theorem tailTrace_5002010 : CollatzResearch.WordTrace tailWord_5002010 prefixEnd_5002010 2568435368596079846571181 := by
  unfold tailWord_5002010
  simp only [CollatzResearch.WordTrace]
  refine ⟨45609573152144880035194871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121625528405719680093852989 45609573152144880035194871)
  ·
    refine ⟨68414359728217320052792307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45609573152144880035194871 68414359728217320052792307)
    ·
      refine ⟨102621539592325980079188461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68414359728217320052792307 102621539592325980079188461)
      ·
        refine ⟨38483077347122242529695673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102621539592325980079188461 38483077347122242529695673)
        ·
          refine ⟨28862308010341681897271755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38483077347122242529695673 28862308010341681897271755)
          ·
            refine ⟨43293462015512522845907633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28862308010341681897271755 43293462015512522845907633)
            ·
              refine ⟨32470096511634392134430725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43293462015512522845907633 32470096511634392134430725)
              ·
                refine ⟨6088143095931448525205761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32470096511634392134430725 6088143095931448525205761)
                ·
                  refine ⟨4566107321948586393904321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6088143095931448525205761 4566107321948586393904321)
                  ·
                    refine ⟨3424580491461439795428241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4566107321948586393904321 3424580491461439795428241)
                    ·
                      refine ⟨2568435368596079846571181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424580491461439795428241 2568435368596079846571181)
                      ·
                        rfl

theorem cell23_5002010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_5002010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002010 prefixEnd_5002010 := by exact prefixLift 5002010
  have htrace : WordTrace (prefixWord ++ tailWord_5002010) baseStart_5002010 baseEnd_5002010 := by
    simpa [prefixWord, tailWord_5002010, baseEnd_5002010] using wordTrace_append hprefix tailTrace_5002010
  have hstable : (prefixWord ++ tailWord_5002010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002010).length < 2 ^ (prefixWord ++ tailWord_5002010).sum := by decide
  have hdescent : baseEnd_5002010 < baseStart_5002010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002016 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 7]
def baseStart_5002016 : Nat := 118140960795 + 5002016 * 2 ^ 59
def prefixEnd_5002016 : Nat := 4983230072969 + 3 ^ 40 * 5002016 * 2
def baseEnd_5002016 : Nat := 285382049942222980344017

theorem tailTrace_5002016 : CollatzResearch.WordTrace tailWord_5002016 prefixEnd_5002016 285382049942222980344017 := by
  unfold tailWord_5002016
  simp only [CollatzResearch.WordTrace]
  refine ⟨91219255723278891582748951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121625674297705188776998601 91219255723278891582748951)
  ·
    refine ⟨136828883584918337374123427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91219255723278891582748951 136828883584918337374123427)
    ·
      refine ⟨205243325377377506061185141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136828883584918337374123427 205243325377377506061185141)
      ·
        refine ⟨19241561754129141193236107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205243325377377506061185141 19241561754129141193236107)
        ·
          refine ⟨28862342631193711789854161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19241561754129141193236107 28862342631193711789854161)
          ·
            refine ⟨21646756973395283842390621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28862342631193711789854161 21646756973395283842390621)
            ·
              refine ⟨8117533865023231440896483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21646756973395283842390621 8117533865023231440896483)
              ·
                refine ⟨12176300797534847161344725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8117533865023231440896483 12176300797534847161344725)
                ·
                  refine ⟨285382049942222980344017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12176300797534847161344725 285382049942222980344017)
                  ·
                    rfl

theorem cell23_5002016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 7].length) (baseStart_5002016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002016 prefixEnd_5002016 := by exact prefixLift 5002016
  have htrace : WordTrace (prefixWord ++ tailWord_5002016) baseStart_5002016 baseEnd_5002016 := by
    simpa [prefixWord, tailWord_5002016, baseEnd_5002016] using wordTrace_append hprefix tailTrace_5002016
  have hstable : (prefixWord ++ tailWord_5002016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002016).length < 2 ^ (prefixWord ++ tailWord_5002016).sum := by decide
  have hdescent : baseEnd_5002016 < baseStart_5002016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002039 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_5002039 : Nat := 118140960795 + 5002039 * 2 ^ 59
def prefixEnd_5002039 : Nat := 4983230072969 + 3 ^ 40 * 5002039 * 2
def baseEnd_5002039 : Nat := 2568450259535060233108547

theorem tailTrace_5002039 : CollatzResearch.WordTrace tailWord_5002039 prefixEnd_5002039 2568450259535060233108547 := by
  unfold tailWord_5002039
  simp only [CollatzResearch.WordTrace]
  refine ⟨182439350325474458093585171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121626233550316305395723447 182439350325474458093585171)
  ·
    refine ⟨273659025488211687140377757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182439350325474458093585171 273659025488211687140377757)
    ·
      refine ⟨102622134558079382677641659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273659025488211687140377757 102622134558079382677641659)
      ·
        refine ⟨153933201837119074016462489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102622134558079382677641659 153933201837119074016462489)
        ·
          refine ⟨115449901377839305512346867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153933201837119074016462489 115449901377839305512346867)
          ·
            refine ⟨173174852066758958268520301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115449901377839305512346867 173174852066758958268520301)
            ·
              refine ⟨64940569525034609350695113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173174852066758958268520301 64940569525034609350695113)
              ·
                refine ⟨48705427143775957013021335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64940569525034609350695113 48705427143775957013021335)
                ·
                  refine ⟨73058140715663935519532003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48705427143775957013021335 73058140715663935519532003)
                  ·
                    refine ⟨109587211073495903279298005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73058140715663935519532003 109587211073495903279298005)
                    ·
                      refine ⟨2568450259535060233108547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109587211073495903279298005 2568450259535060233108547)
                      ·
                        rfl

theorem cell23_5002039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_5002039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002039 prefixEnd_5002039 := by exact prefixLift 5002039
  have htrace : WordTrace (prefixWord ++ tailWord_5002039) baseStart_5002039 baseEnd_5002039 := by
    simpa [prefixWord, tailWord_5002039, baseEnd_5002039] using wordTrace_append hprefix tailTrace_5002039
  have hstable : (prefixWord ++ tailWord_5002039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002039).length < 2 ^ (prefixWord ++ tailWord_5002039).sum := by decide
  have hdescent : baseEnd_5002039 < baseStart_5002039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002083 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 1, 6, 2]
def baseStart_5002083 : Nat := 118140960795 + 5002083 * 2 ^ 59
def prefixEnd_5002083 : Nat := 4983230072969 + 3 ^ 40 * 5002083 * 2
def baseEnd_5002083 : Nat := 2568472852683858060958345

theorem tailTrace_5002083 : CollatzResearch.WordTrace tailWord_5002083 prefixEnd_5002083 2568472852683858060958345 := by
  unfold tailWord_5002083
  simp only [CollatzResearch.WordTrace]
  refine ⟨182440955137315053608186903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121627303424876702405457935 182440955137315053608186903)
  ·
    refine ⟨273661432705972580412280355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182440955137315053608186903 273661432705972580412280355)
    ·
      refine ⟨410492149058958870618420533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273661432705972580412280355 410492149058958870618420533)
      ·
        refine ⟨38483638974277394120476925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 410492149058958870618420533 38483638974277394120476925)
        ·
          refine ⟨14431364615354022795178847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38483638974277394120476925 14431364615354022795178847)
          ·
            refine ⟨21647046923031034192768271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14431364615354022795178847 21647046923031034192768271)
            ·
              refine ⟨32470570384546551289152407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21647046923031034192768271 32470570384546551289152407)
              ·
                refine ⟨48705855576819826933728611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32470570384546551289152407 48705855576819826933728611)
                ·
                  refine ⟨73058783365229740400592917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48705855576819826933728611 73058783365229740400592917)
                  ·
                    refine ⟨3424630470245144081277793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73058783365229740400592917 3424630470245144081277793)
                    ·
                      refine ⟨2568472852683858060958345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424630470245144081277793 2568472852683858060958345)
                      ·
                        rfl

theorem cell23_5002083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_5002083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002083 prefixEnd_5002083 := by exact prefixLift 5002083
  have htrace : WordTrace (prefixWord ++ tailWord_5002083) baseStart_5002083 baseEnd_5002083 := by
    simpa [prefixWord, tailWord_5002083, baseEnd_5002083] using wordTrace_append hprefix tailTrace_5002083
  have hstable : (prefixWord ++ tailWord_5002083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002083).length < 2 ^ (prefixWord ++ tailWord_5002083).sum := by decide
  have hdescent : baseEnd_5002083 < baseStart_5002083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002089 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 12]
def baseStart_5002089 : Nat := 118140960795 + 5002089 * 2 ^ 59
def prefixEnd_5002089 : Nat := 4983230072969 + 3 ^ 40 * 5002089 * 2
def baseEnd_5002089 : Nat := 285386214840865004164813

theorem tailTrace_5002089 : CollatzResearch.WordTrace tailWord_5002089 prefixEnd_5002089 285386214840865004164813 := by
  unfold tailWord_5002089
  simp only [CollatzResearch.WordTrace]
  refine ⟨182441173975293316632905321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121627449316862211088603547 182441173975293316632905321)
  ·
    refine ⟨136830880481469987474678991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182441173975293316632905321 136830880481469987474678991)
    ·
      refine ⟨205246320722204981212018487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136830880481469987474678991 205246320722204981212018487)
      ·
        refine ⟨307869481083307471818027731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205246320722204981212018487 307869481083307471818027731)
        ·
          refine ⟨461804221624961207727041597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307869481083307471818027731 461804221624961207727041597)
          ·
            refine ⟨173176583109360452897640599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461804221624961207727041597 173176583109360452897640599)
            ·
              refine ⟨259764874664040679346460899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173176583109360452897640599 259764874664040679346460899)
              ·
                refine ⟨389647311996061019019691349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259764874664040679346460899 389647311996061019019691349)
                ·
                  refine ⟨285386214840865004164813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 389647311996061019019691349 285386214840865004164813)
                  ·
                    rfl

theorem cell23_5002089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 12].length) (baseStart_5002089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002089 prefixEnd_5002089 := by exact prefixLift 5002089
  have htrace : WordTrace (prefixWord ++ tailWord_5002089) baseStart_5002089 baseEnd_5002089 := by
    simpa [prefixWord, tailWord_5002089, baseEnd_5002089] using wordTrace_append hprefix tailTrace_5002089
  have hstable : (prefixWord ++ tailWord_5002089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002089).length < 2 ^ (prefixWord ++ tailWord_5002089).sum := by decide
  have hdescent : baseEnd_5002089 < baseStart_5002089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002134 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5002134 : Nat := 118140960795 + 5002134 * 2 ^ 59
def prefixEnd_5002134 : Nat := 4983230072969 + 3 ^ 40 * 5002134 * 2
def baseEnd_5002134 : Nat := 2568499040197237361420611

theorem tailTrace_5002134 : CollatzResearch.WordTrace tailWord_5002134 prefixEnd_5002134 2568499040197237361420611 := by
  unfold tailWord_5002134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402675953758143082393341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121628543506753526212195637 11402675953758143082393341)
  ·
    refine ⟨4276003482659303655897503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11402675953758143082393341 4276003482659303655897503)
    ·
      refine ⟨6414005223988955483846255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4276003482659303655897503 6414005223988955483846255)
      ·
        refine ⟨9621007835983433225769383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6414005223988955483846255 9621007835983433225769383)
        ·
          refine ⟨14431511753975149838654075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9621007835983433225769383 14431511753975149838654075)
          ·
            refine ⟨21647267630962724757981113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14431511753975149838654075 21647267630962724757981113)
            ·
              refine ⟨16235450723222043568485835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21647267630962724757981113 16235450723222043568485835)
              ·
                refine ⟨24353176084833065352728753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16235450723222043568485835 24353176084833065352728753)
                ·
                  refine ⟨18264882063624799014546565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24353176084833065352728753 18264882063624799014546565)
                  ·
                    refine ⟨3424665386929649815227481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18264882063624799014546565 3424665386929649815227481)
                    ·
                      refine ⟨2568499040197237361420611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424665386929649815227481 2568499040197237361420611)
                      ·
                        rfl

theorem cell23_5002134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5002134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002134 prefixEnd_5002134 := by exact prefixLift 5002134
  have htrace : WordTrace (prefixWord ++ tailWord_5002134) baseStart_5002134 baseEnd_5002134 := by
    simpa [prefixWord, tailWord_5002134, baseEnd_5002134] using wordTrace_append hprefix tailTrace_5002134
  have hstable : (prefixWord ++ tailWord_5002134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002134).length < 2 ^ (prefixWord ++ tailWord_5002134).sum := by decide
  have hdescent : baseEnd_5002134 < baseStart_5002134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002153 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 1, 5]
def baseStart_5002153 : Nat := 118140960795 + 5002153 * 2 ^ 59
def prefixEnd_5002153 : Nat := 4983230072969 + 3 ^ 40 * 5002153 * 2
def baseEnd_5002153 : Nat := 856169598776557595694341

theorem tailTrace_5002153 : CollatzResearch.WordTrace tailWord_5002153 prefixEnd_5002153 856169598776557595694341 := by
  unfold tailWord_5002153
  simp only [CollatzResearch.WordTrace]
  refine ⟨182443508247061455563235113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121629005498040970375490075 182443508247061455563235113)
  ·
    refine ⟨136832631185296091672426335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182443508247061455563235113 136832631185296091672426335)
    ·
      refine ⟨205248946777944137508639503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136832631185296091672426335 205248946777944137508639503)
      ·
        refine ⟨307873420166916206262959255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205248946777944137508639503 307873420166916206262959255)
        ·
          refine ⟨461810130250374309394438883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307873420166916206262959255 461810130250374309394438883)
          ·
            refine ⟨692715195375561464091658325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461810130250374309394438883 692715195375561464091658325)
            ·
              refine ⟨8117756195807360907324121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 692715195375561464091658325 8117756195807360907324121)
              ·
                refine ⟨6088317146855520680493091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8117756195807360907324121 6088317146855520680493091)
                ·
                  refine ⟨9132475720283281020739637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088317146855520680493091 9132475720283281020739637)
                  ·
                    refine ⟨856169598776557595694341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9132475720283281020739637 856169598776557595694341)
                    ·
                      rfl

theorem cell23_5002153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_5002153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002153 prefixEnd_5002153 := by exact prefixLift 5002153
  have htrace : WordTrace (prefixWord ++ tailWord_5002153) baseStart_5002153 baseEnd_5002153 := by
    simpa [prefixWord, tailWord_5002153, baseEnd_5002153] using wordTrace_append hprefix tailTrace_5002153
  have hstable : (prefixWord ++ tailWord_5002153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002153).length < 2 ^ (prefixWord ++ tailWord_5002153).sum := by decide
  have hdescent : baseEnd_5002153 < baseStart_5002153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002167 : List Nat := [1, 1, 3, 1, 3, 1, 5, 3, 1, 1, 3]
def baseStart_5002167 : Nat := 118140960795 + 5002167 * 2 ^ 59
def prefixEnd_5002167 : Nat := 4983230072969 + 3 ^ 40 * 5002167 * 2
def baseEnd_5002167 : Nat := 2568515985058835732307959

theorem tailTrace_5002167 : CollatzResearch.WordTrace tailWord_5002167 prefixEnd_5002167 2568515985058835732307959 := by
  unfold tailWord_5002167
  simp only [CollatzResearch.WordTrace]
  refine ⟨182444018869010735954244755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121629345912673823969496503 182444018869010735954244755)
  ·
    refine ⟨273666028303516103931367133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182444018869010735954244755 273666028303516103931367133)
    ·
      refine ⟨102624760613818538974262675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273666028303516103931367133 102624760613818538974262675)
      ·
        refine ⟨153937140920727808461394013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102624760613818538974262675 153937140920727808461394013)
        ·
          refine ⟨57726427845272928173022755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153937140920727808461394013 57726427845272928173022755)
          ·
            refine ⟨86589641767909392259534133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57726427845272928173022755 86589641767909392259534133)
            ·
              refine ⟨8117778915741505524331325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86589641767909392259534133 8117778915741505524331325)
              ·
                refine ⟨3044167093403064571624247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8117778915741505524331325 3044167093403064571624247)
                ·
                  refine ⟨4566250640104596857436371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044167093403064571624247 4566250640104596857436371)
                  ·
                    refine ⟨6849375960156895286154557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566250640104596857436371 6849375960156895286154557)
                    ·
                      refine ⟨2568515985058835732307959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849375960156895286154557 2568515985058835732307959)
                      ·
                        rfl

theorem cell23_5002167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_5002167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002167 prefixEnd_5002167 := by exact prefixLift 5002167
  have htrace : WordTrace (prefixWord ++ tailWord_5002167) baseStart_5002167 baseEnd_5002167 := by
    simpa [prefixWord, tailWord_5002167, baseEnd_5002167] using wordTrace_append hprefix tailTrace_5002167
  have hstable : (prefixWord ++ tailWord_5002167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002167).length < 2 ^ (prefixWord ++ tailWord_5002167).sum := by decide
  have hdescent : baseEnd_5002167 < baseStart_5002167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002183 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 4, 4]
def baseStart_5002183 : Nat := 118140960795 + 5002183 * 2 ^ 59
def prefixEnd_5002183 : Nat := 4983230072969 + 3 ^ 40 * 5002183 * 2
def baseEnd_5002183 : Nat := 856174733583102556569295

theorem tailTrace_5002183 : CollatzResearch.WordTrace tailWord_5002183 prefixEnd_5002183 856174733583102556569295 := by
  unfold tailWord_5002183
  simp only [CollatzResearch.WordTrace]
  refine ⟨182444602436952770686827203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121629734957968513791218135 182444602436952770686827203)
  ·
    refine ⟨273666903655429156030240805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182444602436952770686827203 273666903655429156030240805)
    ·
      refine ⟨51312544435392966755670151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273666903655429156030240805 51312544435392966755670151)
      ·
        refine ⟨76968816653089450133505227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51312544435392966755670151 76968816653089450133505227)
        ·
          refine ⟨115453224979634175200257841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76968816653089450133505227 115453224979634175200257841)
          ·
            refine ⟨86589918734725631400193381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115453224979634175200257841 86589918734725631400193381)
            ·
              refine ⟨16235609762761055887536259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86589918734725631400193381 16235609762761055887536259)
              ·
                refine ⟨24353414644141583831304389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16235609762761055887536259 24353414644141583831304389)
                ·
                  refine ⟨4566265245776546968369573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24353414644141583831304389 4566265245776546968369573)
                  ·
                    refine ⟨856174733583102556569295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566265245776546968369573 856174733583102556569295)
                    ·
                      rfl

theorem cell23_5002183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_5002183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002183 prefixEnd_5002183 := by exact prefixLift 5002183
  have htrace : WordTrace (prefixWord ++ tailWord_5002183) baseStart_5002183 baseEnd_5002183 := by
    simpa [prefixWord, tailWord_5002183, baseEnd_5002183] using wordTrace_append hprefix tailTrace_5002183
  have hstable : (prefixWord ++ tailWord_5002183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002183).length < 2 ^ (prefixWord ++ tailWord_5002183).sum := by decide
  have hdescent : baseEnd_5002183 < baseStart_5002183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002184 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_5002184 : Nat := 118140960795 + 5002184 * 2 ^ 59
def prefixEnd_5002184 : Nat := 4983230072969 + 3 ^ 40 * 5002184 * 2
def baseEnd_5002184 : Nat := 2568524714229962165795381

theorem tailTrace_5002184 : CollatzResearch.WordTrace tailWord_5002184 prefixEnd_5002184 2568524714229962165795381 := by
  unfold tailWord_5002184
  simp only [CollatzResearch.WordTrace]
  refine ⟨91222319454974573928806803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121629759273299431905075737 91222319454974573928806803)
  ·
    refine ⟨136833479182461860893210205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91222319454974573928806803 136833479182461860893210205)
    ·
      refine ⟨51312554693423197834953827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136833479182461860893210205 51312554693423197834953827)
      ·
        refine ⟨76968832040134796752430741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51312554693423197834953827 76968832040134796752430741)
        ·
          refine ⟨3607914001881318597770191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76968832040134796752430741 3607914001881318597770191)
          ·
            refine ⟨5411871002821977896655287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607914001881318597770191 5411871002821977896655287)
            ·
              refine ⟨8117806504232966844982931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411871002821977896655287 8117806504232966844982931)
              ·
                refine ⟨12176709756349450267474397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8117806504232966844982931 12176709756349450267474397)
                ·
                  refine ⟨4566266158631043850302899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12176709756349450267474397 4566266158631043850302899)
                  ·
                    refine ⟨6849399237946565775454349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566266158631043850302899 6849399237946565775454349)
                    ·
                      refine ⟨2568524714229962165795381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849399237946565775454349 2568524714229962165795381)
                      ·
                        rfl

theorem cell23_5002184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_5002184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002184 prefixEnd_5002184 := by exact prefixLift 5002184
  have htrace : WordTrace (prefixWord ++ tailWord_5002184) baseStart_5002184 baseEnd_5002184 := by
    simpa [prefixWord, tailWord_5002184, baseEnd_5002184] using wordTrace_append hprefix tailTrace_5002184
  have hstable : (prefixWord ++ tailWord_5002184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002184).length < 2 ^ (prefixWord ++ tailWord_5002184).sum := by decide
  have hdescent : baseEnd_5002184 < baseStart_5002184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002193 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_5002193 : Nat := 118140960795 + 5002193 * 2 ^ 59
def prefixEnd_5002193 : Nat := 4983230072969 + 3 ^ 40 * 5002193 * 2
def baseEnd_5002193 : Nat := 2568529335555852630582839

theorem tailTrace_5002193 : CollatzResearch.WordTrace tailWord_5002193 prefixEnd_5002193 2568529335555852630582839 := by
  unfold tailWord_5002193
  simp only [CollatzResearch.WordTrace]
  refine ⟨182444967166916542394691233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121629978111277694929794155 182444967166916542394691233)
  ·
    refine ⟨136833725375187406796018425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182444967166916542394691233 136833725375187406796018425)
    ·
      refine ⟨102625294031390555097013819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136833725375187406796018425 102625294031390555097013819)
      ·
        refine ⟨153937941047085832645520729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102625294031390555097013819 153937941047085832645520729)
        ·
          refine ⟨115453455785314374484140547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153937941047085832645520729 115453455785314374484140547)
          ·
            refine ⟨173180183677971561726210821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115453455785314374484140547 173180183677971561726210821)
            ·
              refine ⟨32471284439619667823664529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173180183677971561726210821 32471284439619667823664529)
              ·
                refine ⟨24353463329714750867748397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32471284439619667823664529 24353463329714750867748397)
                ·
                  refine ⟨9132548748643031575405649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24353463329714750867748397 9132548748643031575405649)
                  ·
                    refine ⟨6849411561482273681554237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9132548748643031575405649 6849411561482273681554237)
                    ·
                      refine ⟨2568529335555852630582839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849411561482273681554237 2568529335555852630582839)
                      ·
                        rfl

theorem cell23_5002193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_5002193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002193 prefixEnd_5002193 := by exact prefixLift 5002193
  have htrace : WordTrace (prefixWord ++ tailWord_5002193) baseStart_5002193 baseEnd_5002193 := by
    simpa [prefixWord, tailWord_5002193, baseEnd_5002193] using wordTrace_append hprefix tailTrace_5002193
  have hstable : (prefixWord ++ tailWord_5002193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002193).length < 2 ^ (prefixWord ++ tailWord_5002193).sum := by decide
  have hdescent : baseEnd_5002193 < baseStart_5002193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002200 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 2, 4]
def baseStart_5002200 : Nat := 118140960795 + 5002200 * 2 ^ 59
def prefixEnd_5002200 : Nat := 4983230072969 + 3 ^ 40 * 5002200 * 2
def baseEnd_5002200 : Nat := 856177643306811367731769

theorem tailTrace_5002200 : CollatzResearch.WordTrace tailWord_5002200 prefixEnd_5002200 856177643306811367731769 := by
  unfold tailWord_5002200
  simp only [CollatzResearch.WordTrace]
  refine ⟨91222611238945591295098027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121630148318594121726797369 91222611238945591295098027)
  ·
    refine ⟨136833916858418386942647041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91222611238945591295098027 136833916858418386942647041)
    ·
      refine ⟨102625437643813790206985281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136833916858418386942647041 102625437643813790206985281)
      ·
        refine ⟨76969078232860342655238961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102625437643813790206985281 76969078232860342655238961)
        ·
          refine ⟨57726808674645256991429221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76969078232860342655238961 57726808674645256991429221)
          ·
            refine ⟨10823776626495985685892979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57726808674645256991429221 10823776626495985685892979)
            ·
              refine ⟨16235664939743978528839469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10823776626495985685892979 16235664939743978528839469)
              ·
                refine ⟨6088374352403991948314801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16235664939743978528839469 6088374352403991948314801)
                ·
                  refine ⟨4566280764302993961236101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6088374352403991948314801 4566280764302993961236101)
                  ·
                    refine ⟨856177643306811367731769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566280764302993961236101 856177643306811367731769)
                    ·
                      rfl

theorem cell23_5002200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_5002200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002200 prefixEnd_5002200 := by exact prefixLift 5002200
  have htrace : WordTrace (prefixWord ++ tailWord_5002200) baseStart_5002200 baseEnd_5002200 := by
    simpa [prefixWord, tailWord_5002200, baseEnd_5002200] using wordTrace_append hprefix tailTrace_5002200
  have hstable : (prefixWord ++ tailWord_5002200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002200).length < 2 ^ (prefixWord ++ tailWord_5002200).sum := by decide
  have hdescent : baseEnd_5002200 < baseStart_5002200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002207 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 4]
def baseStart_5002207 : Nat := 118140960795 + 5002207 * 2 ^ 59
def prefixEnd_5002207 : Nat := 4983230072969 + 3 ^ 40 * 5002207 * 2
def baseEnd_5002207 : Nat := 2568536524285015575807775

theorem tailTrace_5002207 : CollatzResearch.WordTrace tailWord_5002207 prefixEnd_5002207 2568536524285015575807775 := by
  unfold tailWord_5002207
  simp only [CollatzResearch.WordTrace]
  refine ⟨182445477788865822785700875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121630318525910548523800583 182445477788865822785700875)
  ·
    refine ⟨273668216683298734178551313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182445477788865822785700875 273668216683298734178551313)
    ·
      refine ⟨205251162512474050633913485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273668216683298734178551313 205251162512474050633913485)
      ·
        refine ⟨76969185942177768987717557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205251162512474050633913485 76969185942177768987717557)
        ·
          refine ⟨7215861182079165842598521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76969185942177768987717557 7215861182079165842598521)
          ·
            refine ⟨5411895886559374381948891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7215861182079165842598521 5411895886559374381948891)
            ·
              refine ⟨8117843829839061572923337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411895886559374381948891 8117843829839061572923337)
              ·
                refine ⟨6088382872379296179692503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8117843829839061572923337 6088382872379296179692503)
                ·
                  refine ⟨9132574308568944269538755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088382872379296179692503 9132574308568944269538755)
                  ·
                    refine ⟨13698861462853416404308133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9132574308568944269538755 13698861462853416404308133)
                    ·
                      refine ⟨2568536524285015575807775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13698861462853416404308133 2568536524285015575807775)
                      ·
                        rfl

theorem cell23_5002207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_5002207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002207 prefixEnd_5002207 := by exact prefixLift 5002207
  have htrace : WordTrace (prefixWord ++ tailWord_5002207) baseStart_5002207 baseEnd_5002207 := by
    simpa [prefixWord, tailWord_5002207, baseEnd_5002207] using wordTrace_append hprefix tailTrace_5002207
  have hstable : (prefixWord ++ tailWord_5002207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002207).length < 2 ^ (prefixWord ++ tailWord_5002207).sum := by decide
  have hdescent : baseEnd_5002207 < baseStart_5002207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002223 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 3]
def baseStart_5002223 : Nat := 118140960795 + 5002223 * 2 ^ 59
def prefixEnd_5002223 : Nat := 4983230072969 + 3 ^ 40 * 5002223 * 2
def baseEnd_5002223 : Nat := 2568544739975487513207701

theorem tailTrace_5002223 : CollatzResearch.WordTrace tailWord_5002223 prefixEnd_5002223 2568544739975487513207701 := by
  unfold tailWord_5002223
  simp only [CollatzResearch.WordTrace]
  refine ⟨182446061356807857518283323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121630707571205238345522215 182446061356807857518283323)
  ·
    refine ⟨273669092035211786277424985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182446061356807857518283323 273669092035211786277424985)
    ·
      refine ⟨205251819026408839708068739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273669092035211786277424985 205251819026408839708068739)
      ·
        refine ⟨307877728539613259562103109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205251819026408839708068739 307877728539613259562103109)
        ·
          refine ⟨57727074101177486167894333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307877728539613259562103109 57727074101177486167894333)
          ·
            refine ⟨21647652787941557312960375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57727074101177486167894333 21647652787941557312960375)
            ·
              refine ⟨32471479181912335969440563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21647652787941557312960375 32471479181912335969440563)
              ·
                refine ⟨48707218772868503954160845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32471479181912335969440563 48707218772868503954160845)
                ·
                  refine ⟨18265207039825688982810317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48707218772868503954160845 18265207039825688982810317)
                  ·
                    refine ⟨6849452639934633368553869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18265207039825688982810317 6849452639934633368553869)
                    ·
                      refine ⟨2568544739975487513207701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849452639934633368553869 2568544739975487513207701)
                      ·
                        rfl

theorem cell23_5002223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_5002223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002223 prefixEnd_5002223 := by exact prefixLift 5002223
  have htrace : WordTrace (prefixWord ++ tailWord_5002223) baseStart_5002223 baseEnd_5002223 := by
    simpa [prefixWord, tailWord_5002223, baseEnd_5002223] using wordTrace_append hprefix tailTrace_5002223
  have hstable : (prefixWord ++ tailWord_5002223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002223).length < 2 ^ (prefixWord ++ tailWord_5002223).sum := by decide
  have hdescent : baseEnd_5002223 < baseStart_5002223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002241 : List Nat := [1, 2, 4, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_5002241 : Nat := 118140960795 + 5002241 * 2 ^ 59
def prefixEnd_5002241 : Nat := 4983230072969 + 3 ^ 40 * 5002241 * 2
def baseEnd_5002241 : Nat := 2568553982627268442782619

theorem tailTrace_5002241 : CollatzResearch.WordTrace tailWord_5002241 prefixEnd_5002241 2568553982627268442782619 := by
  unfold tailWord_5002241
  simp only [CollatzResearch.WordTrace]
  refine ⟨182446717870742646592438577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121631145247161764394959051 182446717870742646592438577)
  ·
    refine ⟨136835038403056984944328933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182446717870742646592438577 136835038403056984944328933)
    ·
      refine ⟨25656569700573184677061675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136835038403056984944328933 25656569700573184677061675)
      ·
        refine ⟨38484854550859777015592513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25656569700573184677061675 38484854550859777015592513)
        ·
          refine ⟨28863640913144832761694385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38484854550859777015592513 28863640913144832761694385)
          ·
            refine ⟨21647730684858624571270789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28863640913144832761694385 21647730684858624571270789)
            ·
              refine ⟨4058949503410992107113273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21647730684858624571270789 4058949503410992107113273)
              ·
                refine ⟨3044212127558244080334955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4058949503410992107113273 3044212127558244080334955)
                ·
                  refine ⟨4566318191337366120502433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044212127558244080334955 4566318191337366120502433)
                  ·
                    refine ⟨3424738643503024590376825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4566318191337366120502433 3424738643503024590376825)
                    ·
                      refine ⟨2568553982627268442782619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424738643503024590376825 2568553982627268442782619)
                      ·
                        rfl

theorem cell23_5002241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_5002241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002241 prefixEnd_5002241 := by exact prefixLift 5002241
  have htrace : WordTrace (prefixWord ++ tailWord_5002241) baseStart_5002241 baseEnd_5002241 := by
    simpa [prefixWord, tailWord_5002241, baseEnd_5002241] using wordTrace_append hprefix tailTrace_5002241
  have hstable : (prefixWord ++ tailWord_5002241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002241).length < 2 ^ (prefixWord ++ tailWord_5002241).sum := by decide
  have hdescent : baseEnd_5002241 < baseStart_5002241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002258 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5002258 : Nat := 118140960795 + 5002258 * 2 ^ 59
def prefixEnd_5002258 : Nat := 4983230072969 + 3 ^ 40 * 5002258 * 2
def baseEnd_5002258 : Nat := 2568562711798394876270041

theorem tailTrace_5002258 : CollatzResearch.WordTrace tailWord_5002258 prefixEnd_5002258 2568562711798394876270041 := by
  unfold tailWord_5002258
  simp only [CollatzResearch.WordTrace]
  refine ⟨45611834477920264623951857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121631558607787372330538285 45611834477920264623951857)
  ·
    refine ⟨34208875858440198467963893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45611834477920264623951857 34208875858440198467963893)
    ·
      refine ⟨3207082111728768606371615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34208875858440198467963893 3207082111728768606371615)
      ·
        refine ⟨4810623167593152909557423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3207082111728768606371615 4810623167593152909557423)
        ·
          refine ⟨7215934751389729364336135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4810623167593152909557423 7215934751389729364336135)
          ·
            refine ⟨10823902127084594046504203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215934751389729364336135 10823902127084594046504203)
            ·
              refine ⟨16235853190626891069756305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10823902127084594046504203 16235853190626891069756305)
              ·
                refine ⟨12176889892970168302317229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16235853190626891069756305 12176889892970168302317229)
                ·
                  refine ⟨4566333709863813113368961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12176889892970168302317229 4566333709863813113368961)
                  ·
                    refine ⟨3424750282397859835026721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4566333709863813113368961 3424750282397859835026721)
                    ·
                      refine ⟨2568562711798394876270041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424750282397859835026721 2568562711798394876270041)
                      ·
                        rfl

theorem cell23_5002258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5002258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002258 prefixEnd_5002258 := by exact prefixLift 5002258
  have htrace : WordTrace (prefixWord ++ tailWord_5002258) baseStart_5002258 baseEnd_5002258 := by
    simpa [prefixWord, tailWord_5002258, baseEnd_5002258] using wordTrace_append hprefix tailTrace_5002258
  have hstable : (prefixWord ++ tailWord_5002258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002258).length < 2 ^ (prefixWord ++ tailWord_5002258).sum := by decide
  have hdescent : baseEnd_5002258 < baseStart_5002258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002313 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 3]
def baseStart_5002313 : Nat := 118140960795 + 5002313 * 2 ^ 59
def prefixEnd_5002313 : Nat := 4983230072969 + 3 ^ 40 * 5002313 * 2
def baseEnd_5002313 : Nat := 2568590953234392161082287

theorem tailTrace_5002313 : CollatzResearch.WordTrace tailWord_5002313 prefixEnd_5002313 2568590953234392161082287 := by
  unfold tailWord_5002313
  simp only [CollatzResearch.WordTrace]
  refine ⟨182449343926481802889059593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121632895950987868592706395 182449343926481802889059593)
  ·
    refine ⟨136837007944861352166794695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182449343926481802889059593 136837007944861352166794695)
    ·
      refine ⟨205255511917292028250192043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136837007944861352166794695 205255511917292028250192043)
      ·
        refine ⟨307883267875938042375288065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205255511917292028250192043 307883267875938042375288065)
        ·
          refine ⟨230912450906953531781466049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307883267875938042375288065 230912450906953531781466049)
          ·
            refine ⟨173184338180215148836099537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230912450906953531781466049 173184338180215148836099537)
            ·
              refine ⟨129888253635161361627074653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173184338180215148836099537 129888253635161361627074653)
              ·
                refine ⟨48708095113185510610152995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129888253635161361627074653 48708095113185510610152995)
                ·
                  refine ⟨73062142669778265915229493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48708095113185510610152995 73062142669778265915229493)
                  ·
                    refine ⟨6849575875291712429552765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73062142669778265915229493 6849575875291712429552765)
                    ·
                      refine ⟨2568590953234392161082287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849575875291712429552765 2568590953234392161082287)
                      ·
                        rfl

theorem cell23_5002313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_5002313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002313 prefixEnd_5002313 := by exact prefixLift 5002313
  have htrace : WordTrace (prefixWord ++ tailWord_5002313) baseStart_5002313 baseEnd_5002313 := by
    simpa [prefixWord, tailWord_5002313, baseEnd_5002313] using wordTrace_append hprefix tailTrace_5002313
  have hstable : (prefixWord ++ tailWord_5002313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002313).length < 2 ^ (prefixWord ++ tailWord_5002313).sum := by decide
  have hdescent : baseEnd_5002313 < baseStart_5002313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002334 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5002334 : Nat := 118140960795 + 5002334 * 2 ^ 59
def prefixEnd_5002334 : Nat := 4983230072969 + 3 ^ 40 * 5002334 * 2
def baseEnd_5002334 : Nat := 2568601736328136578919691

theorem tailTrace_5002334 : CollatzResearch.WordTrace tailWord_5002334 prefixEnd_5002334 2568601736328136578919691 := by
  unfold tailWord_5002334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22806263732425715434446757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121633406572937148983716037 22806263732425715434446757)
  ·
    refine ⟨4276174449829821643958767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22806263732425715434446757 4276174449829821643958767)
    ·
      refine ⟨6414261674744732465938151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4276174449829821643958767 6414261674744732465938151)
      ·
        refine ⟨9621392512117098698907227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6414261674744732465938151 9621392512117098698907227)
        ·
          refine ⟨14432088768175648048360841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9621392512117098698907227 14432088768175648048360841)
          ·
            refine ⟨10824066576131736036270631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14432088768175648048360841 10824066576131736036270631)
            ·
              refine ⟨16236099864197604054405947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10824066576131736036270631 16236099864197604054405947)
              ·
                refine ⟨24354149796296406081608921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16236099864197604054405947 24354149796296406081608921)
                ·
                  refine ⟨18265612347222304561206691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24354149796296406081608921 18265612347222304561206691)
                  ·
                    refine ⟨27398418520833456841810037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18265612347222304561206691 27398418520833456841810037)
                    ·
                      refine ⟨2568601736328136578919691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27398418520833456841810037 2568601736328136578919691)
                      ·
                        rfl

theorem cell23_5002334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5002334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002334 prefixEnd_5002334 := by exact prefixLift 5002334
  have htrace : WordTrace (prefixWord ++ tailWord_5002334) baseStart_5002334 baseEnd_5002334 := by
    simpa [prefixWord, tailWord_5002334, baseEnd_5002334] using wordTrace_append hprefix tailTrace_5002334
  have hstable : (prefixWord ++ tailWord_5002334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002334).length < 2 ^ (prefixWord ++ tailWord_5002334).sum := by decide
  have hdescent : baseEnd_5002334 < baseStart_5002334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002340 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_5002340 : Nat := 118140960795 + 5002340 * 2 ^ 59
def prefixEnd_5002340 : Nat := 4983230072969 + 3 ^ 40 * 5002340 * 2
def baseEnd_5002340 : Nat := 2568604817212063555444663

theorem tailTrace_5002340 : CollatzResearch.WordTrace tailWord_5002340 prefixEnd_5002340 2568604817212063555444663 := by
  unfold tailWord_5002340
  simp only [CollatzResearch.WordTrace]
  refine ⟨91225164348691993250146237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121633552464922657666861649 91225164348691993250146237)
  ·
    refine ⟨34209436630759497468804839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91225164348691993250146237 34209436630759497468804839)
    ·
      refine ⟨51314154946139246203207259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34209436630759497468804839 51314154946139246203207259)
      ·
        refine ⟨76971232419208869304810889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51314154946139246203207259 76971232419208869304810889)
        ·
          refine ⟨57728424314406651978608167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76971232419208869304810889 57728424314406651978608167)
          ·
            refine ⟨86592636471609977967912251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57728424314406651978608167 86592636471609977967912251)
            ·
              refine ⟨129888954707414966951868377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86592636471609977967912251 129888954707414966951868377)
              ·
                refine ⟨97416716030561225213901283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129888954707414966951868377 97416716030561225213901283)
                ·
                  refine ⟨146125074045841837820851925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97416716030561225213901283 146125074045841837820851925)
                  ·
                    refine ⟨3424806422949418073926217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 146125074045841837820851925 3424806422949418073926217)
                    ·
                      refine ⟨2568604817212063555444663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424806422949418073926217 2568604817212063555444663)
                      ·
                        rfl

theorem cell23_5002340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_5002340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002340 prefixEnd_5002340 := by exact prefixLift 5002340
  have htrace : WordTrace (prefixWord ++ tailWord_5002340) baseStart_5002340 baseEnd_5002340 := by
    simpa [prefixWord, tailWord_5002340, baseEnd_5002340] using wordTrace_append hprefix tailTrace_5002340
  have hstable : (prefixWord ++ tailWord_5002340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002340).length < 2 ^ (prefixWord ++ tailWord_5002340).sum := by decide
  have hdescent : baseEnd_5002340 < baseStart_5002340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002350 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_5002350 : Nat := 118140960795 + 5002350 * 2 ^ 59
def prefixEnd_5002350 : Nat := 4983230072969 + 3 ^ 40 * 5002350 * 2
def baseEnd_5002350 : Nat := 856203317339536172106539

theorem tailTrace_5002350 : CollatzResearch.WordTrace tailWord_5002350 prefixEnd_5002350 856203317339536172106539 := by
  unfold tailWord_5002350
  simp only [CollatzResearch.WordTrace]
  refine ⟨22806336678418469776019563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121633795618231838805437669 22806336678418469776019563)
  ·
    refine ⟨34209505017627704664029345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22806336678418469776019563 34209505017627704664029345)
    ·
      refine ⟨25657128763220778498022009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34209505017627704664029345 25657128763220778498022009)
      ·
        refine ⟨19242846572415583873516507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25657128763220778498022009 19242846572415583873516507)
        ·
          refine ⟨28864269858623375810274761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19242846572415583873516507 28864269858623375810274761)
          ·
            refine ⟨21648202393967531857706071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28864269858623375810274761 21648202393967531857706071)
            ·
              refine ⟨32472303590951297786559107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21648202393967531857706071 32472303590951297786559107)
              ·
                refine ⟨48708455386426946679838661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32472303590951297786559107 48708455386426946679838661)
                ·
                  refine ⟨9132835384955052502469749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48708455386426946679838661 9132835384955052502469749)
                  ·
                    refine ⟨856203317339536172106539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9132835384955052502469749 856203317339536172106539)
                    ·
                      rfl

theorem cell23_5002350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_5002350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002350 prefixEnd_5002350 := by exact prefixLift 5002350
  have htrace : WordTrace (prefixWord ++ tailWord_5002350) baseStart_5002350 baseEnd_5002350 := by
    simpa [prefixWord, tailWord_5002350, baseEnd_5002350] using wordTrace_append hprefix tailTrace_5002350
  have hstable : (prefixWord ++ tailWord_5002350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002350).length < 2 ^ (prefixWord ++ tailWord_5002350).sum := by decide
  have hdescent : baseEnd_5002350 < baseStart_5002350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002353 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_5002353 : Nat := 118140960795 + 5002353 * 2 ^ 59
def prefixEnd_5002353 : Nat := 4983230072969 + 3 ^ 40 * 5002353 * 2
def baseEnd_5002353 : Nat := 2568611492460572004582103

theorem tailTrace_5002353 : CollatzResearch.WordTrace tailWord_5002353 prefixEnd_5002353 2568611492460572004582103 := by
  unfold tailWord_5002353
  simp only [CollatzResearch.WordTrace]
  refine ⟨182450802846336889720515713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121633868564224593147010475 182450802846336889720515713)
  ·
    refine ⟨136838102134752667290386785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182450802846336889720515713 136838102134752667290386785)
    ·
      refine ⟨102628576601064500467790089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136838102134752667290386785 102628576601064500467790089)
      ·
        refine ⟨76971432450798375350842567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102628576601064500467790089 76971432450798375350842567)
        ·
          refine ⟨115457148676197563026263851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76971432450798375350842567 115457148676197563026263851)
          ·
            refine ⟨173185723014296344539395777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115457148676197563026263851 173185723014296344539395777)
            ·
              refine ⟨129889292260722258404546833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173185723014296344539395777 129889292260722258404546833)
              ·
                refine ⟨97416969195541693803410125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129889292260722258404546833 97416969195541693803410125)
                ·
                  refine ⟨36531363448328135176278797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97416969195541693803410125 36531363448328135176278797)
                  ·
                    refine ⟨13699261293123050691104549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36531363448328135176278797 13699261293123050691104549)
                    ·
                      refine ⟨2568611492460572004582103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13699261293123050691104549 2568611492460572004582103)
                      ·
                        rfl

theorem cell23_5002353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_5002353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002353 prefixEnd_5002353 := by exact prefixLift 5002353
  have htrace : WordTrace (prefixWord ++ tailWord_5002353) baseStart_5002353 baseEnd_5002353 := by
    simpa [prefixWord, tailWord_5002353, baseEnd_5002353] using wordTrace_append hprefix tailTrace_5002353
  have hstable : (prefixWord ++ tailWord_5002353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002353).length < 2 ^ (prefixWord ++ tailWord_5002353).sum := by decide
  have hdescent : baseEnd_5002353 < baseStart_5002353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002380 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_5002380 : Nat := 118140960795 + 5002380 * 2 ^ 59
def prefixEnd_5002380 : Nat := 4983230072969 + 3 ^ 40 * 5002380 * 2
def baseEnd_5002380 : Nat := 856208452146081132981493

theorem tailTrace_5002380 : CollatzResearch.WordTrace tailWord_5002380 prefixEnd_5002380 856208452146081132981493 := by
  unfold tailWord_5002380
  simp only [CollatzResearch.WordTrace]
  refine ⟨91225893808619536665874297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121634525078159382221165729 91225893808619536665874297)
  ·
    refine ⟨68419420356464652499405723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91225893808619536665874297 68419420356464652499405723)
    ·
      refine ⟨102629130534696978749108585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68419420356464652499405723 102629130534696978749108585)
      ·
        refine ⟨76971847901022734061831439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102629130534696978749108585 76971847901022734061831439)
        ·
          refine ⟨115457771851534101092747159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76971847901022734061831439 115457771851534101092747159)
          ·
            refine ⟨173186657777301151639120739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115457771851534101092747159 173186657777301151639120739)
            ·
              refine ⟨259779986665951727458681109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173186657777301151639120739 259779986665951727458681109)
              ·
                refine ⟨12177186874966487224625677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 259779986665951727458681109 12177186874966487224625677)
                ·
                  refine ⟨4566445078112432709234629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12177186874966487224625677 4566445078112432709234629)
                  ·
                    refine ⟨856208452146081132981493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566445078112432709234629 856208452146081132981493)
                    ·
                      rfl

theorem cell23_5002380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_5002380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002380 prefixEnd_5002380 := by exact prefixLift 5002380
  have htrace : WordTrace (prefixWord ++ tailWord_5002380) baseStart_5002380 baseEnd_5002380 := by
    simpa [prefixWord, tailWord_5002380, baseEnd_5002380] using wordTrace_append hprefix tailTrace_5002380
  have hstable : (prefixWord ++ tailWord_5002380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002380).length < 2 ^ (prefixWord ++ tailWord_5002380).sum := by decide
  have hdescent : baseEnd_5002380 < baseStart_5002380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002440 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 3, 5]
def baseStart_5002440 : Nat := 118140960795 + 5002440 * 2 ^ 59
def prefixEnd_5002440 : Nat := 4983230072969 + 3 ^ 40 * 5002440 * 2
def baseEnd_5002440 : Nat := 856218721759171054731401

theorem tailTrace_5002440 : CollatzResearch.WordTrace tailWord_5002440 prefixEnd_5002440 856218721759171054731401 := by
  unfold tailWord_5002440
  simp only [CollatzResearch.WordTrace]
  refine ⟨91226987998510851789466387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121635983998014469052621849 91226987998510851789466387)
  ·
    refine ⟨136840481997766277684199581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91226987998510851789466387 136840481997766277684199581)
    ·
      refine ⟨51315180749162354131574843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136840481997766277684199581 51315180749162354131574843)
      ·
        refine ⟨76972771123743531197362265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51315180749162354131574843 76972771123743531197362265)
        ·
          refine ⟨57729578342807648398021699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76972771123743531197362265 57729578342807648398021699)
          ·
            refine ⟨86594367514211472597032549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57729578342807648398021699 86594367514211472597032549)
            ·
              refine ⟨16236443908914651111943603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86594367514211472597032549 16236443908914651111943603)
              ·
                refine ⟨24354665863371976667915405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16236443908914651111943603 24354665863371976667915405)
                ·
                  refine ⟨9132999698764491250468277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24354665863371976667915405 9132999698764491250468277)
                  ·
                    refine ⟨856218721759171054731401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9132999698764491250468277 856218721759171054731401)
                    ·
                      rfl

theorem cell23_5002440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_5002440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002440 prefixEnd_5002440 := by exact prefixLift 5002440
  have htrace : WordTrace (prefixWord ++ tailWord_5002440) baseStart_5002440 baseEnd_5002440 := by
    simpa [prefixWord, tailWord_5002440, baseEnd_5002440] using wordTrace_append hprefix tailTrace_5002440
  have hstable : (prefixWord ++ tailWord_5002440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002440).length < 2 ^ (prefixWord ++ tailWord_5002440).sum := by decide
  have hdescent : baseEnd_5002440 < baseStart_5002440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002447 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 2, 3, 2]
def baseStart_5002447 : Nat := 118140960795 + 5002447 * 2 ^ 59
def prefixEnd_5002447 : Nat := 4983230072969 + 3 ^ 40 * 5002447 * 2
def baseEnd_5002447 : Nat := 2568659759642094636806671

theorem tailTrace_5002447 : CollatzResearch.WordTrace tailWord_5002447 prefixEnd_5002447 2568659759642094636806671 := by
  unfold tailWord_5002447
  simp only [CollatzResearch.WordTrace]
  refine ⟨182454231307996343774437595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121636154205330895849625063 182454231307996343774437595)
  ·
    refine ⟨273681346961994515661656393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182454231307996343774437595 273681346961994515661656393)
    ·
      refine ⟨205261010221495886746242295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273681346961994515661656393 205261010221495886746242295)
      ·
        refine ⟨307891515332243830119363443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205261010221495886746242295 307891515332243830119363443)
        ·
          refine ⟨461837272998365745179045165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307891515332243830119363443 461837272998365745179045165)
          ·
            refine ⟨173188977374387154442141937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461837272998365745179045165 173188977374387154442141937)
            ·
              refine ⟨129891733030790365831606453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173188977374387154442141937 129891733030790365831606453)
              ·
                refine ⟨12177349971636596796713105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129891733030790365831606453 12177349971636596796713105)
                ·
                  refine ⟨9133012478727447597534829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12177349971636596796713105 9133012478727447597534829)
                  ·
                    refine ⟨3424879679522792849075561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9133012478727447597534829 3424879679522792849075561)
                    ·
                      refine ⟨2568659759642094636806671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424879679522792849075561 2568659759642094636806671)
                      ·
                        rfl

theorem cell23_5002447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 3, 2].length) (baseStart_5002447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002447 prefixEnd_5002447 := by exact prefixLift 5002447
  have htrace : WordTrace (prefixWord ++ tailWord_5002447) baseStart_5002447 baseEnd_5002447 := by
    simpa [prefixWord, tailWord_5002447, baseEnd_5002447] using wordTrace_append hprefix tailTrace_5002447
  have hstable : (prefixWord ++ tailWord_5002447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002447).length < 2 ^ (prefixWord ++ tailWord_5002447).sum := by decide
  have hdescent : baseEnd_5002447 < baseStart_5002447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002461 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 6]
def baseStart_5002461 : Nat := 118140960795 + 5002461 * 2 ^ 59
def prefixEnd_5002461 : Nat := 4983230072969 + 3 ^ 40 * 5002461 * 2
def baseEnd_5002461 : Nat := 285407438707917509114623

theorem tailTrace_5002461 : CollatzResearch.WordTrace tailWord_5002461 prefixEnd_5002461 285407438707917509114623 := by
  unfold tailWord_5002461
  simp only [CollatzResearch.WordTrace]
  refine ⟨182454741929945624165447237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121636494619963749443631491 182454741929945624165447237)
  ·
    refine ⟨34210264111864804531021357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182454741929945624165447237 34210264111864804531021357)
    ·
      refine ⟨12828849041949301699133009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34210264111864804531021357 12828849041949301699133009)
      ·
        refine ⟨9621636781461976274349757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12828849041949301699133009 9621636781461976274349757)
        ·
          refine ⟨3608113793048241102881159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9621636781461976274349757 3608113793048241102881159)
          ·
            refine ⟨5412170689572361654321739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608113793048241102881159 5412170689572361654321739)
            ·
              refine ⟨8118256034358542481482609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412170689572361654321739 8118256034358542481482609)
              ·
                refine ⟨6088692025768906861111957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8118256034358542481482609 6088692025768906861111957)
                ·
                  refine ⟨285407438707917509114623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6088692025768906861111957 285407438707917509114623)
                  ·
                    rfl

theorem cell23_5002461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_5002461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002461 prefixEnd_5002461 := by exact prefixLift 5002461
  have htrace : WordTrace (prefixWord ++ tailWord_5002461) baseStart_5002461 baseEnd_5002461 := by
    simpa [prefixWord, tailWord_5002461, baseEnd_5002461] using wordTrace_append hprefix tailTrace_5002461
  have hstable : (prefixWord ++ tailWord_5002461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002461).length < 2 ^ (prefixWord ++ tailWord_5002461).sum := by decide
  have hdescent : baseEnd_5002461 < baseStart_5002461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002471 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5002471 : Nat := 118140960795 + 5002471 * 2 ^ 59
def prefixEnd_5002471 : Nat := 4983230072969 + 3 ^ 40 * 5002471 * 2
def baseEnd_5002471 : Nat := 2568672083177802542906561

theorem tailTrace_5002471 : CollatzResearch.WordTrace tailWord_5002471 prefixEnd_5002471 2568672083177802542906561 := by
  unfold tailWord_5002471
  simp only [CollatzResearch.WordTrace]
  refine ⟨182455106659909395873311267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121636737773272930582207511 182455106659909395873311267)
  ·
    refine ⟨273682659989864093809966901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182455106659909395873311267 273682659989864093809966901)
    ·
      refine ⟨25657749374049758794684397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 273682659989864093809966901 25657749374049758794684397)
      ·
        refine ⟨9621656015268659548006649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25657749374049758794684397 9621656015268659548006649)
        ·
          refine ⟨7216242011451494661004987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9621656015268659548006649 7216242011451494661004987)
          ·
            refine ⟨10824363017177241991507481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7216242011451494661004987 10824363017177241991507481)
            ·
              refine ⟨8118272262882931493630611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10824363017177241991507481 8118272262882931493630611)
              ·
                refine ⟨12177408394324397240445917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8118272262882931493630611 12177408394324397240445917)
                ·
                  refine ⟨4566528147871648965167219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12177408394324397240445917 4566528147871648965167219)
                  ·
                    refine ⟨6849792221807473447750829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566528147871648965167219 6849792221807473447750829)
                    ·
                      refine ⟨2568672083177802542906561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849792221807473447750829 2568672083177802542906561)
                      ·
                        rfl

theorem cell23_5002471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5002471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002471 prefixEnd_5002471 := by exact prefixLift 5002471
  have htrace : WordTrace (prefixWord ++ tailWord_5002471) baseStart_5002471 baseEnd_5002471 := by
    simpa [prefixWord, tailWord_5002471, baseEnd_5002471] using wordTrace_append hprefix tailTrace_5002471
  have hstable : (prefixWord ++ tailWord_5002471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002471).length < 2 ^ (prefixWord ++ tailWord_5002471).sum := by decide
  have hdescent : baseEnd_5002471 < baseStart_5002471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002490 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_5002490 : Nat := 118140960795 + 5002490 * 2 ^ 59
def prefixEnd_5002490 : Nat := 4983230072969 + 3 ^ 40 * 5002490 * 2
def baseEnd_5002490 : Nat := 2568681839310237968568973

theorem tailTrace_5002490 : CollatzResearch.WordTrace tailWord_5002490 prefixEnd_5002490 2568681839310237968568973 := by
  unfold tailWord_5002490
  simp only [CollatzResearch.WordTrace]
  refine ⟨45613949911710140529563231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121637199764560374745501949 45613949911710140529563231)
  ·
    refine ⟨68420924867565210794344847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45613949911710140529563231 68420924867565210794344847)
    ·
      refine ⟨102631387301347816191517271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68420924867565210794344847 102631387301347816191517271)
      ·
        refine ⟨153947080952021724287275907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102631387301347816191517271 153947080952021724287275907)
        ·
          refine ⟨230920621428032586430913861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153947080952021724287275907 230920621428032586430913861)
          ·
            refine ⟨43297616517756109955796349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230920621428032586430913861 43297616517756109955796349)
            ·
              refine ⟨16236606194158541233423631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43297616517756109955796349 16236606194158541233423631)
              ·
                refine ⟨24354909291237811850135447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16236606194158541233423631 24354909291237811850135447)
                ·
                  refine ⟨36532363936856717775203171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24354909291237811850135447 36532363936856717775203171)
                  ·
                    refine ⟨54798545905285076662804757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36532363936856717775203171 54798545905285076662804757)
                    ·
                      refine ⟨2568681839310237968568973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54798545905285076662804757 2568681839310237968568973)
                      ·
                        rfl

theorem cell23_5002490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_5002490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002490 prefixEnd_5002490 := by exact prefixLift 5002490
  have htrace : WordTrace (prefixWord ++ tailWord_5002490) baseStart_5002490 baseEnd_5002490 := by
    simpa [prefixWord, tailWord_5002490, baseEnd_5002490] using wordTrace_append hprefix tailTrace_5002490
  have hstable : (prefixWord ++ tailWord_5002490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002490).length < 2 ^ (prefixWord ++ tailWord_5002490).sum := by decide
  have hdescent : baseEnd_5002490 < baseStart_5002490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002494 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_5002494 : Nat := 118140960795 + 5002494 * 2 ^ 59
def prefixEnd_5002494 : Nat := 4983230072969 + 3 ^ 40 * 5002494 * 2
def baseEnd_5002494 : Nat := 2568683893232855952918955

theorem tailTrace_5002494 : CollatzResearch.WordTrace tailWord_5002494 prefixEnd_5002494 2568683893232855952918955 := by
  unfold tailWord_5002494
  simp only [CollatzResearch.WordTrace]
  refine ⟨22806993192353258850174817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121637297025884047200932357 22806993192353258850174817)
  ·
    refine ⟨17105244894264944137631113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22806993192353258850174817 17105244894264944137631113)
    ·
      refine ⟨12828933670698708103223335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17105244894264944137631113 12828933670698708103223335)
      ·
        refine ⟨19243400506048062154835003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12828933670698708103223335 19243400506048062154835003)
        ·
          refine ⟨28865100759072093232252505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19243400506048062154835003 28865100759072093232252505)
          ·
            refine ⟨21648825569304069924189379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28865100759072093232252505 21648825569304069924189379)
            ·
              refine ⟨32473238353956104886284069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21648825569304069924189379 32473238353956104886284069)
              ·
                refine ⟨6088732191366769666178263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32473238353956104886284069 6088732191366769666178263)
                ·
                  refine ⟨9133098287050154499267395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6088732191366769666178263 9133098287050154499267395)
                  ·
                    refine ⟨13699647430575231748901093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9133098287050154499267395 13699647430575231748901093)
                    ·
                      refine ⟨2568683893232855952918955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13699647430575231748901093 2568683893232855952918955)
                      ·
                        rfl

theorem cell23_5002494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_5002494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002494 prefixEnd_5002494 := by exact prefixLift 5002494
  have htrace : WordTrace (prefixWord ++ tailWord_5002494) baseStart_5002494 baseEnd_5002494 := by
    simpa [prefixWord, tailWord_5002494, baseEnd_5002494] using wordTrace_append hprefix tailTrace_5002494
  have hstable : (prefixWord ++ tailWord_5002494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002494).length < 2 ^ (prefixWord ++ tailWord_5002494).sum := by decide
  have hdescent : baseEnd_5002494 < baseStart_5002494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002528 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 3, 2, 2]
def baseStart_5002528 : Nat := 118140960795 + 5002528 * 2 ^ 59
def prefixEnd_5002528 : Nat := 4983230072969 + 3 ^ 40 * 5002528 * 2
def baseEnd_5002528 : Nat := 2568701351575108819893799

theorem tailTrace_5002528 : CollatzResearch.WordTrace tailWord_5002528 prefixEnd_5002528 2568701351575108819893799 := by
  unfold tailWord_5002528
  simp only [CollatzResearch.WordTrace]
  refine ⟨91228592810351447304068119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121638123747135263072090825 91228592810351447304068119)
  ·
    refine ⟨136842889215527170956102179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91228592810351447304068119 136842889215527170956102179)
    ·
      refine ⟨205264333823290756434153269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136842889215527170956102179 205264333823290756434153269)
      ·
        refine ⟨19243531295933508415701869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205264333823290756434153269 19243531295933508415701869)
        ·
          refine ⟨7216324235975065655888201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19243531295933508415701869 7216324235975065655888201)
          ·
            refine ⟨5412243176981299241916151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7216324235975065655888201 5412243176981299241916151)
            ·
              refine ⟨8118364765471948862874227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412243176981299241916151 8118364765471948862874227)
              ·
                refine ⟨12177547148207923294311341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8118364765471948862874227 12177547148207923294311341)
                ·
                  refine ⟨4566580180577971235366753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12177547148207923294311341 4566580180577971235366753)
                  ·
                    refine ⟨3424935135433478426525065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4566580180577971235366753 3424935135433478426525065)
                    ·
                      refine ⟨2568701351575108819893799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424935135433478426525065 2568701351575108819893799)
                      ·
                        rfl

theorem cell23_5002528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_5002528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002528 prefixEnd_5002528 := by exact prefixLift 5002528
  have htrace : WordTrace (prefixWord ++ tailWord_5002528) baseStart_5002528 baseEnd_5002528 := by
    simpa [prefixWord, tailWord_5002528, baseEnd_5002528] using wordTrace_append hprefix tailTrace_5002528
  have hstable : (prefixWord ++ tailWord_5002528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002528).length < 2 ^ (prefixWord ++ tailWord_5002528).sum := by decide
  have hdescent : baseEnd_5002528 < baseStart_5002528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002538 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_5002538 : Nat := 118140960795 + 5002538 * 2 ^ 59
def prefixEnd_5002538 : Nat := 4983230072969 + 3 ^ 40 * 5002538 * 2
def baseEnd_5002538 : Nat := 856235495460551260256251

theorem tailTrace_5002538 : CollatzResearch.WordTrace tailWord_5002538 prefixEnd_5002538 856235495460551260256251 := by
  unfold tailWord_5002538
  simp only [CollatzResearch.WordTrace]
  refine ⟨45614387587666666579000067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121638366900444444210666845 45614387587666666579000067)
  ·
    refine ⟨68421581381499999868500101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45614387587666666579000067 68421581381499999868500101)
    ·
      refine ⟨12829046509031249975343769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68421581381499999868500101 12829046509031249975343769)
      ·
        refine ⟨9621784881773437481507827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12829046509031249975343769 9621784881773437481507827)
        ·
          refine ⟨14432677322660156222261741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9621784881773437481507827 14432677322660156222261741)
          ·
            refine ⟨5412253995997558583348153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14432677322660156222261741 5412253995997558583348153)
            ·
              refine ⟨4059190496998168937511115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5412253995997558583348153 4059190496998168937511115)
              ·
                refine ⟨6088785745497253406266673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4059190496998168937511115 6088785745497253406266673)
                ·
                  refine ⟨4566589309122940054700005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6088785745497253406266673 4566589309122940054700005)
                  ·
                    refine ⟨856235495460551260256251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566589309122940054700005 856235495460551260256251)
                    ·
                      rfl

theorem cell23_5002538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_5002538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002538 prefixEnd_5002538 := by exact prefixLift 5002538
  have htrace : WordTrace (prefixWord ++ tailWord_5002538) baseStart_5002538 baseEnd_5002538 := by
    simpa [prefixWord, tailWord_5002538, baseEnd_5002538] using wordTrace_append hprefix tailTrace_5002538
  have hstable : (prefixWord ++ tailWord_5002538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002538).length < 2 ^ (prefixWord ++ tailWord_5002538).sum := by decide
  have hdescent : baseEnd_5002538 < baseStart_5002538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002544 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 2, 1, 3]
def baseStart_5002544 : Nat := 118140960795 + 5002544 * 2 ^ 59
def prefixEnd_5002544 : Nat := 4983230072969 + 3 ^ 40 * 5002544 * 2
def baseEnd_5002544 : Nat := 2568709567265580757293725

theorem tailTrace_5002544 : CollatzResearch.WordTrace tailWord_5002544 prefixEnd_5002544 2568709567265580757293725 := by
  unfold tailWord_5002544
  simp only [CollatzResearch.WordTrace]
  refine ⟨91228884594322464670359343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121638512792429952893812457 91228884594322464670359343)
  ·
    refine ⟨136843326891483697005539015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91228884594322464670359343 136843326891483697005539015)
    ·
      refine ⟨205264990337225545508308523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136843326891483697005539015 205264990337225545508308523)
      ·
        refine ⟨307897485505838318262462785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205264990337225545508308523 307897485505838318262462785)
        ·
          refine ⟨230923114129378738696847089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307897485505838318262462785 230923114129378738696847089)
          ·
            refine ⟨173192335597034054022635317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230923114129378738696847089 173192335597034054022635317)
            ·
              refine ⟨16236781462221942564622061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173192335597034054022635317 16236781462221942564622061)
              ·
                refine ⟨6088793048333228461733273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16236781462221942564622061 6088793048333228461733273)
                ·
                  refine ⟨4566594786249921346299955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6088793048333228461733273 4566594786249921346299955)
                  ·
                    refine ⟨6849892179374882019449933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566594786249921346299955 6849892179374882019449933)
                    ·
                      refine ⟨2568709567265580757293725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6849892179374882019449933 2568709567265580757293725)
                      ·
                        rfl

theorem cell23_5002544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 1, 3].length) (baseStart_5002544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002544 prefixEnd_5002544 := by exact prefixLift 5002544
  have htrace : WordTrace (prefixWord ++ tailWord_5002544) baseStart_5002544 baseEnd_5002544 := by
    simpa [prefixWord, tailWord_5002544, baseEnd_5002544] using wordTrace_append hprefix tailTrace_5002544
  have hstable : (prefixWord ++ tailWord_5002544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002544).length < 2 ^ (prefixWord ++ tailWord_5002544).sum := by decide
  have hdescent : baseEnd_5002544 < baseStart_5002544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002554 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2]
def baseStart_5002554 : Nat := 118140960795 + 5002554 * 2 ^ 59
def prefixEnd_5002554 : Nat := 4983230072969 + 3 ^ 40 * 5002554 * 2
def baseEnd_5002554 : Nat := 2568714702072125718168679

theorem tailTrace_5002554 : CollatzResearch.WordTrace tailWord_5002554 prefixEnd_5002554 2568714702072125718168679 := by
  unfold tailWord_5002554
  simp only [CollatzResearch.WordTrace]
  refine ⟨45614533479652175262145679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121638755945739134032388477 45614533479652175262145679)
  ·
    refine ⟨68421800219478262893218519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45614533479652175262145679 68421800219478262893218519)
    ·
      refine ⟨102632700329217394339827779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68421800219478262893218519 102632700329217394339827779)
      ·
        refine ⟨153949050493826091509741669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102632700329217394339827779 153949050493826091509741669)
        ·
          refine ⟨28865446967592392158076563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153949050493826091509741669 28865446967592392158076563)
          ·
            refine ⟨43298170451388588237114845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28865446967592392158076563 43298170451388588237114845)
            ·
              refine ⟨16236813919270720588918067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43298170451388588237114845 16236813919270720588918067)
              ·
                refine ⟨24355220878906080883377101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16236813919270720588918067 24355220878906080883377101)
                ·
                  refine ⟨9133207829589780331266413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24355220878906080883377101 9133207829589780331266413)
                  ·
                    refine ⟨3424952936096167624224905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9133207829589780331266413 3424952936096167624224905)
                    ·
                      refine ⟨2568714702072125718168679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424952936096167624224905 2568714702072125718168679)
                      ·
                        rfl

theorem cell23_5002554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_5002554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002554 prefixEnd_5002554 := by exact prefixLift 5002554
  have htrace : WordTrace (prefixWord ++ tailWord_5002554) baseStart_5002554 baseEnd_5002554 := by
    simpa [prefixWord, tailWord_5002554, baseEnd_5002554] using wordTrace_append hprefix tailTrace_5002554
  have hstable : (prefixWord ++ tailWord_5002554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002554).length < 2 ^ (prefixWord ++ tailWord_5002554).sum := by decide
  have hdescent : baseEnd_5002554 < baseStart_5002554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002597 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_5002597 : Nat := 118140960795 + 5002597 * 2 ^ 59
def prefixEnd_5002597 : Nat := 4983230072969 + 3 ^ 40 * 5002597 * 2
def baseEnd_5002597 : Nat := 2568736781740269049930981

theorem tailTrace_5002597 : CollatzResearch.WordTrace tailWord_5002597 prefixEnd_5002597 2568736781740269049930981 := by
  unfold tailWord_5002597
  simp only [CollatzResearch.WordTrace]
  refine ⟨182459702257452919392398045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121639801504968612928265363 182459702257452919392398045)
  ·
    refine ⟨68422388346544844772149267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182459702257452919392398045 68422388346544844772149267)
    ·
      refine ⟨102633582519817267158223901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68422388346544844772149267 102633582519817267158223901)
      ·
        refine ⟨38487593444931475184333963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102633582519817267158223901 38487593444931475184333963)
        ·
          refine ⟨57731390167397212776500945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38487593444931475184333963 57731390167397212776500945)
          ·
            refine ⟨43298542625547909582375709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57731390167397212776500945 43298542625547909582375709)
            ·
              refine ⟨16236953484580466093390891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43298542625547909582375709 16236953484580466093390891)
              ·
                refine ⟨24355430226870699140086337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16236953484580466093390891 24355430226870699140086337)
                ·
                  refine ⟨18266572670153024355064753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24355430226870699140086337 18266572670153024355064753)
                  ·
                    refine ⟨13699929502614768266298565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18266572670153024355064753 13699929502614768266298565)
                    ·
                      refine ⟨2568736781740269049930981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13699929502614768266298565 2568736781740269049930981)
                      ·
                        rfl

theorem cell23_5002597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_5002597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002597 prefixEnd_5002597 := by exact prefixLift 5002597
  have htrace : WordTrace (prefixWord ++ tailWord_5002597) baseStart_5002597 baseEnd_5002597 := by
    simpa [prefixWord, tailWord_5002597, baseEnd_5002597] using wordTrace_append hprefix tailTrace_5002597
  have hstable : (prefixWord ++ tailWord_5002597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002597).length < 2 ^ (prefixWord ++ tailWord_5002597).sum := by decide
  have hdescent : baseEnd_5002597 < baseStart_5002597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002640 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_5002640 : Nat := 118140960795 + 5002640 * 2 ^ 59
def prefixEnd_5002640 : Nat := 4983230072969 + 3 ^ 40 * 5002640 * 2
def baseEnd_5002640 : Nat := 2568758861408412381693283

theorem tailTrace_5002640 : CollatzResearch.WordTrace tailWord_5002640 prefixEnd_5002640 2568758861408412381693283 := by
  unfold tailWord_5002640
  simp only [CollatzResearch.WordTrace]
  refine ⟨91230635298148568868106687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121640847064198091824142249 91230635298148568868106687)
  ·
    refine ⟨136845952947222853302160031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91230635298148568868106687 136845952947222853302160031)
    ·
      refine ⟨205268929420834279953240047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136845952947222853302160031 205268929420834279953240047)
      ·
        refine ⟨307903394131251419929860071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205268929420834279953240047 307903394131251419929860071)
        ·
          refine ⟨461855091196877129894790107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307903394131251419929860071 461855091196877129894790107)
          ·
            refine ⟨692782636795315694842185161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461855091196877129894790107 692782636795315694842185161)
            ·
              refine ⟨519586977596486771131638871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692782636795315694842185161 519586977596486771131638871)
              ·
                refine ⟨779380466394730156697458307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519586977596486771131638871 779380466394730156697458307)
                ·
                  refine ⟨1169070699592095235046187461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779380466394730156697458307 1169070699592095235046187461)
                  ·
                    refine ⟨219200756173517856571160149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1169070699592095235046187461 219200756173517856571160149)
                    ·
                      refine ⟨2568758861408412381693283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 219200756173517856571160149 2568758861408412381693283)
                      ·
                        rfl

theorem cell23_5002640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_5002640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002640 prefixEnd_5002640 := by exact prefixLift 5002640
  have htrace : WordTrace (prefixWord ++ tailWord_5002640) baseStart_5002640 baseEnd_5002640 := by
    simpa [prefixWord, tailWord_5002640, baseEnd_5002640] using wordTrace_append hprefix tailTrace_5002640
  have hstable : (prefixWord ++ tailWord_5002640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002640).length < 2 ^ (prefixWord ++ tailWord_5002640).sum := by decide
  have hdescent : baseEnd_5002640 < baseStart_5002640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002652 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5002652 : Nat := 118140960795 + 5002652 * 2 ^ 59
def prefixEnd_5002652 : Nat := 4983230072969 + 3 ^ 40 * 5002652 * 2
def baseEnd_5002652 : Nat := 2568765023176266334743229

theorem tailTrace_5002652 : CollatzResearch.WordTrace tailWord_5002652 prefixEnd_5002652 2568765023176266334743229 := by
  unfold tailWord_5002652
  simp only [CollatzResearch.WordTrace]
  refine ⟨91230854136126831892825105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121641138848169109190433473 91230854136126831892825105)
  ·
    refine ⟨68423140602095123919618829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91230854136126831892825105 68423140602095123919618829)
    ·
      refine ⟨25658677725785671469857061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68423140602095123919618829 25658677725785671469857061)
      ·
        refine ⟨4811002073584813400598199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25658677725785671469857061 4811002073584813400598199)
        ·
          refine ⟨7216503110377220100897299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4811002073584813400598199 7216503110377220100897299)
          ·
            refine ⟨10824754665565830151345949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7216503110377220100897299 10824754665565830151345949)
            ·
              refine ⟨4059282999587186306754731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10824754665565830151345949 4059282999587186306754731)
              ·
                refine ⟨6088924499380779460132097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4059282999587186306754731 6088924499380779460132097)
                ·
                  refine ⟨4566693374535584595099073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6088924499380779460132097 4566693374535584595099073)
                  ·
                    refine ⟨3425020030901688446324305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4566693374535584595099073 3425020030901688446324305)
                    ·
                      refine ⟨2568765023176266334743229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425020030901688446324305 2568765023176266334743229)
                      ·
                        rfl

theorem cell23_5002652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5002652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002652 prefixEnd_5002652 := by exact prefixLift 5002652
  have htrace : WordTrace (prefixWord ++ tailWord_5002652) baseStart_5002652 baseEnd_5002652 := by
    simpa [prefixWord, tailWord_5002652, baseEnd_5002652] using wordTrace_append hprefix tailTrace_5002652
  have hstable : (prefixWord ++ tailWord_5002652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002652).length < 2 ^ (prefixWord ++ tailWord_5002652).sum := by decide
  have hdescent : baseEnd_5002652 < baseStart_5002652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002667 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 9, 4]
def baseStart_5002667 : Nat := 118140960795 + 5002667 * 2 ^ 59
def prefixEnd_5002667 : Nat := 4983230072969 + 3 ^ 40 * 5002667 * 2
def baseEnd_5002667 : Nat := 856257575128694592018553

theorem tailTrace_5002667 : CollatzResearch.WordTrace tailWord_5002667 prefixEnd_5002667 856257575128694592018553 := by
  unfold tailWord_5002667
  simp only [CollatzResearch.WordTrace]
  refine ⟨182462255367199321347446255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121641503578132880898297503 182462255367199321347446255)
  ·
    refine ⟨273693383050798982021169383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182462255367199321347446255 273693383050798982021169383)
    ·
      refine ⟨410540074576198473031754075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273693383050798982021169383 410540074576198473031754075)
      ·
        refine ⟨615810111864297709547631113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410540074576198473031754075 615810111864297709547631113)
        ·
          refine ⟨461857583898223282160723335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615810111864297709547631113 461857583898223282160723335)
          ·
            refine ⟨692786375847334923241085003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461857583898223282160723335 692786375847334923241085003)
            ·
              refine ⟨1039179563771002384861627505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692786375847334923241085003 1039179563771002384861627505)
              ·
                refine ⟨779384672828251788646220629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039179563771002384861627505 779384672828251788646220629)
                ·
                  refine ⟨4566707067353037824098949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 779384672828251788646220629 4566707067353037824098949)
                  ·
                    refine ⟨856257575128694592018553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566707067353037824098949 856257575128694592018553)
                    ·
                      rfl

theorem cell23_5002667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 4].length) (baseStart_5002667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002667 prefixEnd_5002667 := by exact prefixLift 5002667
  have htrace : WordTrace (prefixWord ++ tailWord_5002667) baseStart_5002667 baseEnd_5002667 := by
    simpa [prefixWord, tailWord_5002667, baseEnd_5002667] using wordTrace_append hprefix tailTrace_5002667
  have hstable : (prefixWord ++ tailWord_5002667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002667).length < 2 ^ (prefixWord ++ tailWord_5002667).sum := by decide
  have hdescent : baseEnd_5002667 < baseStart_5002667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002674 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_5002674 : Nat := 118140960795 + 5002674 * 2 ^ 59
def prefixEnd_5002674 : Nat := 4983230072969 + 3 ^ 40 * 5002674 * 2
def baseEnd_5002674 : Nat := 2568776319750665248668127

theorem tailTrace_5002674 : CollatzResearch.WordTrace tailWord_5002674 prefixEnd_5002674 2568776319750665248668127 := by
  unfold tailWord_5002674
  simp only [CollatzResearch.WordTrace]
  refine ⟨45615627669543490385737769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121641673785449307695300717 45615627669543490385737769)
  ·
    refine ⟨34211720752157617789303327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45615627669543490385737769 34211720752157617789303327)
    ·
      refine ⟨51317581128236426683954991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34211720752157617789303327 51317581128236426683954991)
      ·
        refine ⟨76976371692354640025932487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51317581128236426683954991 76976371692354640025932487)
        ·
          refine ⟨115464557538531960038898731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76976371692354640025932487 115464557538531960038898731)
          ·
            refine ⟨173196836307797940058348097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115464557538531960038898731 173196836307797940058348097)
            ·
              refine ⟨129897627230848455043761073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173196836307797940058348097 129897627230848455043761073)
              ·
                refine ⟨97423220423136341282820805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129897627230848455043761073 97423220423136341282820805)
                ·
                  refine ⟨18266853829338063990528901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97423220423136341282820805 18266853829338063990528901)
                  ·
                    refine ⟨3425035093000886998224169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18266853829338063990528901 3425035093000886998224169)
                    ·
                      refine ⟨2568776319750665248668127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425035093000886998224169 2568776319750665248668127)
                      ·
                        rfl

theorem cell23_5002674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_5002674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002674 prefixEnd_5002674 := by exact prefixLift 5002674
  have htrace : WordTrace (prefixWord ++ tailWord_5002674) baseStart_5002674 baseEnd_5002674 := by
    simpa [prefixWord, tailWord_5002674, baseEnd_5002674] using wordTrace_append hprefix tailTrace_5002674
  have hstable : (prefixWord ++ tailWord_5002674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002674).length < 2 ^ (prefixWord ++ tailWord_5002674).sum := by decide
  have hdescent : baseEnd_5002674 < baseStart_5002674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002697 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 6]
def baseStart_5002697 : Nat := 118140960795 + 5002697 * 2 ^ 59
def prefixEnd_5002697 : Nat := 4983230072969 + 3 ^ 40 * 5002697 * 2
def baseEnd_5002697 : Nat := 285420903311746517631169

theorem tailTrace_5002697 : CollatzResearch.WordTrace tailWord_5002697 prefixEnd_5002697 285420903311746517631169 := by
  unfold tailWord_5002697
  simp only [CollatzResearch.WordTrace]
  refine ⟨182463349557090636471038345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121642233038060424314025563 182463349557090636471038345)
  ·
    refine ⟨136847512167817977353278759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182463349557090636471038345 136847512167817977353278759)
    ·
      refine ⟨205271268251726966029918139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136847512167817977353278759 205271268251726966029918139)
      ·
        refine ⟨307906902377590449044877209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205271268251726966029918139 307906902377590449044877209)
        ·
          refine ⟨230930176783192836783657907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307906902377590449044877209 230930176783192836783657907)
          ·
            refine ⟨346395265174789255175486861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230930176783192836783657907 346395265174789255175486861)
            ·
              refine ⟨129898224440545970690807573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346395265174789255175486861 129898224440545970690807573)
              ·
                refine ⟨6088979270650592376131605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129898224440545970690807573 6088979270650592376131605)
                ·
                  refine ⟨285420903311746517631169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6088979270650592376131605 285420903311746517631169)
                  ·
                    rfl

theorem cell23_5002697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 6].length) (baseStart_5002697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002697 prefixEnd_5002697 := by exact prefixLift 5002697
  have htrace : WordTrace (prefixWord ++ tailWord_5002697) baseStart_5002697 baseEnd_5002697 := by
    simpa [prefixWord, tailWord_5002697, baseEnd_5002697] using wordTrace_append hprefix tailTrace_5002697
  have hstable : (prefixWord ++ tailWord_5002697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002697).length < 2 ^ (prefixWord ++ tailWord_5002697).sum := by decide
  have hdescent : baseEnd_5002697 < baseStart_5002697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002714 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 6]
def baseStart_5002714 : Nat := 118140960795 + 5002714 * 2 ^ 59
def prefixEnd_5002714 : Nat := 4983230072969 + 3 ^ 40 * 5002714 * 2
def baseEnd_5002714 : Nat := 285421873219649454685327

theorem tailTrace_5002714 : CollatzResearch.WordTrace tailWord_5002714 prefixEnd_5002714 285421873219649454685327 := by
  unfold tailWord_5002714
  simp only [CollatzResearch.WordTrace]
  refine ⟨45615992399507262093601799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121642646398686032249604797 45615992399507262093601799)
  ·
    refine ⟨68423988599260893140402699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45615992399507262093601799 68423988599260893140402699)
    ·
      refine ⟨102635982898891339710604049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68423988599260893140402699 102635982898891339710604049)
      ·
        refine ⟨76976987174168504782953037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102635982898891339710604049 76976987174168504782953037)
        ·
          refine ⟨28866370190313189293607389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76976987174168504782953037 28866370190313189293607389)
          ·
            refine ⟨10824888821367445985102771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28866370190313189293607389 10824888821367445985102771)
            ·
              refine ⟨16237333232051168977654157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10824888821367445985102771 16237333232051168977654157)
              ·
                refine ⟨6088999962019188366620309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16237333232051168977654157 6088999962019188366620309)
                ·
                  refine ⟨285421873219649454685327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6088999962019188366620309 285421873219649454685327)
                  ·
                    rfl

theorem cell23_5002714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_5002714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002714 prefixEnd_5002714 := by exact prefixLift 5002714
  have htrace : WordTrace (prefixWord ++ tailWord_5002714) baseStart_5002714 baseEnd_5002714 := by
    simpa [prefixWord, tailWord_5002714, baseEnd_5002714] using wordTrace_append hprefix tailTrace_5002714
  have hstable : (prefixWord ++ tailWord_5002714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002714).length < 2 ^ (prefixWord ++ tailWord_5002714).sum := by decide
  have hdescent : baseEnd_5002714 < baseStart_5002714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002757 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_5002757 : Nat := 118140960795 + 5002757 * 2 ^ 59
def prefixEnd_5002757 : Nat := 4983230072969 + 3 ^ 40 * 5002757 * 2
def baseEnd_5002757 : Nat := 856272979548329474643415

theorem tailTrace_5002757 : CollatzResearch.WordTrace tailWord_5002757 prefixEnd_5002757 856272979548329474643415 := by
  unfold tailWord_5002757
  simp only [CollatzResearch.WordTrace]
  refine ⟨182465537936873266718222525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121643691957915511145481683 182465537936873266718222525)
  ·
    refine ⟨68424576726327475019333447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182465537936873266718222525 68424576726327475019333447)
    ·
      refine ⟨102636865089491212529000171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68424576726327475019333447 102636865089491212529000171)
      ·
        refine ⟨153955297634236818793500257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102636865089491212529000171 153955297634236818793500257)
        ·
          refine ⟨115466473225677614095125193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153955297634236818793500257 115466473225677614095125193)
          ·
            refine ⟨86599854919258210571343895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115466473225677614095125193 86599854919258210571343895)
            ·
              refine ⟨129899782378887315857015843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86599854919258210571343895 129899782378887315857015843)
              ·
                refine ⟨194849673568330973785523765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129899782378887315857015843 194849673568330973785523765)
                ·
                  refine ⟨18267156897031028792392853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194849673568330973785523765 18267156897031028792392853)
                  ·
                    refine ⟨856272979548329474643415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18267156897031028792392853 856272979548329474643415)
                    ·
                      rfl

theorem cell23_5002757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_5002757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002757 prefixEnd_5002757 := by exact prefixLift 5002757
  have htrace : WordTrace (prefixWord ++ tailWord_5002757) baseStart_5002757 baseEnd_5002757 := by
    simpa [prefixWord, tailWord_5002757, baseEnd_5002757] using wordTrace_append hprefix tailTrace_5002757
  have hstable : (prefixWord ++ tailWord_5002757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002757).length < 2 ^ (prefixWord ++ tailWord_5002757).sum := by decide
  have hdescent : baseEnd_5002757 < baseStart_5002757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002781 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_5002781 : Nat := 118140960795 + 5002781 * 2 ^ 59
def prefixEnd_5002781 : Nat := 4983230072969 + 3 ^ 40 * 5002781 * 2
def baseEnd_5002781 : Nat := 2568831262180696330030135

theorem tailTrace_5002781 : CollatzResearch.WordTrace tailWord_5002781 prefixEnd_5002781 2568831262180696330030135 := by
  unfold tailWord_5002781
  simp only [CollatzResearch.WordTrace]
  refine ⟨182466413288786318817096197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121644275525857545878064131 182466413288786318817096197)
  ·
    refine ⟨34212452491647434778205537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182466413288786318817096197 34212452491647434778205537)
    ·
      refine ⟨25659339368735576083654153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34212452491647434778205537 25659339368735576083654153)
      ·
        refine ⟨19244504526551682062740615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25659339368735576083654153 19244504526551682062740615)
        ·
          refine ⟨28866756789827523094110923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19244504526551682062740615 28866756789827523094110923)
          ·
            refine ⟨43300135184741284641166385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28866756789827523094110923 43300135184741284641166385)
            ·
              refine ⟨32475101388555963480874789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43300135184741284641166385 32475101388555963480874789)
              ·
                refine ⟨6089081510354243152664023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32475101388555963480874789 6089081510354243152664023)
                ·
                  refine ⟨9133622265531364728996035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6089081510354243152664023 9133622265531364728996035)
                  ·
                    refine ⟨13700433398297047093494053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9133622265531364728996035 13700433398297047093494053)
                    ·
                      refine ⟨2568831262180696330030135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13700433398297047093494053 2568831262180696330030135)
                      ·
                        rfl

theorem cell23_5002781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_5002781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002781 prefixEnd_5002781 := by exact prefixLift 5002781
  have htrace : WordTrace (prefixWord ++ tailWord_5002781) baseStart_5002781 baseEnd_5002781 := by
    simpa [prefixWord, tailWord_5002781, baseEnd_5002781] using wordTrace_append hprefix tailTrace_5002781
  have hstable : (prefixWord ++ tailWord_5002781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002781).length < 2 ^ (prefixWord ++ tailWord_5002781).sum := by decide
  have hdescent : baseEnd_5002781 < baseStart_5002781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002792 : List Nat := [2, 1, 5, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_5002792 : Nat := 118140960795 + 5002792 * 2 ^ 59
def prefixEnd_5002792 : Nat := 4983230072969 + 3 ^ 40 * 5002792 * 2
def baseEnd_5002792 : Nat := 2568836910467895786992585

theorem tailTrace_5002792 : CollatzResearch.WordTrace tailWord_5002792 prefixEnd_5002792 2568836910467895786992585 := by
  unfold tailWord_5002792
  simp only [CollatzResearch.WordTrace]
  refine ⟨91233407245873233847873315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121644542994497645130497753 91233407245873233847873315)
  ·
    refine ⟨136850110868809850771809973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91233407245873233847873315 136850110868809850771809973)
    ·
      refine ⟨12829697893950923509857185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136850110868809850771809973 12829697893950923509857185)
      ·
        refine ⟨9622273420463192632392889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12829697893950923509857185 9622273420463192632392889)
        ·
          refine ⟨7216705065347394474294667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9622273420463192632392889 7216705065347394474294667)
          ·
            refine ⟨10825057598021091711442001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7216705065347394474294667 10825057598021091711442001)
            ·
              refine ⟨8118793198515818783581501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10825057598021091711442001 8118793198515818783581501)
              ·
                refine ⟨3044547449443432043843063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8118793198515818783581501 3044547449443432043843063)
                ·
                  refine ⟨4566821174165148065764595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044547449443432043843063 4566821174165148065764595)
                  ·
                    refine ⟨6850231761247722098646893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566821174165148065764595 6850231761247722098646893)
                    ·
                      refine ⟨2568836910467895786992585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6850231761247722098646893 2568836910467895786992585)
                      ·
                        rfl

theorem cell23_5002792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_5002792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002792 prefixEnd_5002792 := by exact prefixLift 5002792
  have htrace : WordTrace (prefixWord ++ tailWord_5002792) baseStart_5002792 baseEnd_5002792 := by
    simpa [prefixWord, tailWord_5002792, baseEnd_5002792] using wordTrace_append hprefix tailTrace_5002792
  have hstable : (prefixWord ++ tailWord_5002792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002792).length < 2 ^ (prefixWord ++ tailWord_5002792).sum := by decide
  have hdescent : baseEnd_5002792 < baseStart_5002792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002798 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5002798 : Nat := 118140960795 + 5002798 * 2 ^ 59
def prefixEnd_5002798 : Nat := 4983230072969 + 3 ^ 40 * 5002798 * 2
def baseEnd_5002798 : Nat := 2568839991351822763517557

theorem tailTrace_5002798 : CollatzResearch.WordTrace tailWord_5002798 prefixEnd_5002798 2568839991351822763517557 := by
  unfold tailWord_5002798
  simp only [CollatzResearch.WordTrace]
  refine ⟨22808379166215591340058131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121644688886483153813643365 22808379166215591340058131)
  ·
    refine ⟨34212568749323387010087197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22808379166215591340058131 34212568749323387010087197)
    ·
      refine ⟨12829713280996270128782699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34212568749323387010087197 12829713280996270128782699)
      ·
        refine ⟨19244569921494405193174049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12829713280996270128782699 19244569921494405193174049)
        ·
          refine ⟨14433427441120803894880537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19244569921494405193174049 14433427441120803894880537)
          ·
            refine ⟨10825070580840602921160403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14433427441120803894880537 10825070580840602921160403)
            ·
              refine ⟨16237605871260904381740605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10825070580840602921160403 16237605871260904381740605)
              ·
                refine ⟨6089102201722839143152727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16237605871260904381740605 6089102201722839143152727)
                ·
                  refine ⟨9133653302584258714729091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6089102201722839143152727 9133653302584258714729091)
                  ·
                    refine ⟨13700479953876388072093637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9133653302584258714729091 13700479953876388072093637)
                    ·
                      refine ⟨2568839991351822763517557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13700479953876388072093637 2568839991351822763517557)
                      ·
                        rfl

theorem cell23_5002798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5002798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002798 prefixEnd_5002798 := by exact prefixLift 5002798
  have htrace : WordTrace (prefixWord ++ tailWord_5002798) baseStart_5002798 baseEnd_5002798 := by
    simpa [prefixWord, tailWord_5002798, baseEnd_5002798] using wordTrace_append hprefix tailTrace_5002798
  have hstable : (prefixWord ++ tailWord_5002798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002798).length < 2 ^ (prefixWord ++ tailWord_5002798).sum := by decide
  have hdescent : baseEnd_5002798 < baseStart_5002798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002808 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 2, 4]
def baseStart_5002808 : Nat := 118140960795 + 5002808 * 2 ^ 59
def prefixEnd_5002808 : Nat := 4983230072969 + 3 ^ 40 * 5002808 * 2
def baseEnd_5002808 : Nat := 856281708719455908130837

theorem tailTrace_5002808 : CollatzResearch.WordTrace tailWord_5002808 prefixEnd_5002808 856281708719455908130837 := by
  unfold tailWord_5002808
  simp only [CollatzResearch.WordTrace]
  refine ⟨91233699029844251214164539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121644932039792334952219385 91233699029844251214164539)
  ·
    refine ⟨136850548544766376821246809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91233699029844251214164539 136850548544766376821246809)
    ·
      refine ⟨102637911408574782615935107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136850548544766376821246809 102637911408574782615935107)
      ·
        refine ⟨153956867112862173923902661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102637911408574782615935107 153956867112862173923902661)
        ·
          refine ⟨28866912583661657610731749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153956867112862173923902661 28866912583661657610731749)
          ·
            refine ⟨5412546109436560802012203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28866912583661657610731749 5412546109436560802012203)
            ·
              refine ⟨8118819164154841203018305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412546109436560802012203 8118819164154841203018305)
              ·
                refine ⟨6089114373116130902263729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8118819164154841203018305 6089114373116130902263729)
                ·
                  refine ⟨4566835779837098176697797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6089114373116130902263729 4566835779837098176697797)
                  ·
                    refine ⟨856281708719455908130837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566835779837098176697797 856281708719455908130837)
                    ·
                      rfl

theorem cell23_5002808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_5002808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002808 prefixEnd_5002808 := by exact prefixLift 5002808
  have htrace : WordTrace (prefixWord ++ tailWord_5002808) baseStart_5002808 baseEnd_5002808 := by
    simpa [prefixWord, tailWord_5002808, baseEnd_5002808] using wordTrace_append hprefix tailTrace_5002808
  have hstable : (prefixWord ++ tailWord_5002808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002808).length < 2 ^ (prefixWord ++ tailWord_5002808).sum := by decide
  have hdescent : baseEnd_5002808 < baseStart_5002808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002815 : List Nat := [1, 1, 2, 2, 3, 3, 2, 4, 1, 2, 2]
def baseStart_5002815 : Nat := 118140960795 + 5002815 * 2 ^ 59
def prefixEnd_5002815 : Nat := 4983230072969 + 3 ^ 40 * 5002815 * 2
def baseEnd_5002815 : Nat := 2568848720522949197004979

theorem tailTrace_5002815 : CollatzResearch.WordTrace tailWord_5002815 prefixEnd_5002815 2568848720522949197004979 := by
  unfold tailWord_5002815
  simp only [CollatzResearch.WordTrace]
  refine ⟨182467653370663142623833899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121645102247108761749222599 182467653370663142623833899)
  ·
    refine ⟨273701480055994713935750849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182467653370663142623833899 273701480055994713935750849)
    ·
      refine ⟨205276110041996035451813137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273701480055994713935750849 205276110041996035451813137)
      ·
        refine ⟨153957082531497026588859853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205276110041996035451813137 153957082531497026588859853)
        ·
          refine ⟨57733905949311384970822445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153957082531497026588859853 57733905949311384970822445)
          ·
            refine ⟨21650214730991769364058417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57733905949311384970822445 21650214730991769364058417)
            ·
              refine ⟨16237661048243827023043813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21650214730991769364058417 16237661048243827023043813)
              ·
                refine ⟨3044561446545717566820715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16237661048243827023043813 3044561446545717566820715)
                ·
                  refine ⟨4566842169818576350231073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044561446545717566820715 4566842169818576350231073)
                  ·
                    refine ⟨3425131627363932262673305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4566842169818576350231073 3425131627363932262673305)
                    ·
                      refine ⟨2568848720522949197004979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425131627363932262673305 2568848720522949197004979)
                      ·
                        rfl

theorem cell23_5002815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_5002815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002815 prefixEnd_5002815 := by exact prefixLift 5002815
  have htrace : WordTrace (prefixWord ++ tailWord_5002815) baseStart_5002815 baseEnd_5002815 := by
    simpa [prefixWord, tailWord_5002815, baseEnd_5002815] using wordTrace_append hprefix tailTrace_5002815
  have hstable : (prefixWord ++ tailWord_5002815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002815).length < 2 ^ (prefixWord ++ tailWord_5002815).sum := by decide
  have hdescent : baseEnd_5002815 < baseStart_5002815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002841 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 3, 3, 2]
def baseStart_5002841 : Nat := 118140960795 + 5002841 * 2 ^ 59
def prefixEnd_5002841 : Nat := 4983230072969 + 3 ^ 40 * 5002841 * 2
def baseEnd_5002841 : Nat := 2568862071019966095279859

theorem tailTrace_5002841 : CollatzResearch.WordTrace tailWord_5002841 prefixEnd_5002841 2568862071019966095279859 := by
  unfold tailWord_5002841
  simp only [CollatzResearch.WordTrace]
  refine ⟨182468601668568949064280377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121645734445712632709520251 182468601668568949064280377)
  ·
    refine ⟨136851451251426711798210283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182468601668568949064280377 136851451251426711798210283)
    ·
      refine ⟨205277176877140067697315425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136851451251426711798210283 205277176877140067697315425)
      ·
        refine ⟨153957882657855050772986569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205277176877140067697315425 153957882657855050772986569)
        ·
          refine ⟨115468411993391288079739927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153957882657855050772986569 115468411993391288079739927)
          ·
            refine ⟨173202617990086932119609891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115468411993391288079739927 173202617990086932119609891)
            ·
              refine ⟨259803926985130398179414837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173202617990086932119609891 259803926985130398179414837)
              ·
                refine ⟨24356618154855974829320141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259803926985130398179414837 24356618154855974829320141)
                ·
                  refine ⟨9133731808070990560995053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24356618154855974829320141 9133731808070990560995053)
                  ·
                    refine ⟨3425149428026621460373145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9133731808070990560995053 3425149428026621460373145)
                    ·
                      refine ⟨2568862071019966095279859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425149428026621460373145 2568862071019966095279859)
                      ·
                        rfl

theorem cell23_5002841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_5002841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002841 prefixEnd_5002841 := by exact prefixLift 5002841
  have htrace : WordTrace (prefixWord ++ tailWord_5002841) baseStart_5002841 baseEnd_5002841 := by
    simpa [prefixWord, tailWord_5002841, baseEnd_5002841] using wordTrace_append hprefix tailTrace_5002841
  have hstable : (prefixWord ++ tailWord_5002841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002841).length < 2 ^ (prefixWord ++ tailWord_5002841).sum := by decide
  have hdescent : baseEnd_5002841 < baseStart_5002841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002928 : List Nat := [2, 1, 1, 1, 2, 1, 8, 2, 5]
def baseStart_5002928 : Nat := 118140960795 + 5002928 * 2 ^ 59
def prefixEnd_5002928 : Nat := 4983230072969 + 3 ^ 40 * 5002928 * 2
def baseEnd_5002928 : Nat := 285434082648545250543551

theorem tailTrace_5002928 : CollatzResearch.WordTrace tailWord_5002928 prefixEnd_5002928 285434082648545250543551 := by
  unfold tailWord_5002928
  simp only [CollatzResearch.WordTrace]
  refine ⟨91235887409626881461348719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121647849879502508615131625 91235887409626881461348719)
  ·
    refine ⟨136853831114440322192023079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91235887409626881461348719 136853831114440322192023079)
    ·
      refine ⟨205280746671660483288034619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136853831114440322192023079 205280746671660483288034619)
      ·
        refine ⟨307921120007490724932051929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205280746671660483288034619 307921120007490724932051929)
        ·
          refine ⟨230940840005618043699038947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307921120007490724932051929 230940840005618043699038947)
          ·
            refine ⟨346411260008427065548558421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230940840005618043699038947 346411260008427065548558421)
            ·
              refine ⟨4059506953223754674397169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 346411260008427065548558421 4059506953223754674397169)
              ·
                refine ⟨3044630214917816005797877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4059506953223754674397169 3044630214917816005797877)
                ·
                  refine ⟨285434082648545250543551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3044630214917816005797877 285434082648545250543551)
                  ·
                    rfl

theorem cell23_5002928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 5].length) (baseStart_5002928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002928 prefixEnd_5002928 := by exact prefixLift 5002928
  have htrace : WordTrace (prefixWord ++ tailWord_5002928) baseStart_5002928 baseEnd_5002928 := by
    simpa [prefixWord, tailWord_5002928, baseEnd_5002928] using wordTrace_append hprefix tailTrace_5002928
  have hstable : (prefixWord ++ tailWord_5002928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002928).length < 2 ^ (prefixWord ++ tailWord_5002928).sum := by decide
  have hdescent : baseEnd_5002928 < baseStart_5002928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002931 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 1, 7, 2]
def baseStart_5002931 : Nat := 118140960795 + 5002931 * 2 ^ 59
def prefixEnd_5002931 : Nat := 4983230072969 + 3 ^ 40 * 5002931 * 2
def baseEnd_5002931 : Nat := 2568908284278870743154445

theorem tailTrace_5002931 : CollatzResearch.WordTrace tailWord_5002931 prefixEnd_5002931 2568908284278870743154445 := by
  unfold tailWord_5002931
  simp only [CollatzResearch.WordTrace]
  refine ⟨182471884238242894435056647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121647922825495262956704431 182471884238242894435056647)
  ·
    refine ⟨273707826357364341652584971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182471884238242894435056647 273707826357364341652584971)
    ·
      refine ⟨410561739536046512478877457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273707826357364341652584971 410561739536046512478877457)
      ·
        refine ⟨307921304652034884359158093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410561739536046512478877457 307921304652034884359158093)
        ·
          refine ⟨115470489244513081634684285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307921304652034884359158093 115470489244513081634684285)
          ·
            refine ⟨43301433466692405613006607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115470489244513081634684285 43301433466692405613006607)
            ·
              refine ⟨64952150200038608419509911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43301433466692405613006607 64952150200038608419509911)
              ·
                refine ⟨97428225300057912629264867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64952150200038608419509911 97428225300057912629264867)
                ·
                  refine ⟨146142337950086868943897301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97428225300057912629264867 146142337950086868943897301)
                  ·
                    refine ⟨3425211045705160990872593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 146142337950086868943897301 3425211045705160990872593)
                    ·
                      refine ⟨2568908284278870743154445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425211045705160990872593 2568908284278870743154445)
                      ·
                        rfl

theorem cell23_5002931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 7, 2].length) (baseStart_5002931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002931 prefixEnd_5002931 := by exact prefixLift 5002931
  have htrace : WordTrace (prefixWord ++ tailWord_5002931) baseStart_5002931 baseEnd_5002931 := by
    simpa [prefixWord, tailWord_5002931, baseEnd_5002931] using wordTrace_append hprefix tailTrace_5002931
  have hstable : (prefixWord ++ tailWord_5002931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002931).length < 2 ^ (prefixWord ++ tailWord_5002931).sum := by decide
  have hdescent : baseEnd_5002931 < baseStart_5002931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002948 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_5002948 : Nat := 118140960795 + 5002948 * 2 ^ 59
def prefixEnd_5002948 : Nat := 4983230072969 + 3 ^ 40 * 5002948 * 2
def baseEnd_5002948 : Nat := 2568917013449997176641867

theorem tailTrace_5002948 : CollatzResearch.WordTrace tailWord_5002948 prefixEnd_5002948 2568917013449997176641867 := by
  unfold tailWord_5002948
  simp only [CollatzResearch.WordTrace]
  refine ⟨91236252139590653169212749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121648336186120870892283665 91236252139590653169212749)
  ·
    refine ⟨34213594552346494938454781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91236252139590653169212749 34213594552346494938454781)
    ·
      refine ⟨12830097957129935601920543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34213594552346494938454781 12830097957129935601920543)
      ·
        refine ⟨19245146935694903402880815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12830097957129935601920543 19245146935694903402880815)
        ·
          refine ⟨28867720403542355104321223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19245146935694903402880815 28867720403542355104321223)
          ·
            refine ⟨43301580605313532656481835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28867720403542355104321223 43301580605313532656481835)
            ·
              refine ⟨64952370907970298984722753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43301580605313532656481835 64952370907970298984722753)
              ·
                refine ⟨48714278180977724238542065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64952370907970298984722753 48714278180977724238542065)
                ·
                  refine ⟨36535708635733293178906549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48714278180977724238542065 36535708635733293178906549)
                  ·
                    refine ⟨3425222684599996235522489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36535708635733293178906549 3425222684599996235522489)
                    ·
                      refine ⟨2568917013449997176641867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425222684599996235522489 2568917013449997176641867)
                      ·
                        rfl

theorem cell23_5002948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_5002948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002948 prefixEnd_5002948 := by exact prefixLift 5002948
  have htrace : WordTrace (prefixWord ++ tailWord_5002948) baseStart_5002948 baseEnd_5002948 := by
    simpa [prefixWord, tailWord_5002948, baseEnd_5002948] using wordTrace_append hprefix tailTrace_5002948
  have hstable : (prefixWord ++ tailWord_5002948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002948).length < 2 ^ (prefixWord ++ tailWord_5002948).sum := by decide
  have hdescent : baseEnd_5002948 < baseStart_5002948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002961 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_5002961 : Nat := 118140960795 + 5002961 * 2 ^ 59
def prefixEnd_5002961 : Nat := 4983230072969 + 3 ^ 40 * 5002961 * 2
def baseEnd_5002961 : Nat := 2568923688698505625779307

theorem tailTrace_5002961 : CollatzResearch.WordTrace tailWord_5002961 prefixEnd_5002961 2568923688698505625779307 := by
  unfold tailWord_5002961
  simp only [CollatzResearch.WordTrace]
  refine ⟨182472978428134209558648737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121648652285422806372432491 182472978428134209558648737)
  ·
    refine ⟨136854733821100657168986553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182472978428134209558648737 136854733821100657168986553)
    ·
      refine ⟨102641050365825492876739915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136854733821100657168986553 102641050365825492876739915)
      ·
        refine ⟨153961575548738239315109873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102641050365825492876739915 153961575548738239315109873)
        ·
          refine ⟨115471181661553679486332405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153961575548738239315109873 115471181661553679486332405)
          ·
            refine ⟨10825423280770657451843663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115471181661553679486332405 10825423280770657451843663)
            ·
              refine ⟨16238134921155986177765495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10825423280770657451843663 16238134921155986177765495)
              ·
                refine ⟨24357202381733979266648243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16238134921155986177765495 24357202381733979266648243)
                ·
                  refine ⟨36535803572600968899972365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24357202381733979266648243 36535803572600968899972365)
                  ·
                    refine ⟨13700926339725363337489637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36535803572600968899972365 13700926339725363337489637)
                    ·
                      refine ⟨2568923688698505625779307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13700926339725363337489637 2568923688698505625779307)
                      ·
                        rfl

theorem cell23_5002961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_5002961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002961 prefixEnd_5002961 := by exact prefixLift 5002961
  have htrace : WordTrace (prefixWord ++ tailWord_5002961) baseStart_5002961 baseEnd_5002961 := by
    simpa [prefixWord, tailWord_5002961, baseEnd_5002961] using wordTrace_append hprefix tailTrace_5002961
  have hstable : (prefixWord ++ tailWord_5002961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002961).length < 2 ^ (prefixWord ++ tailWord_5002961).sum := by decide
  have hdescent : baseEnd_5002961 < baseStart_5002961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5002998 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_5002998 : Nat := 118140960795 + 5002998 * 2 ^ 59
def prefixEnd_5002998 : Nat := 4983230072969 + 3 ^ 40 * 5002998 * 2
def baseEnd_5002998 : Nat := 2568942687482721981016637

theorem tailTrace_5002998 : CollatzResearch.WordTrace tailWord_5002998 prefixEnd_5002998 2568942687482721981016637 := by
  unfold tailWord_5002998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11404645495562510304859103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121649551952666776585163765 11404645495562510304859103)
  ·
    refine ⟨17106968243343765457288655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11404645495562510304859103 17106968243343765457288655)
    ·
      refine ⟨25660452365015648185932983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17106968243343765457288655 25660452365015648185932983)
      ·
        refine ⟨38490678547523472278899475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25660452365015648185932983 38490678547523472278899475)
        ·
          refine ⟨57736017821285208418349213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38490678547523472278899475 57736017821285208418349213)
          ·
            refine ⟨21651006682981953156880955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57736017821285208418349213 21651006682981953156880955)
            ·
              refine ⟨32476510024472929735321433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21651006682981953156880955 32476510024472929735321433)
              ·
                refine ⟨24357382518354697301491075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32476510024472929735321433 24357382518354697301491075)
                ·
                  refine ⟨36536073777532045952236613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24357382518354697301491075 36536073777532045952236613)
                  ·
                    refine ⟨6850513833287258616044365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36536073777532045952236613 6850513833287258616044365)
                    ·
                      refine ⟨2568942687482721981016637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6850513833287258616044365 2568942687482721981016637)
                      ·
                        rfl

theorem cell23_5002998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_5002998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5002998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5002998 prefixEnd_5002998 := by exact prefixLift 5002998
  have htrace : WordTrace (prefixWord ++ tailWord_5002998) baseStart_5002998 baseEnd_5002998 := by
    simpa [prefixWord, tailWord_5002998, baseEnd_5002998] using wordTrace_append hprefix tailTrace_5002998
  have hstable : (prefixWord ++ tailWord_5002998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5002998).length < 2 ^ (prefixWord ++ tailWord_5002998).sum := by decide
  have hdescent : baseEnd_5002998 < baseStart_5002998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5002998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003045 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_5003045 : Nat := 118140960795 + 5003045 * 2 ^ 59
def prefixEnd_5003045 : Nat := 4983230072969 + 3 ^ 40 * 5003045 * 2
def baseEnd_5003045 : Nat := 2568966821073483297128921

theorem tailTrace_5003045 : CollatzResearch.WordTrace tailWord_5003045 prefixEnd_5003045 2568966821073483297128921 := by
  unfold tailWord_5003045
  simp only [CollatzResearch.WordTrace]
  refine ⟨182476042159829891904706589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121650694773219927936471059 182476042159829891904706589)
  ·
    refine ⟨68428515809936209464264971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182476042159829891904706589 68428515809936209464264971)
    ·
      refine ⟨102642773714904314196397457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68428515809936209464264971 102642773714904314196397457)
      ·
        refine ⟨76982080286178235647298093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102642773714904314196397457 76982080286178235647298093)
        ·
          refine ⟨28868280107316838367736785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76982080286178235647298093 28868280107316838367736785)
          ·
            refine ⟨21651210080487628775802589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28868280107316838367736785 21651210080487628775802589)
            ·
              refine ⟨8119203780182860790925971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21651210080487628775802589 8119203780182860790925971)
              ·
                refine ⟨12178805670274291186388957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8119203780182860790925971 12178805670274291186388957)
                ·
                  refine ⟨4567052126352859194895859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12178805670274291186388957 4567052126352859194895859)
                  ·
                    refine ⟨6850578189529288792343789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4567052126352859194895859 6850578189529288792343789)
                    ·
                      refine ⟨2568966821073483297128921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6850578189529288792343789 2568966821073483297128921)
                      ·
                        rfl

theorem cell23_5003045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_5003045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003045 prefixEnd_5003045 := by exact prefixLift 5003045
  have htrace : WordTrace (prefixWord ++ tailWord_5003045) baseStart_5003045 baseEnd_5003045 := by
    simpa [prefixWord, tailWord_5003045, baseEnd_5003045] using wordTrace_append hprefix tailTrace_5003045
  have hstable : (prefixWord ++ tailWord_5003045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003045).length < 2 ^ (prefixWord ++ tailWord_5003045).sum := by decide
  have hdescent : baseEnd_5003045 < baseStart_5003045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003065 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 3, 5]
def baseStart_5003065 : Nat := 118140960795 + 5003065 * 2 ^ 59
def prefixEnd_5003065 : Nat := 4983230072969 + 3 ^ 40 * 5003065 * 2
def baseEnd_5003065 : Nat := 856325696895524406292943

theorem tailTrace_5003065 : CollatzResearch.WordTrace tailWord_5003065 prefixEnd_5003065 856325696895524406292943 := by
  unfold tailWord_5003065
  simp only [CollatzResearch.WordTrace]
  refine ⟨182476771619757435320434649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121651181079838290213623099 182476771619757435320434649)
  ·
    refine ⟨136857578714818076490325987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182476771619757435320434649 136857578714818076490325987)
    ·
      refine ⟨205286368072227114735488981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136857578714818076490325987 205286368072227114735488981)
      ·
        refine ⟨4811399251692823001613023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 205286368072227114735488981 4811399251692823001613023)
        ·
          refine ⟨7217098877539234502419535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4811399251692823001613023 7217098877539234502419535)
          ·
            refine ⟨10825648316308851753629303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7217098877539234502419535 10825648316308851753629303)
            ·
              refine ⟨16238472474463277630443955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10825648316308851753629303 16238472474463277630443955)
              ·
                refine ⟨24357708711694916445665933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16238472474463277630443955 24357708711694916445665933)
                ·
                  refine ⟨9134140766885593667124725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24357708711694916445665933 9134140766885593667124725)
                  ·
                    refine ⟨856325696895524406292943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9134140766885593667124725 856325696895524406292943)
                    ·
                      rfl

theorem cell23_5003065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 5].length) (baseStart_5003065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003065 prefixEnd_5003065 := by exact prefixLift 5003065
  have htrace : WordTrace (prefixWord ++ tailWord_5003065) baseStart_5003065 baseEnd_5003065 := by
    simpa [prefixWord, tailWord_5003065, baseEnd_5003065] using wordTrace_append hprefix tailTrace_5003065
  have hstable : (prefixWord ++ tailWord_5003065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003065).length < 2 ^ (prefixWord ++ tailWord_5003065).sum := by decide
  have hdescent : baseEnd_5003065 < baseStart_5003065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003068 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_5003068 : Nat := 118140960795 + 5003068 * 2 ^ 59
def prefixEnd_5003068 : Nat := 4983230072969 + 3 ^ 40 * 5003068 * 2
def baseEnd_5003068 : Nat := 2568978631128536707141315

theorem tailTrace_5003068 : CollatzResearch.WordTrace tailWord_5003068 prefixEnd_5003068 2568978631128536707141315 := by
  unfold tailWord_5003068
  simp only [CollatzResearch.WordTrace]
  refine ⟨91238440519373283416396929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121651254025831044555195905 91238440519373283416396929)
  ·
    refine ⟨68428830389529962562297697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91238440519373283416396929 68428830389529962562297697)
    ·
      refine ⟨51321622792147471921723273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68428830389529962562297697 51321622792147471921723273)
      ·
        refine ⟨38491217094110603941292455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51321622792147471921723273 38491217094110603941292455)
        ·
          refine ⟨57736825641165905911938683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38491217094110603941292455 57736825641165905911938683)
          ·
            refine ⟨86605238461748858867908025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57736825641165905911938683 86605238461748858867908025)
            ·
              refine ⟨64953928846311644150931019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86605238461748858867908025 64953928846311644150931019)
              ·
                refine ⟨97430893269467466226396529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64953928846311644150931019 97430893269467466226396529)
                ·
                  refine ⟨73073169952100599669797397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97430893269467466226396529 73073169952100599669797397)
                  ·
                    refine ⟨3425304841504715609521753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73073169952100599669797397 3425304841504715609521753)
                    ·
                      refine ⟨2568978631128536707141315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425304841504715609521753 2568978631128536707141315)
                      ·
                        rfl

theorem cell23_5003068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_5003068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003068 prefixEnd_5003068 := by exact prefixLift 5003068
  have htrace : WordTrace (prefixWord ++ tailWord_5003068) baseStart_5003068 baseEnd_5003068 := by
    simpa [prefixWord, tailWord_5003068, baseEnd_5003068] using wordTrace_append hprefix tailTrace_5003068
  have hstable : (prefixWord ++ tailWord_5003068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003068).length < 2 ^ (prefixWord ++ tailWord_5003068).sum := by decide
  have hdescent : baseEnd_5003068 < baseStart_5003068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003121 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 2, 7]
def baseStart_5003121 : Nat := 118140960795 + 5003121 * 2 ^ 59
def prefixEnd_5003121 : Nat := 4983230072969 + 3 ^ 40 * 5003121 * 2
def baseEnd_5003121 : Nat := 856335281867741666592857

theorem tailTrace_5003121 : CollatzResearch.WordTrace tailWord_5003121 prefixEnd_5003121 856335281867741666592857 := by
  unfold tailWord_5003121
  simp only [CollatzResearch.WordTrace]
  refine ⟨182478814107554556884473217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121652542738369704589648811 182478814107554556884473217)
  ·
    refine ⟨136859110580665917663354913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182478814107554556884473217 136859110580665917663354913)
    ·
      refine ⟨102644332935499438247516185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136859110580665917663354913 102644332935499438247516185)
      ·
        refine ⟨76983249701624578685637139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102644332935499438247516185 76983249701624578685637139)
        ·
          refine ⟨115474874552436868028455709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76983249701624578685637139 115474874552436868028455709)
          ·
            refine ⟨43303077957163825510670891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115474874552436868028455709 43303077957163825510670891)
            ·
              refine ⟨64954616935745738266006337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43303077957163825510670891 64954616935745738266006337)
              ·
                refine ⟨48715962701809303699504753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64954616935745738266006337 48715962701809303699504753)
                ·
                  refine ⟨36536972026356977774628565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48715962701809303699504753 36536972026356977774628565)
                  ·
                    refine ⟨856335281867741666592857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36536972026356977774628565 856335281867741666592857)
                    ·
                      rfl

theorem cell23_5003121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_5003121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003121 prefixEnd_5003121 := by exact prefixLift 5003121
  have htrace : WordTrace (prefixWord ++ tailWord_5003121) baseStart_5003121 baseEnd_5003121 := by
    simpa [prefixWord, tailWord_5003121, baseEnd_5003121] using wordTrace_append hprefix tailTrace_5003121
  have hstable : (prefixWord ++ tailWord_5003121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003121).length < 2 ^ (prefixWord ++ tailWord_5003121).sum := by decide
  have hdescent : baseEnd_5003121 < baseStart_5003121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003131 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 5]
def baseStart_5003131 : Nat := 118140960795 + 5003131 * 2 ^ 59
def prefixEnd_5003131 : Nat := 4983230072969 + 3 ^ 40 * 5003131 * 2
def baseEnd_5003131 : Nat := 2569010980409769960653525

theorem tailTrace_5003131 : CollatzResearch.WordTrace tailWord_5003131 prefixEnd_5003131 2569010980409769960653525 := by
  unfold tailWord_5003131
  simp only [CollatzResearch.WordTrace]
  refine ⟨182479178837518328592337247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121652785891678885728224831 182479178837518328592337247)
  ·
    refine ⟨273718768256277492888505871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182479178837518328592337247 273718768256277492888505871)
    ·
      refine ⟨410578152384416239332758807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273718768256277492888505871 410578152384416239332758807)
      ·
        refine ⟨615867228576624358999138211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410578152384416239332758807 615867228576624358999138211)
        ·
          refine ⟨923800842864936538498707317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615867228576624358999138211 923800842864936538498707317)
          ·
            refine ⟨86606329018587800484253811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 923800842864936538498707317 86606329018587800484253811)
            ·
              refine ⟨129909493527881700726380717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86606329018587800484253811 129909493527881700726380717)
              ·
                refine ⟨48716060072955637772392769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129909493527881700726380717 48716060072955637772392769)
                ·
                  refine ⟨36537045054716728329294577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48716060072955637772392769 36537045054716728329294577)
                  ·
                    refine ⟨27402783791037546246970933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36537045054716728329294577 27402783791037546246970933)
                    ·
                      refine ⟨2569010980409769960653525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27402783791037546246970933 2569010980409769960653525)
                      ·
                        rfl

theorem cell23_5003131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_5003131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003131 prefixEnd_5003131 := by exact prefixLift 5003131
  have htrace : WordTrace (prefixWord ++ tailWord_5003131) baseStart_5003131 baseEnd_5003131 := by
    simpa [prefixWord, tailWord_5003131, baseEnd_5003131] using wordTrace_append hprefix tailTrace_5003131
  have hstable : (prefixWord ++ tailWord_5003131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003131).length < 2 ^ (prefixWord ++ tailWord_5003131).sum := by decide
  have hdescent : baseEnd_5003131 < baseStart_5003131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003166 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5003166 : Nat := 118140960795 + 5003166 * 2 ^ 59
def prefixEnd_5003166 : Nat := 4983230072969 + 3 ^ 40 * 5003166 * 2
def baseEnd_5003166 : Nat := 2569028952232677323715865

theorem tailTrace_5003166 : CollatzResearch.WordTrace tailWord_5003166 prefixEnd_5003166 2569028952232677323715865 := by
  unfold tailWord_5003166
  simp only [CollatzResearch.WordTrace]
  refine ⟨22810056924048941196232669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121653636928261019713240901 22810056924048941196232669)
  ·
    refine ⟨8553771346518352948587251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22810056924048941196232669 8553771346518352948587251)
    ·
      refine ⟨12830657019777529422880877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8553771346518352948587251 12830657019777529422880877)
      ·
        refine ⟨4811496382416573533580329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12830657019777529422880877 4811496382416573533580329)
        ·
          refine ⟨3608622286812430150185247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4811496382416573533580329 3608622286812430150185247)
          ·
            refine ⟨5412933430218645225277871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608622286812430150185247 5412933430218645225277871)
            ·
              refine ⟨8119400145327967837916807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412933430218645225277871 8119400145327967837916807)
              ·
                refine ⟨12179100217991951756875211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8119400145327967837916807 12179100217991951756875211)
                ·
                  refine ⟨18268650326987927635312817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12179100217991951756875211 18268650326987927635312817)
                  ·
                    refine ⟨13701487745240945726484613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18268650326987927635312817 13701487745240945726484613)
                    ·
                      refine ⟨2569028952232677323715865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13701487745240945726484613 2569028952232677323715865)
                      ·
                        rfl

theorem cell23_5003166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5003166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003166 prefixEnd_5003166 := by exact prefixLift 5003166
  have htrace : WordTrace (prefixWord ++ tailWord_5003166) baseStart_5003166 baseEnd_5003166 := by
    simpa [prefixWord, tailWord_5003166, baseEnd_5003166] using wordTrace_append hprefix tailTrace_5003166
  have hstable : (prefixWord ++ tailWord_5003166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003166).length < 2 ^ (prefixWord ++ tailWord_5003166).sum := by decide
  have hdescent : baseEnd_5003166 < baseStart_5003166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003169 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5003169 : Nat := 118140960795 + 5003169 * 2 ^ 59
def prefixEnd_5003169 : Nat := 4983230072969 + 3 ^ 40 * 5003169 * 2
def baseEnd_5003169 : Nat := 2569030492674640811978351

theorem tailTrace_5003169 : CollatzResearch.WordTrace tailWord_5003169 prefixEnd_5003169 2569030492674640811978351 := by
  unfold tailWord_5003169
  simp only [CollatzResearch.WordTrace]
  refine ⟨182480564811380661082220561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121653709874253774054813707 182480564811380661082220561)
  ·
    refine ⟨136860423608535495811665421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182480564811380661082220561 136860423608535495811665421)
    ·
      refine ⟨51322658853200810929374533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136860423608535495811665421 51322658853200810929374533)
      ·
        refine ⟨9622998534975152049257725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51322658853200810929374533 9622998534975152049257725)
        ·
          refine ⟨3608624450615682018471647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9622998534975152049257725 3608624450615682018471647)
          ·
            refine ⟨5412936675923523027707471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608624450615682018471647 5412936675923523027707471)
            ·
              refine ⟨8119405013885284541561207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412936675923523027707471 8119405013885284541561207)
              ·
                refine ⟨12179107520827926812341811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8119405013885284541561207 12179107520827926812341811)
                ·
                  refine ⟨18268661281241890218512717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12179107520827926812341811 18268661281241890218512717)
                  ·
                    refine ⟨6850747980465708831942269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18268661281241890218512717 6850747980465708831942269)
                    ·
                      refine ⟨2569030492674640811978351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6850747980465708831942269 2569030492674640811978351)
                      ·
                        rfl

theorem cell23_5003169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5003169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003169 prefixEnd_5003169 := by exact prefixLift 5003169
  have htrace : WordTrace (prefixWord ++ tailWord_5003169) baseStart_5003169 baseEnd_5003169 := by
    simpa [prefixWord, tailWord_5003169, baseEnd_5003169] using wordTrace_append hprefix tailTrace_5003169
  have hstable : (prefixWord ++ tailWord_5003169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003169).length < 2 ^ (prefixWord ++ tailWord_5003169).sum := by decide
  have hdescent : baseEnd_5003169 < baseStart_5003169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003248 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_5003248 : Nat := 118140960795 + 5003248 * 2 ^ 59
def prefixEnd_5003248 : Nat := 4983230072969 + 3 ^ 40 * 5003248 * 2
def baseEnd_5003248 : Nat := 2569071057646346002890487

theorem tailTrace_5003248 : CollatzResearch.WordTrace tailWord_5003248 prefixEnd_5003248 2569071057646346002890487 := by
  unfold tailWord_5003248
  simp only [CollatzResearch.WordTrace]
  refine ⟨91241723089047228787173199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121655630785396305049564265 91241723089047228787173199)
  ·
    refine ⟨136862584633570843180759799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91241723089047228787173199 136862584633570843180759799)
    ·
      refine ⟨205293876950356264771139699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136862584633570843180759799 205293876950356264771139699)
      ·
        refine ⟨307940815425534397156709549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205293876950356264771139699 307940815425534397156709549)
        ·
          refine ⟨115477805784575398933766081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307940815425534397156709549 115477805784575398933766081)
          ·
            refine ⟨86608354338431549200324561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115477805784575398933766081 86608354338431549200324561)
            ·
              refine ⟨64956265753823661900243421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86608354338431549200324561 64956265753823661900243421)
              ·
                refine ⟨24358599657683873212591283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64956265753823661900243421 24358599657683873212591283)
                ·
                  refine ⟨36537899486525809818886925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24358599657683873212591283 36537899486525809818886925)
                  ·
                    refine ⟨13701712307447178682082597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36537899486525809818886925 13701712307447178682082597)
                    ·
                      refine ⟨2569071057646346002890487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13701712307447178682082597 2569071057646346002890487)
                      ·
                        rfl

theorem cell23_5003248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_5003248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003248 prefixEnd_5003248 := by exact prefixLift 5003248
  have htrace : WordTrace (prefixWord ++ tailWord_5003248) baseStart_5003248 baseEnd_5003248 := by
    simpa [prefixWord, tailWord_5003248, baseEnd_5003248] using wordTrace_append hprefix tailTrace_5003248
  have hstable : (prefixWord ++ tailWord_5003248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003248).length < 2 ^ (prefixWord ++ tailWord_5003248).sum := by decide
  have hdescent : baseEnd_5003248 < baseStart_5003248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003262 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_5003262 : Nat := 118140960795 + 5003262 * 2 ^ 59
def prefixEnd_5003262 : Nat := 4983230072969 + 3 ^ 40 * 5003262 * 2
def baseEnd_5003262 : Nat := 856359415458502982705141

theorem tailTrace_5003262 : CollatzResearch.WordTrace tailWord_5003262 prefixEnd_5003262 856359415458502982705141 := by
  unfold tailWord_5003262
  simp only [CollatzResearch.WordTrace]
  refine ⟨22810494600005467245669505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121655971200029158643570693 22810494600005467245669505)
  ·
    refine ⟨17107870950004100434252129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22810494600005467245669505 17107870950004100434252129)
    ·
      refine ⟨12830903212503075325689097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17107870950004100434252129 12830903212503075325689097)
      ·
        refine ⟨9623177409377306494266823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12830903212503075325689097 9623177409377306494266823)
        ·
          refine ⟨14434766114065959741400235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9623177409377306494266823 14434766114065959741400235)
          ·
            refine ⟨21652149171098939612100353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14434766114065959741400235 21652149171098939612100353)
            ·
              refine ⟨16239111878324204709075265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21652149171098939612100353 16239111878324204709075265)
              ·
                refine ⟨12179333908743153531806449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16239111878324204709075265 12179333908743153531806449)
                ·
                  refine ⟨9134500431557365148854837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12179333908743153531806449 9134500431557365148854837)
                  ·
                    refine ⟨856359415458502982705141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9134500431557365148854837 856359415458502982705141)
                    ·
                      rfl

theorem cell23_5003262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_5003262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003262 prefixEnd_5003262 := by exact prefixLift 5003262
  have htrace : WordTrace (prefixWord ++ tailWord_5003262) baseStart_5003262 baseEnd_5003262 := by
    simpa [prefixWord, tailWord_5003262, baseEnd_5003262] using wordTrace_append hprefix tailTrace_5003262
  have hstable : (prefixWord ++ tailWord_5003262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003262).length < 2 ^ (prefixWord ++ tailWord_5003262).sum := by decide
  have hdescent : baseEnd_5003262 < baseStart_5003262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003265 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_5003265 : Nat := 118140960795 + 5003265 * 2 ^ 59
def prefixEnd_5003265 : Nat := 4983230072969 + 3 ^ 40 * 5003265 * 2
def baseEnd_5003265 : Nat := 2569079786817472436377909

theorem tailTrace_5003265 : CollatzResearch.WordTrace tailWord_5003265 prefixEnd_5003265 2569079786817472436377909 := by
  unfold tailWord_5003265
  simp only [CollatzResearch.WordTrace]
  refine ⟨182484066219032869477715249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121656044146021912985143499 182484066219032869477715249)
  ·
    refine ⟨136863049664274652108286437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182484066219032869477715249 136863049664274652108286437)
    ·
      refine ⟨25661821812051497270303707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136863049664274652108286437 25661821812051497270303707)
      ·
        refine ⟨38492732718077245905455561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25661821812051497270303707 38492732718077245905455561)
        ·
          refine ⟨28869549538557934429091671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38492732718077245905455561 28869549538557934429091671)
          ·
            refine ⟨43304324307836901643637507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28869549538557934429091671 43304324307836901643637507)
            ·
              refine ⟨64956486461755352465456261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43304324307836901643637507 64956486461755352465456261)
              ·
                refine ⟨12179341211579128587273049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64956486461755352465456261 12179341211579128587273049)
                ·
                  refine ⟨9134505908684346440454787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12179341211579128587273049 9134505908684346440454787)
                  ·
                    refine ⟨13701758863026519660682181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9134505908684346440454787 13701758863026519660682181)
                    ·
                      refine ⟨2569079786817472436377909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13701758863026519660682181 2569079786817472436377909)
                      ·
                        rfl

theorem cell23_5003265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_5003265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003265 prefixEnd_5003265 := by exact prefixLift 5003265
  have htrace : WordTrace (prefixWord ++ tailWord_5003265) baseStart_5003265 baseEnd_5003265 := by
    simpa [prefixWord, tailWord_5003265, baseEnd_5003265] using wordTrace_append hprefix tailTrace_5003265
  have hstable : (prefixWord ++ tailWord_5003265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003265).length < 2 ^ (prefixWord ++ tailWord_5003265).sum := by decide
  have hdescent : baseEnd_5003265 < baseStart_5003265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003275 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 3, 4]
def baseStart_5003275 : Nat := 118140960795 + 5003275 * 2 ^ 59
def prefixEnd_5003275 : Nat := 4983230072969 + 3 ^ 40 * 5003275 * 2
def baseEnd_5003275 : Nat := 856361640541339132417621

theorem tailTrace_5003275 : CollatzResearch.WordTrace tailWord_5003275 prefixEnd_5003275 856361640541339132417621 := by
  unfold tailWord_5003275
  simp only [CollatzResearch.WordTrace]
  refine ⟨182484430948996641185579279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121656287299331094123719519 182484430948996641185579279)
  ·
    refine ⟨273726646423494961778368919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182484430948996641185579279 273726646423494961778368919)
    ·
      refine ⟨410589969635242442667553379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273726646423494961778368919 410589969635242442667553379)
      ·
        refine ⟨615884954452863664001330069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410589969635242442667553379 615884954452863664001330069)
        ·
          refine ⟨28869607239977984250062347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 615884954452863664001330069 28869607239977984250062347)
          ·
            refine ⟨43304410859966976375093521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28869607239977984250062347 43304410859966976375093521)
            ·
              refine ⟨32478308144975232281320141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43304410859966976375093521 32478308144975232281320141)
              ·
                refine ⟨12179365554365712105495053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32478308144975232281320141 12179365554365712105495053)
                ·
                  refine ⟨4567262082887142039560645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12179365554365712105495053 4567262082887142039560645)
                  ·
                    refine ⟨856361640541339132417621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4567262082887142039560645 856361640541339132417621)
                    ·
                      rfl

theorem cell23_5003275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 4].length) (baseStart_5003275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003275 prefixEnd_5003275 := by exact prefixLift 5003275
  have htrace : WordTrace (prefixWord ++ tailWord_5003275) baseStart_5003275 baseEnd_5003275 := by
    simpa [prefixWord, tailWord_5003275, baseEnd_5003275] using wordTrace_append hprefix tailTrace_5003275
  have hstable : (prefixWord ++ tailWord_5003275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003275).length < 2 ^ (prefixWord ++ tailWord_5003275).sum := by decide
  have hdescent : baseEnd_5003275 < baseStart_5003275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003292 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_5003292 : Nat := 118140960795 + 5003292 * 2 ^ 59
def prefixEnd_5003292 : Nat := 4983230072969 + 3 ^ 40 * 5003292 * 2
def baseEnd_5003292 : Nat := 856364550265047943580095

theorem tailTrace_5003292 : CollatzResearch.WordTrace tailWord_5003292 prefixEnd_5003292 856364550265047943580095 := by
  unfold tailWord_5003292
  simp only [CollatzResearch.WordTrace]
  refine ⟨91242525494967526544474065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121656700659956702059298753 91242525494967526544474065)
  ·
    refine ⟨68431894121225644908355549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91242525494967526544474065 68431894121225644908355549)
    ·
      refine ⟨25661960295459616840633331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68431894121225644908355549 25661960295459616840633331)
      ·
        refine ⟨38492940443189425260949997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25661960295459616840633331 38492940443189425260949997)
        ·
          refine ⟨14434852666196034472856249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38492940443189425260949997 14434852666196034472856249)
          ·
            refine ⟨10826139499647025854642187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14434852666196034472856249 10826139499647025854642187)
            ·
              refine ⟨16239209249470538781963281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10826139499647025854642187 16239209249470538781963281)
              ·
                refine ⟨12179406937102904086472461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16239209249470538781963281 12179406937102904086472461)
                ·
                  refine ⟨4567277601413589032427173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12179406937102904086472461 4567277601413589032427173)
                  ·
                    refine ⟨856364550265047943580095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4567277601413589032427173 856364550265047943580095)
                    ·
                      rfl

theorem cell23_5003292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_5003292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003292 prefixEnd_5003292 := by exact prefixLift 5003292
  have htrace : WordTrace (prefixWord ++ tailWord_5003292) baseStart_5003292 baseEnd_5003292 := by
    simpa [prefixWord, tailWord_5003292, baseEnd_5003292] using wordTrace_append hprefix tailTrace_5003292
  have hstable : (prefixWord ++ tailWord_5003292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003292).length < 2 ^ (prefixWord ++ tailWord_5003292).sum := by decide
  have hdescent : baseEnd_5003292 < baseStart_5003292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003342 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_5003342 : Nat := 118140960795 + 5003342 * 2 ^ 59
def prefixEnd_5003342 : Nat := 4983230072969 + 3 ^ 40 * 5003342 * 2
def baseEnd_5003342 : Nat := 2569119324827868635115055

theorem tailTrace_5003342 : CollatzResearch.WordTrace tailWord_5003342 prefixEnd_5003342 2569119324827868635115055 := by
  unfold tailWord_5003342
  simp only [CollatzResearch.WordTrace]
  refine ⟨22810859329969238953533535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121657916426502607752178853 22810859329969238953533535)
  ·
    refine ⟨34216288994953858430300303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22810859329969238953533535 34216288994953858430300303)
    ·
      refine ⟨51324433492430787645450455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34216288994953858430300303 51324433492430787645450455)
      ·
        refine ⟨76986650238646181468175683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51324433492430787645450455 76986650238646181468175683)
        ·
          refine ⟨115479975357969272202263525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76986650238646181468175683 115479975357969272202263525)
          ·
            refine ⟨21652495379619238537924411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115479975357969272202263525 21652495379619238537924411)
            ·
              refine ⟨32478743069428857806886617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21652495379619238537924411 32478743069428857806886617)
              ·
                refine ⟨24359057302071643355164963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32478743069428857806886617 24359057302071643355164963)
                ·
                  refine ⟨36538585953107465032747445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24359057302071643355164963 36538585953107465032747445)
                  ·
                    refine ⟨3425492433103824846820073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36538585953107465032747445 3425492433103824846820073)
                    ·
                      refine ⟨2569119324827868635115055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425492433103824846820073 2569119324827868635115055)
                      ·
                        rfl

theorem cell23_5003342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_5003342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003342 prefixEnd_5003342 := by exact prefixLift 5003342
  have htrace : WordTrace (prefixWord ++ tailWord_5003342) baseStart_5003342 baseEnd_5003342 := by
    simpa [prefixWord, tailWord_5003342, baseEnd_5003342] using wordTrace_append hprefix tailTrace_5003342
  have hstable : (prefixWord ++ tailWord_5003342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003342).length < 2 ^ (prefixWord ++ tailWord_5003342).sum := by decide
  have hdescent : baseEnd_5003342 < baseStart_5003342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003352 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 1, 5]
def baseStart_5003352 : Nat := 118140960795 + 5003352 * 2 ^ 59
def prefixEnd_5003352 : Nat := 4983230072969 + 3 ^ 40 * 5003352 * 2
def baseEnd_5003352 : Nat := 856374819878137865330003

theorem tailTrace_5003352 : CollatzResearch.WordTrace tailWord_5003352 prefixEnd_5003352 856374819878137865330003 := by
  unfold tailWord_5003352
  simp only [CollatzResearch.WordTrace]
  refine ⟨91243619684858841668066155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121658159579811788890754873 91243619684858841668066155)
  ·
    refine ⟨136865429527288262502099233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91243619684858841668066155 136865429527288262502099233)
    ·
      refine ⟨102649072145466196876574425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136865429527288262502099233 102649072145466196876574425)
      ·
        refine ⟨76986804109099647657430819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102649072145466196876574425 76986804109099647657430819)
        ·
          refine ⟨115480206163649471486146229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76986804109099647657430819 115480206163649471486146229)
          ·
            refine ⟨10826269327842137951826209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115480206163649471486146229 10826269327842137951826209)
            ·
              refine ⟨8119701995881603463869657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10826269327842137951826209 8119701995881603463869657)
              ·
                refine ⟨6089776496911202597902243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8119701995881603463869657 6089776496911202597902243)
                ·
                  refine ⟨9134664745366803896853365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6089776496911202597902243 9134664745366803896853365)
                  ·
                    refine ⟨856374819878137865330003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9134664745366803896853365 856374819878137865330003)
                    ·
                      rfl

theorem cell23_5003352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_5003352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003352 prefixEnd_5003352 := by exact prefixLift 5003352
  have htrace : WordTrace (prefixWord ++ tailWord_5003352) baseStart_5003352 baseEnd_5003352 := by
    simpa [prefixWord, tailWord_5003352, baseEnd_5003352] using wordTrace_append hprefix tailTrace_5003352
  have hstable : (prefixWord ++ tailWord_5003352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003352).length < 2 ^ (prefixWord ++ tailWord_5003352).sum := by decide
  have hdescent : baseEnd_5003352 < baseStart_5003352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003372 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_5003372 : Nat := 118140960795 + 5003372 * 2 ^ 59
def prefixEnd_5003372 : Nat := 4983230072969 + 3 ^ 40 * 5003372 * 2
def baseEnd_5003372 : Nat := 2569134729247503517739917

theorem tailTrace_5003372 : CollatzResearch.WordTrace tailWord_5003372 prefixEnd_5003372 2569134729247503517739917 := by
  unfold tailWord_5003372
  simp only [CollatzResearch.WordTrace]
  refine ⟨91243984414822613375930185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121658645886430151167906913 91243984414822613375930185)
  ·
    refine ⟨68432988311116960031947639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91243984414822613375930185 68432988311116960031947639)
    ·
      refine ⟨102649482466675440047921459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68432988311116960031947639 102649482466675440047921459)
      ·
        refine ⟨153974223700013160071882189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102649482466675440047921459 153974223700013160071882189)
        ·
          refine ⟨57740333887504935026955821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153974223700013160071882189 57740333887504935026955821)
          ·
            refine ⟨21652625207814350635108433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57740333887504935026955821 21652625207814350635108433)
            ·
              refine ⟨16239468905860762976331325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21652625207814350635108433 16239468905860762976331325)
              ·
                refine ⟨6089800839697786116124247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16239468905860762976331325 6089800839697786116124247)
                ·
                  refine ⟨9134701259546679174186371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6089800839697786116124247 9134701259546679174186371)
                  ·
                    refine ⟨13702051889320018761279557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9134701259546679174186371 13702051889320018761279557)
                    ·
                      refine ⟨2569134729247503517739917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13702051889320018761279557 2569134729247503517739917)
                      ·
                        rfl

theorem cell23_5003372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_5003372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003372 prefixEnd_5003372 := by exact prefixLift 5003372
  have htrace : WordTrace (prefixWord ++ tailWord_5003372) baseStart_5003372 baseEnd_5003372 := by
    simpa [prefixWord, tailWord_5003372, baseEnd_5003372] using wordTrace_append hprefix tailTrace_5003372
  have hstable : (prefixWord ++ tailWord_5003372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003372).length < 2 ^ (prefixWord ++ tailWord_5003372).sum := by decide
  have hdescent : baseEnd_5003372 < baseStart_5003372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003375 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_5003375 : Nat := 118140960795 + 5003375 * 2 ^ 59
def prefixEnd_5003375 : Nat := 4983230072969 + 3 ^ 40 * 5003375 * 2
def baseEnd_5003375 : Nat := 2569136269689467006002403

theorem tailTrace_5003375 : CollatzResearch.WordTrace tailWord_5003375 prefixEnd_5003375 2569136269689467006002403 := by
  unfold tailWord_5003375
  simp only [CollatzResearch.WordTrace]
  refine ⟨182488078248634358264219579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121658718832422905509479719 182488078248634358264219579)
  ·
    refine ⟨273732117372951537396329369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182488078248634358264219579 273732117372951537396329369)
    ·
      refine ⟨205299088029713653047247027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273732117372951537396329369 205299088029713653047247027)
      ·
        refine ⟨307948632044570479570870541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205299088029713653047247027 307948632044570479570870541)
        ·
          refine ⟨115480737016713929839076453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307948632044570479570870541 115480737016713929839076453)
          ·
            refine ⟨21652638190633861844826835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115480737016713929839076453 21652638190633861844826835)
            ·
              refine ⟨32478957285950792767240253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21652638190633861844826835 32478957285950792767240253)
              ·
                refine ⟨12179608982231547287715095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32478957285950792767240253 12179608982231547287715095)
                ·
                  refine ⟨18269413473347320931572643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12179608982231547287715095 18269413473347320931572643)
                  ·
                    refine ⟨27404120210020981397358965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18269413473347320931572643 27404120210020981397358965)
                    ·
                      refine ⟨2569136269689467006002403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27404120210020981397358965 2569136269689467006002403)
                      ·
                        rfl

theorem cell23_5003375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_5003375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003375 prefixEnd_5003375 := by exact prefixLift 5003375
  have htrace : WordTrace (prefixWord ++ tailWord_5003375) baseStart_5003375 baseEnd_5003375 := by
    simpa [prefixWord, tailWord_5003375, baseEnd_5003375] using wordTrace_append hprefix tailTrace_5003375
  have hstable : (prefixWord ++ tailWord_5003375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003375).length < 2 ^ (prefixWord ++ tailWord_5003375).sum := by decide
  have hdescent : baseEnd_5003375 < baseStart_5003375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003385 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_5003385 : Nat := 118140960795 + 5003385 * 2 ^ 59
def prefixEnd_5003385 : Nat := 4983230072969 + 3 ^ 40 * 5003385 * 2
def baseEnd_5003385 : Nat := 2569141404496011966877357

theorem tailTrace_5003385 : CollatzResearch.WordTrace tailWord_5003385 prefixEnd_5003385 2569141404496011966877357 := by
  unfold tailWord_5003385
  simp only [CollatzResearch.WordTrace]
  refine ⟨182488442978598129972083609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121658961985732086648055739 182488442978598129972083609)
  ·
    refine ⟨136866332233948597479062707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182488442978598129972083609 136866332233948597479062707)
    ·
      refine ⟨205299498350922896218594061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136866332233948597479062707 205299498350922896218594061)
      ·
        refine ⟨76987311881596086081972773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205299498350922896218594061 76987311881596086081972773)
        ·
          refine ⟨14435120977799266140369895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76987311881596086081972773 14435120977799266140369895)
          ·
            refine ⟨21652681466698899210554843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14435120977799266140369895 21652681466698899210554843)
            ·
              refine ⟨32479022200048348815832265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21652681466698899210554843 32479022200048348815832265)
              ·
                refine ⟨24359266650036261611874199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32479022200048348815832265 24359266650036261611874199)
                ·
                  refine ⟨36538899975054392417811299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24359266650036261611874199 36538899975054392417811299)
                  ·
                    refine ⟨54808349962581588626716949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36538899975054392417811299 54808349962581588626716949)
                    ·
                      refine ⟨2569141404496011966877357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54808349962581588626716949 2569141404496011966877357)
                      ·
                        rfl

theorem cell23_5003385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_5003385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003385 prefixEnd_5003385 := by exact prefixLift 5003385
  have htrace : WordTrace (prefixWord ++ tailWord_5003385) baseStart_5003385 baseEnd_5003385 := by
    simpa [prefixWord, tailWord_5003385, baseEnd_5003385] using wordTrace_append hprefix tailTrace_5003385
  have hstable : (prefixWord ++ tailWord_5003385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003385).length < 2 ^ (prefixWord ++ tailWord_5003385).sum := by decide
  have hdescent : baseEnd_5003385 < baseStart_5003385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003395 : List Nat := [1, 1, 1, 3, 3, 4, 2, 8]
def baseStart_5003395 : Nat := 118140960795 + 5003395 * 2 ^ 59
def prefixEnd_5003395 : Nat := 4983230072969 + 3 ^ 40 * 5003395 * 2
def baseEnd_5003395 : Nat := 95153575529724330657493

theorem tailTrace_5003395 : CollatzResearch.WordTrace tailWord_5003395 prefixEnd_5003395 95153575529724330657493 := by
  unfold tailWord_5003395
  simp only [CollatzResearch.WordTrace]
  refine ⟨182488807708561901679947639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121659205139041267786631759 182488807708561901679947639)
  ·
    refine ⟨273733211562842852519921459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182488807708561901679947639 273733211562842852519921459)
    ·
      refine ⟨410599817344264278779882189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273733211562842852519921459 410599817344264278779882189)
      ·
        refine ⟨153974931504099104542455821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410599817344264278779882189 153974931504099104542455821)
        ·
          refine ⟨57740599314037164203420933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153974931504099104542455821 57740599314037164203420933)
          ·
            refine ⟨10826362371381968288141425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57740599314037164203420933 10826362371381968288141425)
            ·
              refine ⟨8119771778536476216106069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10826362371381968288141425 8119771778536476216106069)
              ·
                refine ⟨95153575529724330657493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8119771778536476216106069 95153575529724330657493)
                ·
                  rfl

theorem cell23_5003395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 8].length) (baseStart_5003395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003395 prefixEnd_5003395 := by exact prefixLift 5003395
  have htrace : WordTrace (prefixWord ++ tailWord_5003395) baseStart_5003395 baseEnd_5003395 := by
    simpa [prefixWord, tailWord_5003395, baseEnd_5003395] using wordTrace_append hprefix tailTrace_5003395
  have hstable : (prefixWord ++ tailWord_5003395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003395).length < 2 ^ (prefixWord ++ tailWord_5003395).sum := by decide
  have hdescent : baseEnd_5003395 < baseStart_5003395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003399 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 2, 4]
def baseStart_5003399 : Nat := 118140960795 + 5003399 * 2 ^ 59
def prefixEnd_5003399 : Nat := 4983230072969 + 3 ^ 40 * 5003399 * 2
def baseEnd_5003399 : Nat := 856382864408391637367431

theorem tailTrace_5003399 : CollatzResearch.WordTrace tailWord_5003399 prefixEnd_5003399 856382864408391637367431 := by
  unfold tailWord_5003399
  simp only [CollatzResearch.WordTrace]
  refine ⟨182488953600547410363093251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121659302400364940242062167 182488953600547410363093251)
  ·
    refine ⟨273733430400821115544639877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182488953600547410363093251 273733430400821115544639877)
    ·
      refine ⟨51325018200153959164619977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273733430400821115544639877 51325018200153959164619977)
      ·
        refine ⟨38493763650115469373464983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51325018200153959164619977 38493763650115469373464983)
        ·
          refine ⟨57740645475173204060197475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38493763650115469373464983 57740645475173204060197475)
          ·
            refine ⟨86610968212759806090296213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57740645475173204060197475 86610968212759806090296213)
            ·
              refine ⟨4059889134973115910482635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86610968212759806090296213 4059889134973115910482635)
              ·
                refine ⟨6089833702459673865723953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4059889134973115910482635 6089833702459673865723953)
                ·
                  refine ⟨4567375276844755399292965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6089833702459673865723953 4567375276844755399292965)
                  ·
                    refine ⟨856382864408391637367431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4567375276844755399292965 856382864408391637367431)
                    ·
                      rfl

theorem cell23_5003399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_5003399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003399 prefixEnd_5003399 := by exact prefixLift 5003399
  have htrace : WordTrace (prefixWord ++ tailWord_5003399) baseStart_5003399 baseEnd_5003399 := by
    simpa [prefixWord, tailWord_5003399, baseEnd_5003399] using wordTrace_append hprefix tailTrace_5003399
  have hstable : (prefixWord ++ tailWord_5003399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003399).length < 2 ^ (prefixWord ++ tailWord_5003399).sum := by decide
  have hdescent : baseEnd_5003399 < baseStart_5003399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003406 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_5003406 : Nat := 118140960795 + 5003406 * 2 ^ 59
def prefixEnd_5003406 : Nat := 4983230072969 + 3 ^ 40 * 5003406 * 2
def baseEnd_5003406 : Nat := 2569152187589756384714761

theorem tailTrace_5003406 : CollatzResearch.WordTrace tailWord_5003406 prefixEnd_5003406 2569152187589756384714761 := by
  unfold tailWord_5003406
  simp only [CollatzResearch.WordTrace]
  refine ⟨22811151113940256319824759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121659472607681367039065381 22811151113940256319824759)
  ·
    refine ⟨34216726670910384479737139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22811151113940256319824759 34216726670910384479737139)
    ·
      refine ⟨51325090006365576719605709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34216726670910384479737139 51325090006365576719605709)
      ·
        refine ⟨19246908752387091269852141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51325090006365576719605709 19246908752387091269852141)
        ·
          refine ⟨7217590782145159226194553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19246908752387091269852141 7217590782145159226194553)
          ·
            refine ⟨5413193086608869419645915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7217590782145159226194553 5413193086608869419645915)
            ·
              refine ⟨8119789629913304129468873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5413193086608869419645915 8119789629913304129468873)
              ·
                refine ⟨6089842222434978097101655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8119789629913304129468873 6089842222434978097101655)
                ·
                  refine ⟨9134763333652467145652483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6089842222434978097101655 9134763333652467145652483)
                  ·
                    refine ⟨13702145000478700718478725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9134763333652467145652483 13702145000478700718478725)
                    ·
                      refine ⟨2569152187589756384714761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13702145000478700718478725 2569152187589756384714761)
                      ·
                        rfl

theorem cell23_5003406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_5003406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003406 prefixEnd_5003406 := by exact prefixLift 5003406
  have htrace : WordTrace (prefixWord ++ tailWord_5003406) baseStart_5003406 baseEnd_5003406 := by
    simpa [prefixWord, tailWord_5003406, baseEnd_5003406] using wordTrace_append hprefix tailTrace_5003406
  have hstable : (prefixWord ++ tailWord_5003406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003406).length < 2 ^ (prefixWord ++ tailWord_5003406).sum := by decide
  have hdescent : baseEnd_5003406 < baseStart_5003406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003465 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_5003465 : Nat := 118140960795 + 5003465 * 2 ^ 59
def prefixEnd_5003465 : Nat := 4983230072969 + 3 ^ 40 * 5003465 * 2
def baseEnd_5003465 : Nat := 2569182482948371653876989

theorem tailTrace_5003465 : CollatzResearch.WordTrace tailWord_5003465 prefixEnd_5003465 2569182482948371653876989 := by
  unfold tailWord_5003465
  simp only [CollatzResearch.WordTrace]
  refine ⟨182491360818308303634995849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121660907212205535756663899 182491360818308303634995849)
  ·
    refine ⟨136868520613731227726246887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182491360818308303634995849 136868520613731227726246887)
    ·
      refine ⟨205302780920596841589370331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136868520613731227726246887 205302780920596841589370331)
      ·
        refine ⟨307954171380895262384055497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205302780920596841589370331 307954171380895262384055497)
        ·
          refine ⟨230965628535671446788041623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307954171380895262384055497 230965628535671446788041623)
          ·
            refine ⟨346448442803507170182062435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230965628535671446788041623 346448442803507170182062435)
            ·
              refine ⟨519672664205260755273093653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346448442803507170182062435 519672664205260755273093653)
              ·
                refine ⟨24359656134621597903426265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 519672664205260755273093653 24359656134621597903426265)
                ·
                  refine ⟨18269742100966198427569699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24359656134621597903426265 18269742100966198427569699)
                  ·
                    refine ⟨27404613151449297641354549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18269742100966198427569699 27404613151449297641354549)
                    ·
                      refine ⟨2569182482948371653876989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27404613151449297641354549 2569182482948371653876989)
                      ·
                        rfl

theorem cell23_5003465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_5003465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003465 prefixEnd_5003465 := by exact prefixLift 5003465
  have htrace : WordTrace (prefixWord ++ tailWord_5003465) baseStart_5003465 baseEnd_5003465 := by
    simpa [prefixWord, tailWord_5003465, baseEnd_5003465] using wordTrace_append hprefix tailTrace_5003465
  have hstable : (prefixWord ++ tailWord_5003465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003465).length < 2 ^ (prefixWord ++ tailWord_5003465).sum := by decide
  have hdescent : baseEnd_5003465 < baseStart_5003465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003475 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 4]
def baseStart_5003475 : Nat := 118140960795 + 5003475 * 2 ^ 59
def prefixEnd_5003475 : Nat := 4983230072969 + 3 ^ 40 * 5003475 * 2
def baseEnd_5003475 : Nat := 2569187617754916614751943

theorem tailTrace_5003475 : CollatzResearch.WordTrace tailWord_5003475 prefixEnd_5003475 2569187617754916614751943 := by
  unfold tailWord_5003475
  simp only [CollatzResearch.WordTrace]
  refine ⟨182491725548272075342859879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121661150365514716895239919 182491725548272075342859879)
  ·
    refine ⟨273737588322408113014289819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182491725548272075342859879 273737588322408113014289819)
    ·
      refine ⟨410606382483612169521434729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273737588322408113014289819 410606382483612169521434729)
      ·
        refine ⟨307954786862709127141076047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410606382483612169521434729 307954786862709127141076047)
        ·
          refine ⟨461932180294063690711614071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307954786862709127141076047 461932180294063690711614071)
          ·
            refine ⟨692898270441095536067421107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461932180294063690711614071 692898270441095536067421107)
            ·
              refine ⟨1039347405661643304101131661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692898270441095536067421107 1039347405661643304101131661)
              ·
                refine ⟨389755277123116239037924373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1039347405661643304101131661 389755277123116239037924373)
                ·
                  refine ⟨18269778615146073704902705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 389755277123116239037924373 18269778615146073704902705)
                  ·
                    refine ⟨13702333961359555278677029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18269778615146073704902705 13702333961359555278677029)
                    ·
                      refine ⟨2569187617754916614751943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13702333961359555278677029 2569187617754916614751943)
                      ·
                        rfl

theorem cell23_5003475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_5003475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003475 prefixEnd_5003475 := by exact prefixLift 5003475
  have htrace : WordTrace (prefixWord ++ tailWord_5003475) baseStart_5003475 baseEnd_5003475 := by
    simpa [prefixWord, tailWord_5003475, baseEnd_5003475] using wordTrace_append hprefix tailTrace_5003475
  have hstable : (prefixWord ++ tailWord_5003475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003475).length < 2 ^ (prefixWord ++ tailWord_5003475).sum := by decide
  have hdescent : baseEnd_5003475 < baseStart_5003475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003479 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 4, 2, 2]
def baseStart_5003479 : Nat := 118140960795 + 5003479 * 2 ^ 59
def prefixEnd_5003479 : Nat := 4983230072969 + 3 ^ 40 * 5003479 * 2
def baseEnd_5003479 : Nat := 2569189671677534599101925

theorem tailTrace_5003479 : CollatzResearch.WordTrace tailWord_5003479 prefixEnd_5003479 2569189671677534599101925 := by
  unfold tailWord_5003479
  simp only [CollatzResearch.WordTrace]
  refine ⟨182491871440257584026005491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121661247626838389350670327 182491871440257584026005491)
  ·
    refine ⟨273737807160386376039008237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182491871440257584026005491 273737807160386376039008237)
    ·
      refine ⟨102651677685144891014628089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273737807160386376039008237 102651677685144891014628089)
      ·
        refine ⟨76988758263858668260971067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102651677685144891014628089 76988758263858668260971067)
        ·
          refine ⟨115483137395788002391456601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76988758263858668260971067 115483137395788002391456601)
          ·
            refine ⟨86612353046841001793592451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115483137395788002391456601 86612353046841001793592451)
            ·
              refine ⟨129918529570261502690388677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86612353046841001793592451 129918529570261502690388677)
              ·
                refine ⟨24359724294424031754447877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129918529570261502690388677 24359724294424031754447877)
                ·
                  refine ⟨4567448305204505953958977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24359724294424031754447877 4567448305204505953958977)
                  ·
                    refine ⟨3425586228903379465469233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4567448305204505953958977 3425586228903379465469233)
                    ·
                      refine ⟨2569189671677534599101925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425586228903379465469233 2569189671677534599101925)
                      ·
                        rfl

theorem cell23_5003479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_5003479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003479 prefixEnd_5003479 := by exact prefixLift 5003479
  have htrace : WordTrace (prefixWord ++ tailWord_5003479) baseStart_5003479 baseEnd_5003479 := by
    simpa [prefixWord, tailWord_5003479, baseEnd_5003479] using wordTrace_append hprefix tailTrace_5003479
  have hstable : (prefixWord ++ tailWord_5003479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003479).length < 2 ^ (prefixWord ++ tailWord_5003479).sum := by decide
  have hdescent : baseEnd_5003479 < baseStart_5003479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003490 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5003490 : Nat := 118140960795 + 5003490 * 2 ^ 59
def prefixEnd_5003490 : Nat := 4983230072969 + 3 ^ 40 * 5003490 * 2
def baseEnd_5003490 : Nat := 2569195319964734056064375

theorem tailTrace_5003490 : CollatzResearch.WordTrace tailWord_5003490 prefixEnd_5003490 2569195319964734056064375 := by
  unfold tailWord_5003490
  simp only [CollatzResearch.WordTrace]
  refine ⟨45623068160804433226163981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121661515095478488603103949 45623068160804433226163981)
  ·
    refine ⟨17108650560301662459811493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45623068160804433226163981 17108650560301662459811493)
    ·
      refine ⟨3207871980056561711214655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17108650560301662459811493 3207871980056561711214655)
      ·
        refine ⟨4811807970084842566821983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3207871980056561711214655 4811807970084842566821983)
        ·
          refine ⟨7217711955127263850232975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4811807970084842566821983 7217711955127263850232975)
          ·
            refine ⟨10826567932690895775349463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7217711955127263850232975 10826567932690895775349463)
            ·
              refine ⟨16239851899036343663024195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10826567932690895775349463 16239851899036343663024195)
              ·
                refine ⟨24359777848554515494536293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16239851899036343663024195 24359777848554515494536293)
                ·
                  refine ⟨4567458346603971655225555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24359777848554515494536293 4567458346603971655225555)
                  ·
                    refine ⟨6851187519905957482838333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4567458346603971655225555 6851187519905957482838333)
                    ·
                      refine ⟨2569195319964734056064375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6851187519905957482838333 2569195319964734056064375)
                      ·
                        rfl

theorem cell23_5003490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5003490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003490 prefixEnd_5003490 := by exact prefixLift 5003490
  have htrace : WordTrace (prefixWord ++ tailWord_5003490) baseStart_5003490 baseEnd_5003490 := by
    simpa [prefixWord, tailWord_5003490, baseEnd_5003490] using wordTrace_append hprefix tailTrace_5003490
  have hstable : (prefixWord ++ tailWord_5003490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003490).length < 2 ^ (prefixWord ++ tailWord_5003490).sum := by decide
  have hdescent : baseEnd_5003490 < baseStart_5003490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003496 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_5003496 : Nat := 118140960795 + 5003496 * 2 ^ 59
def prefixEnd_5003496 : Nat := 4983230072969 + 3 ^ 40 * 5003496 * 2
def baseEnd_5003496 : Nat := 2569198400848661032589347

theorem tailTrace_5003496 : CollatzResearch.WordTrace tailWord_5003496 prefixEnd_5003496 2569198400848661032589347 := by
  unfold tailWord_5003496
  simp only [CollatzResearch.WordTrace]
  refine ⟨91246245740597997964687171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121661660987463997286249561 91246245740597997964687171)
  ·
    refine ⟨136869368610896996947030757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91246245740597997964687171 136869368610896996947030757)
    ·
      refine ⟨25663006614543186927568267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136869368610896996947030757 25663006614543186927568267)
      ·
        refine ⟨38494509921814780391352401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25663006614543186927568267 38494509921814780391352401)
        ·
          refine ⟨28870882441361085293514301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38494509921814780391352401 28870882441361085293514301)
          ·
            refine ⟨10826580915510406985067863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28870882441361085293514301 10826580915510406985067863)
            ·
              refine ⟨16239871373265610477601795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10826580915510406985067863 16239871373265610477601795)
              ·
                refine ⟨24359807059898415716402693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16239871373265610477601795 24359807059898415716402693)
                ·
                  refine ⟨4567463823730952946825505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24359807059898415716402693 4567463823730952946825505)
                  ·
                    refine ⟨3425597867798214710119129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4567463823730952946825505 3425597867798214710119129)
                    ·
                      refine ⟨2569198400848661032589347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425597867798214710119129 2569198400848661032589347)
                      ·
                        rfl

theorem cell23_5003496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_5003496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003496 prefixEnd_5003496 := by exact prefixLift 5003496
  have htrace : WordTrace (prefixWord ++ tailWord_5003496) baseStart_5003496 baseEnd_5003496 := by
    simpa [prefixWord, tailWord_5003496, baseEnd_5003496] using wordTrace_append hprefix tailTrace_5003496
  have hstable : (prefixWord ++ tailWord_5003496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003496).length < 2 ^ (prefixWord ++ tailWord_5003496).sum := by decide
  have hdescent : baseEnd_5003496 < baseStart_5003496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003525 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_5003525 : Nat := 118140960795 + 5003525 * 2 ^ 59
def prefixEnd_5003525 : Nat := 4983230072969 + 3 ^ 40 * 5003525 * 2
def baseEnd_5003525 : Nat := 2569213291787641419126713

theorem tailTrace_5003525 : CollatzResearch.WordTrace tailWord_5003525 prefixEnd_5003525 2569213291787641419126713 := by
  unfold tailWord_5003525
  simp only [CollatzResearch.WordTrace]
  refine ⟨182493549198090933882180029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121662366132060622588120019 182493549198090933882180029)
  ·
    refine ⟨68435080949284100205817511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182493549198090933882180029 68435080949284100205817511)
    ·
      refine ⟨102652621423926150308726267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68435080949284100205817511 102652621423926150308726267)
      ·
        refine ⟨153978932135889225463089401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102652621423926150308726267 153978932135889225463089401)
        ·
          refine ⟨115484199101916919097317051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153978932135889225463089401 115484199101916919097317051)
          ·
            refine ⟨173226298652875378645975577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115484199101916919097317051 173226298652875378645975577)
            ·
              refine ⟨129919723989656533984481683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173226298652875378645975577 129919723989656533984481683)
              ·
                refine ⟨194879585984484800976722525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129919723989656533984481683 194879585984484800976722525)
                ·
                  refine ⟨73079844744181800366270947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194879585984484800976722525 73079844744181800366270947)
                  ·
                    refine ⟨109619767116272700549406421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73079844744181800366270947 109619767116272700549406421)
                    ·
                      refine ⟨2569213291787641419126713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109619767116272700549406421 2569213291787641419126713)
                      ·
                        rfl

theorem cell23_5003525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_5003525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003525 prefixEnd_5003525 := by exact prefixLift 5003525
  have htrace : WordTrace (prefixWord ++ tailWord_5003525) baseStart_5003525 baseEnd_5003525 := by
    simpa [prefixWord, tailWord_5003525, baseEnd_5003525] using wordTrace_append hprefix tailTrace_5003525
  have hstable : (prefixWord ++ tailWord_5003525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003525).length < 2 ^ (prefixWord ++ tailWord_5003525).sum := by decide
  have hdescent : baseEnd_5003525 < baseStart_5003525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003532 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_5003532 : Nat := 118140960795 + 5003532 * 2 ^ 59
def prefixEnd_5003532 : Nat := 4983230072969 + 3 ^ 40 * 5003532 * 2
def baseEnd_5003532 : Nat := 856405628717407630579727

theorem tailTrace_5003532 : CollatzResearch.WordTrace tailWord_5003532 prefixEnd_5003532 856405628717407630579727 := by
  unfold tailWord_5003532
  simp only [CollatzResearch.WordTrace]
  refine ⟨91246902254532787038842425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121662536339377049385123233 91246902254532787038842425)
  ·
    refine ⟨68435176690899590279131819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91246902254532787038842425 68435176690899590279131819)
    ·
      refine ⟨102652765036349385418697729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68435176690899590279131819 102652765036349385418697729)
      ·
        refine ⟨76989573777262039064023297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102652765036349385418697729 76989573777262039064023297)
        ·
          refine ⟨57742180332946529298017473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76989573777262039064023297 57742180332946529298017473)
          ·
            refine ⟨43306635249709896973513105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57742180332946529298017473 43306635249709896973513105)
            ·
              refine ⟨32479976437282422730134829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43306635249709896973513105 32479976437282422730134829)
              ·
                refine ⟨12179991163980908523800561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32479976437282422730134829 12179991163980908523800561)
                ·
                  refine ⟨9134993372985681392850421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12179991163980908523800561 9134993372985681392850421)
                  ·
                    refine ⟨856405628717407630579727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9134993372985681392850421 856405628717407630579727)
                    ·
                      rfl

theorem cell23_5003532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_5003532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003532 prefixEnd_5003532 := by exact prefixLift 5003532
  have htrace : WordTrace (prefixWord ++ tailWord_5003532) baseStart_5003532 baseEnd_5003532 := by
    simpa [prefixWord, tailWord_5003532, baseEnd_5003532] using wordTrace_append hprefix tailTrace_5003532
  have hstable : (prefixWord ++ tailWord_5003532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003532).length < 2 ^ (prefixWord ++ tailWord_5003532).sum := by decide
  have hdescent : baseEnd_5003532 < baseStart_5003532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003596 : List Nat := [2, 2, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_5003596 : Nat := 118140960795 + 5003596 * 2 ^ 59
def prefixEnd_5003596 : Nat := 4983230072969 + 3 ^ 40 * 5003596 * 2
def baseEnd_5003596 : Nat := 856416582971370213779629

theorem tailTrace_5003596 : CollatzResearch.WordTrace tailWord_5003596 prefixEnd_5003596 856416582971370213779629 := by
  unfold tailWord_5003596
  simp only [CollatzResearch.WordTrace]
  refine ⟨91248069390416856504007321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121664092520555808672009761 91248069390416856504007321)
  ·
    refine ⟨68436052042812642378005491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91248069390416856504007321 68436052042812642378005491)
    ·
      refine ⟨102654078064218963567008237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68436052042812642378005491 102654078064218963567008237)
      ·
        refine ⟨38495279274082111337628089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102654078064218963567008237 38495279274082111337628089)
        ·
          refine ⟨28871459455561583503221067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38495279274082111337628089 28871459455561583503221067)
          ·
            refine ⟨43307189183342375254831601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28871459455561583503221067 43307189183342375254831601)
            ·
              refine ⟨32480391887506781441123701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43307189183342375254831601 32480391887506781441123701)
              ·
                refine ⟨3045036739453760760105347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32480391887506781441123701 3045036739453760760105347)
                ·
                  refine ⟨4567555109180641140158021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045036739453760760105347 4567555109180641140158021)
                  ·
                    refine ⟨856416582971370213779629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4567555109180641140158021 856416582971370213779629)
                    ·
                      rfl

theorem cell23_5003596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_5003596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003596 prefixEnd_5003596 := by exact prefixLift 5003596
  have htrace : WordTrace (prefixWord ++ tailWord_5003596) baseStart_5003596 baseEnd_5003596 := by
    simpa [prefixWord, tailWord_5003596, baseEnd_5003596] using wordTrace_append hprefix tailTrace_5003596
  have hstable : (prefixWord ++ tailWord_5003596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003596).length < 2 ^ (prefixWord ++ tailWord_5003596).sum := by decide
  have hdescent : baseEnd_5003596 < baseStart_5003596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003679 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5003679 : Nat := 118140960795 + 5003679 * 2 ^ 59
def prefixEnd_5003679 : Nat := 4983230072969 + 3 ^ 40 * 5003679 * 2
def baseEnd_5003679 : Nat := 2569292367808433816601005

theorem tailTrace_5003679 : CollatzResearch.WordTrace tailWord_5003679 prefixEnd_5003679 2569292367808433816601005 := by
  unfold tailWord_5003679
  simp only [CollatzResearch.WordTrace]
  refine ⟨182499166039533018183286091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121666110693022012122190727 182499166039533018183286091)
  ·
    refine ⟨273748749059299527274929137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182499166039533018183286091 273748749059299527274929137)
    ·
      refine ⟨205311561794474645456196853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273748749059299527274929137 205311561794474645456196853)
      ·
        refine ⟨19247958918231998011518455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205311561794474645456196853 19247958918231998011518455)
        ·
          refine ⟨28871938377347997017277683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19247958918231998011518455 28871938377347997017277683)
          ·
            refine ⟨43307907566021995525916525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28871938377347997017277683 43307907566021995525916525)
            ·
              refine ⟨16240465337258248322218697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43307907566021995525916525 16240465337258248322218697)
              ·
                refine ⟨12180349002943686241664023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16240465337258248322218697 12180349002943686241664023)
                ·
                  refine ⟨18270523504415529362496035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12180349002943686241664023 18270523504415529362496035)
                  ·
                    refine ⟨27405785256623294043744053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18270523504415529362496035 27405785256623294043744053)
                    ·
                      refine ⟨2569292367808433816601005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27405785256623294043744053 2569292367808433816601005)
                      ·
                        rfl

theorem cell23_5003679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5003679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003679 prefixEnd_5003679 := by exact prefixLift 5003679
  have htrace : WordTrace (prefixWord ++ tailWord_5003679) baseStart_5003679 baseEnd_5003679 := by
    simpa [prefixWord, tailWord_5003679, baseEnd_5003679] using wordTrace_append hprefix tailTrace_5003679
  have hstable : (prefixWord ++ tailWord_5003679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003679).length < 2 ^ (prefixWord ++ tailWord_5003679).sum := by decide
  have hdescent : baseEnd_5003679 < baseStart_5003679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003712 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 1, 9]
def baseStart_5003712 : Nat := 118140960795 + 5003712 * 2 ^ 59
def prefixEnd_5003712 : Nat := 4983230072969 + 3 ^ 40 * 5003712 * 2
def baseEnd_5003712 : Nat := 856436437556677395829451

theorem tailTrace_5003712 : CollatzResearch.WordTrace tailWord_5003712 prefixEnd_5003712 856436437556677395829451 := by
  unfold tailWord_5003712
  simp only [CollatzResearch.WordTrace]
  refine ⟨91250184824206732409618695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121666913098942309879491593 91250184824206732409618695)
  ·
    refine ⟨136875277236310098614428043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91250184824206732409618695 136875277236310098614428043)
    ·
      refine ⟨205312915854465147921642065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136875277236310098614428043 205312915854465147921642065)
      ·
        refine ⟨153984686890848860941231549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205312915854465147921642065 153984686890848860941231549)
        ·
          refine ⟨57744257584068322852961831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153984686890848860941231549 57744257584068322852961831)
          ·
            refine ⟨86616386376102484279442747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57744257584068322852961831 86616386376102484279442747)
            ·
              refine ⟨129924579564153726419164121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86616386376102484279442747 129924579564153726419164121)
              ·
                refine ⟨97443434673115294814373091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129924579564153726419164121 97443434673115294814373091)
                ·
                  refine ⟨146165152009672942221559637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97443434673115294814373091 146165152009672942221559637)
                  ·
                    refine ⟨856436437556677395829451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 146165152009672942221559637 856436437556677395829451)
                    ·
                      rfl

theorem cell23_5003712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_5003712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003712 prefixEnd_5003712 := by exact prefixLift 5003712
  have htrace : WordTrace (prefixWord ++ tailWord_5003712) baseStart_5003712 baseEnd_5003712 := by
    simpa [prefixWord, tailWord_5003712, baseEnd_5003712] using wordTrace_append hprefix tailTrace_5003712
  have hstable : (prefixWord ++ tailWord_5003712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003712).length < 2 ^ (prefixWord ++ tailWord_5003712).sum := by decide
  have hdescent : baseEnd_5003712 < baseStart_5003712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003716 : List Nat := [2, 3, 3, 2, 2, 2, 9]
def baseStart_5003716 : Nat := 118140960795 + 5003716 * 2 ^ 59
def prefixEnd_5003716 : Nat := 4983230072969 + 3 ^ 40 * 5003716 * 2
def baseEnd_5003716 : Nat := 31719893414724076195535

theorem tailTrace_5003716 : CollatzResearch.WordTrace tailWord_5003716 prefixEnd_5003716 31719893414724076195535 := by
  unfold tailWord_5003716
  simp only [CollatzResearch.WordTrace]
  refine ⟨91250257770199486751191501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121667010360265982334922001 91250257770199486751191501)
  ·
    refine ⟨34218846663824807531696813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91250257770199486751191501 34218846663824807531696813)
    ·
      refine ⟨12832067498934302824386305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34218846663824807531696813 12832067498934302824386305)
      ·
        refine ⟨9624050624200727118289729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12832067498934302824386305 9624050624200727118289729)
        ·
          refine ⟨7218037968150545338717297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9624050624200727118289729 7218037968150545338717297)
          ·
            refine ⟨5413528476112909004037973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7218037968150545338717297 5413528476112909004037973)
            ·
              refine ⟨31719893414724076195535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5413528476112909004037973 31719893414724076195535)
              ·
                rfl

theorem cell23_5003716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 9].length) (baseStart_5003716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003716 prefixEnd_5003716 := by exact prefixLift 5003716
  have htrace : WordTrace (prefixWord ++ tailWord_5003716) baseStart_5003716 baseEnd_5003716 := by
    simpa [prefixWord, tailWord_5003716, baseEnd_5003716] using wordTrace_append hprefix tailTrace_5003716
  have hstable : (prefixWord ++ tailWord_5003716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003716).length < 2 ^ (prefixWord ++ tailWord_5003716).sum := by decide
  have hdescent : baseEnd_5003716 < baseStart_5003716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003736 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 3, 3, 2]
def baseStart_5003736 : Nat := 118140960795 + 5003736 * 2 ^ 59
def prefixEnd_5003736 : Nat := 4983230072969 + 3 ^ 40 * 5003736 * 2
def baseEnd_5003736 : Nat := 2569321636205740093588243

theorem tailTrace_5003736 : CollatzResearch.WordTrace tailWord_5003736 prefixEnd_5003736 2569321636205740093588243 := by
  unfold tailWord_5003736
  simp only [CollatzResearch.WordTrace]
  refine ⟨91250622500163258459055531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121667496666884344612074041 91250622500163258459055531)
  ·
    refine ⟨136875933750244887688583297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91250622500163258459055531 136875933750244887688583297)
    ·
      refine ⟨102656950312683665766437473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136875933750244887688583297 102656950312683665766437473)
      ·
        refine ⟨76992712734512749324828105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102656950312683665766437473 76992712734512749324828105)
        ·
          refine ⟨57744534550884561993621079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76992712734512749324828105 57744534550884561993621079)
          ·
            refine ⟨86616801826326842990431619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57744534550884561993621079 86616801826326842990431619)
            ·
              refine ⟨129925202739490264485647429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86616801826326842990431619 129925202739490264485647429)
              ·
                refine ⟨24360975513654424591058893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129925202739490264485647429 24360975513654424591058893)
                ·
                  refine ⟨9135365817620409221647085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24360975513654424591058893 9135365817620409221647085)
                  ·
                    refine ⟨3425762181607653458117657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9135365817620409221647085 3425762181607653458117657)
                    ·
                      refine ⟨2569321636205740093588243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425762181607653458117657 2569321636205740093588243)
                      ·
                        rfl

theorem cell23_5003736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_5003736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003736 prefixEnd_5003736 := by exact prefixLift 5003736
  have htrace : WordTrace (prefixWord ++ tailWord_5003736) baseStart_5003736 baseEnd_5003736 := by
    simpa [prefixWord, tailWord_5003736, baseEnd_5003736] using wordTrace_append hprefix tailTrace_5003736
  have hstable : (prefixWord ++ tailWord_5003736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003736).length < 2 ^ (prefixWord ++ tailWord_5003736).sum := by decide
  have hdescent : baseEnd_5003736 < baseStart_5003736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003743 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 3]
def baseStart_5003743 : Nat := 118140960795 + 5003743 * 2 ^ 59
def prefixEnd_5003743 : Nat := 4983230072969 + 3 ^ 40 * 5003743 * 2
def baseEnd_5003743 : Nat := 2569325230570321566200711

theorem tailTrace_5003743 : CollatzResearch.WordTrace tailWord_5003743 prefixEnd_5003743 2569325230570321566200711 := by
  unfold tailWord_5003743
  simp only [CollatzResearch.WordTrace]
  refine ⟨182501500311301157113615883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121667666874200771409077255 182501500311301157113615883)
  ·
    refine ⟨273752250466951735670423825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182501500311301157113615883 273752250466951735670423825)
    ·
      refine ⟨205314187850213801752817869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273752250466951735670423825 205314187850213801752817869)
      ·
        refine ⟨76992820443830175657306701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205314187850213801752817869 76992820443830175657306701)
        ·
          refine ⟨28872307666436315871490013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76992820443830175657306701 28872307666436315871490013)
          ·
            refine ⟨10827115374913618451808755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28872307666436315871490013 10827115374913618451808755)
            ·
              refine ⟨16240673062370427677713133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10827115374913618451808755 16240673062370427677713133)
              ·
                refine ⟨6090252398388910379142425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16240673062370427677713133 6090252398388910379142425)
                ·
                  refine ⟨4567689298791682784356819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6090252398388910379142425 4567689298791682784356819)
                  ·
                    refine ⟨6851533948187524176535229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4567689298791682784356819 6851533948187524176535229)
                    ·
                      refine ⟨2569325230570321566200711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6851533948187524176535229 2569325230570321566200711)
                      ·
                        rfl

theorem cell23_5003743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_5003743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003743 prefixEnd_5003743 := by exact prefixLift 5003743
  have htrace : WordTrace (prefixWord ++ tailWord_5003743) baseStart_5003743 baseEnd_5003743 := by
    simpa [prefixWord, tailWord_5003743, baseEnd_5003743] using wordTrace_append hprefix tailTrace_5003743
  have hstable : (prefixWord ++ tailWord_5003743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003743).length < 2 ^ (prefixWord ++ tailWord_5003743).sum := by decide
  have hdescent : baseEnd_5003743 < baseStart_5003743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003769 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_5003769 : Nat := 118140960795 + 5003769 * 2 ^ 59
def prefixEnd_5003769 : Nat := 4983230072969 + 3 ^ 40 * 5003769 * 2
def baseEnd_5003769 : Nat := 2569338581067338464475591

theorem tailTrace_5003769 : CollatzResearch.WordTrace tailWord_5003769 prefixEnd_5003769 2569338581067338464475591 := by
  unfold tailWord_5003769
  simp only [CollatzResearch.WordTrace]
  refine ⟨182502448609206963554062361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121668299072804642369374907 182502448609206963554062361)
  ·
    refine ⟨136876836456905222665546771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182502448609206963554062361 136876836456905222665546771)
    ·
      refine ⟨205315254685357833998320157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136876836456905222665546771 205315254685357833998320157)
      ·
        refine ⟨76993220507009187749370059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205315254685357833998320157 76993220507009187749370059)
        ·
          refine ⟨115489830760513781624055089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76993220507009187749370059 115489830760513781624055089)
          ·
            refine ⟨86617373070385336218041317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115489830760513781624055089 86617373070385336218041317)
            ·
              refine ⟨16240757450697250540882747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86617373070385336218041317 16240757450697250540882747)
              ·
                refine ⟨24361136176045875811324121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16240757450697250540882747 24361136176045875811324121)
                ·
                  refine ⟨18270852132034406858493091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24361136176045875811324121 18270852132034406858493091)
                  ·
                    refine ⟨27406278198051610287739637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18270852132034406858493091 27406278198051610287739637)
                    ·
                      refine ⟨2569338581067338464475591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27406278198051610287739637 2569338581067338464475591)
                      ·
                        rfl

theorem cell23_5003769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_5003769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003769 prefixEnd_5003769 := by exact prefixLift 5003769
  have htrace : WordTrace (prefixWord ++ tailWord_5003769) baseStart_5003769 baseEnd_5003769 := by
    simpa [prefixWord, tailWord_5003769, baseEnd_5003769] using wordTrace_append hprefix tailTrace_5003769
  have hstable : (prefixWord ++ tailWord_5003769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003769).length < 2 ^ (prefixWord ++ tailWord_5003769).sum := by decide
  have hdescent : baseEnd_5003769 < baseStart_5003769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003778 : List Nat := [3, 4, 1, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5003778 : Nat := 118140960795 + 5003778 * 2 ^ 59
def prefixEnd_5003778 : Nat := 4983230072969 + 3 ^ 40 * 5003778 * 2
def baseEnd_5003778 : Nat := 2569343202393228929263051

theorem tailTrace_5003778 : CollatzResearch.WordTrace tailWord_5003778 prefixEnd_5003778 2569343202393228929263051 := by
  unfold tailWord_5003778
  simp only [CollatzResearch.WordTrace]
  refine ⟨45625694216543589522784997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121668517910782905394093325 45625694216543589522784997)
  ·
    refine ⟨8554817665601923035522187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45625694216543589522784997 8554817665601923035522187)
    ·
      refine ⟨12832226498402884553283281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8554817665601923035522187 12832226498402884553283281)
      ·
        refine ⟨9624169873802163414962461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12832226498402884553283281 9624169873802163414962461)
        ·
          refine ⟨3609063702675811280610923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9624169873802163414962461 3609063702675811280610923)
          ·
            refine ⟨5413595554013716920916385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609063702675811280610923 5413595554013716920916385)
            ·
              refine ⟨4060196665510287690687289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5413595554013716920916385 4060196665510287690687289)
              ·
                refine ⟨3045147499132715768015467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4060196665510287690687289 3045147499132715768015467)
                ·
                  refine ⟨4567721248699073652023201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045147499132715768015467 4567721248699073652023201)
                  ·
                    refine ⟨3425790936524305239017401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4567721248699073652023201 3425790936524305239017401)
                    ·
                      refine ⟨2569343202393228929263051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425790936524305239017401 2569343202393228929263051)
                      ·
                        rfl

theorem cell23_5003778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5003778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003778 prefixEnd_5003778 := by exact prefixLift 5003778
  have htrace : WordTrace (prefixWord ++ tailWord_5003778) baseStart_5003778 baseEnd_5003778 := by
    simpa [prefixWord, tailWord_5003778, baseEnd_5003778] using wordTrace_append hprefix tailTrace_5003778
  have hstable : (prefixWord ++ tailWord_5003778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003778).length < 2 ^ (prefixWord ++ tailWord_5003778).sum := by decide
  have hdescent : baseEnd_5003778 < baseStart_5003778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003779 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 4]
def baseStart_5003779 : Nat := 118140960795 + 5003779 * 2 ^ 59
def prefixEnd_5003779 : Nat := 4983230072969 + 3 ^ 40 * 5003779 * 2
def baseEnd_5003779 : Nat := 2569343715873883425350545

theorem tailTrace_5003779 : CollatzResearch.WordTrace tailWord_5003779 prefixEnd_5003779 2569343715873883425350545 := by
  unfold tailWord_5003779
  simp only [CollatzResearch.WordTrace]
  refine ⟨182502813339170735261926391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121668542226113823507950927 182502813339170735261926391)
  ·
    refine ⟨273754220008756102892889587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182502813339170735261926391 273754220008756102892889587)
    ·
      refine ⟨410631330013134154339334381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273754220008756102892889587 410631330013134154339334381)
      ·
        refine ⟨153986748754925307877250393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410631330013134154339334381 153986748754925307877250393)
        ·
          refine ⟨115490061566193980907937795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153986748754925307877250393 115490061566193980907937795)
          ·
            refine ⟨173235092349290971361906693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115490061566193980907937795 173235092349290971361906693)
            ·
              refine ⟨32481579815492057130357505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173235092349290971361906693 32481579815492057130357505)
              ·
                refine ⟨24361184861619042847768129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32481579815492057130357505 24361184861619042847768129)
                ·
                  refine ⟨18270888646214282135826097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24361184861619042847768129 18270888646214282135826097)
                  ·
                    refine ⟨13703166484660711601869573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18270888646214282135826097 13703166484660711601869573)
                    ·
                      refine ⟨2569343715873883425350545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13703166484660711601869573 2569343715873883425350545)
                      ·
                        rfl

theorem cell23_5003779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_5003779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003779 prefixEnd_5003779 := by exact prefixLift 5003779
  have htrace : WordTrace (prefixWord ++ tailWord_5003779) baseStart_5003779 baseEnd_5003779 := by
    simpa [prefixWord, tailWord_5003779, baseEnd_5003779] using wordTrace_append hprefix tailTrace_5003779
  have hstable : (prefixWord ++ tailWord_5003779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003779).length < 2 ^ (prefixWord ++ tailWord_5003779).sum := by decide
  have hdescent : baseEnd_5003779 < baseStart_5003779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003800 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 2, 2, 2]
def baseStart_5003800 : Nat := 118140960795 + 5003800 * 2 ^ 59
def prefixEnd_5003800 : Nat := 4983230072969 + 3 ^ 40 * 5003800 * 2
def baseEnd_5003800 : Nat := 2569354498967627843187949

theorem tailTrace_5003800 : CollatzResearch.WordTrace tailWord_5003800 prefixEnd_5003800 2569354498967627843187949 := by
  unfold tailWord_5003800
  simp only [CollatzResearch.WordTrace]
  refine ⟨91251789636047327924220427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121669052848063103898960569 91251789636047327924220427)
  ·
    refine ⟨136877684454070991886330641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91251789636047327924220427 136877684454070991886330641)
    ·
      refine ⟨102658263340553243914747981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136877684454070991886330641 102658263340553243914747981)
      ·
        refine ⟨38496848752707466468030493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102658263340553243914747981 38496848752707466468030493)
        ·
          refine ⟨14436318282265299925511435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38496848752707466468030493 14436318282265299925511435)
          ·
            refine ⟨21654477423397949888267153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14436318282265299925511435 21654477423397949888267153)
            ·
              refine ⟨16240858067548462416200365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21654477423397949888267153 16240858067548462416200365)
              ·
                refine ⟨6090321775330673406075137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16240858067548462416200365 6090321775330673406075137)
                ·
                  refine ⟨4567741331498005054556353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6090321775330673406075137 4567741331498005054556353)
                  ·
                    refine ⟨3425805998623503790917265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4567741331498005054556353 3425805998623503790917265)
                    ·
                      refine ⟨2569354498967627843187949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425805998623503790917265 2569354498967627843187949)
                      ·
                        rfl

theorem cell23_5003800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_5003800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003800 prefixEnd_5003800 := by exact prefixLift 5003800
  have htrace : WordTrace (prefixWord ++ tailWord_5003800) baseStart_5003800 baseEnd_5003800 := by
    simpa [prefixWord, tailWord_5003800, baseEnd_5003800] using wordTrace_append hprefix tailTrace_5003800
  have hstable : (prefixWord ++ tailWord_5003800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003800).length < 2 ^ (prefixWord ++ tailWord_5003800).sum := by decide
  have hdescent : baseEnd_5003800 < baseStart_5003800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003856 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 1, 6, 2]
def baseStart_5003856 : Nat := 118140960795 + 5003856 * 2 ^ 59
def prefixEnd_5003856 : Nat := 4983230072969 + 3 ^ 40 * 5003856 * 2
def baseEnd_5003856 : Nat := 2569383253884279624087691

theorem tailTrace_5003856 : CollatzResearch.WordTrace tailWord_5003856 prefixEnd_5003856 2569383253884279624087691 := by
  unfold tailWord_5003856
  simp only [CollatzResearch.WordTrace]
  refine ⟨91252810879945888706239711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121670414506594518274986281 91252810879945888706239711)
  ·
    refine ⟨136879216319918833059359567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91252810879945888706239711 136879216319918833059359567)
    ·
      refine ⟨205318824479878249589039351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136879216319918833059359567 205318824479878249589039351)
      ·
        refine ⟨307978236719817374383559027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205318824479878249589039351 307978236719817374383559027)
        ·
          refine ⟨461967355079726061575338541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307978236719817374383559027 461967355079726061575338541)
          ·
            refine ⟨173237758154897273090751953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461967355079726061575338541 173237758154897273090751953)
            ·
              refine ⟨129928318616172954818063965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173237758154897273090751953 129928318616172954818063965)
              ·
                refine ⟨48723119481064858056773987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129928318616172954818063965 48723119481064858056773987)
                ·
                  refine ⟨73084679221597287085160981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48723119481064858056773987 73084679221597287085160981)
                  ·
                    refine ⟨3425844338512372832116921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73084679221597287085160981 3425844338512372832116921)
                    ·
                      refine ⟨2569383253884279624087691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425844338512372832116921 2569383253884279624087691)
                      ·
                        rfl

theorem cell23_5003856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 6, 2].length) (baseStart_5003856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003856 prefixEnd_5003856 := by exact prefixLift 5003856
  have htrace : WordTrace (prefixWord ++ tailWord_5003856) baseStart_5003856 baseEnd_5003856 := by
    simpa [prefixWord, tailWord_5003856, baseEnd_5003856] using wordTrace_append hprefix tailTrace_5003856
  have hstable : (prefixWord ++ tailWord_5003856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003856).length < 2 ^ (prefixWord ++ tailWord_5003856).sum := by decide
  have hdescent : baseEnd_5003856 < baseStart_5003856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003874 : List Nat := [3, 3, 2, 3, 2, 1, 1, 3, 5]
def baseStart_5003874 : Nat := 118140960795 + 5003874 * 2 ^ 59
def prefixEnd_5003874 : Nat := 4983230072969 + 3 ^ 40 * 5003874 * 2
def baseEnd_5003874 : Nat := 285488055170673394851401

theorem tailTrace_5003874 : CollatzResearch.WordTrace tailWord_5003874 prefixEnd_5003874 285488055170673394851401 := by
  unfold tailWord_5003874
  simp only [CollatzResearch.WordTrace]
  refine ⟨45626569568456641621658669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121670852182551044324423117 45626569568456641621658669)
  ·
    refine ⟨17109963588171240608122001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45626569568456641621658669 17109963588171240608122001)
    ·
      refine ⟨12832472691128430456091501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17109963588171240608122001 12832472691128430456091501)
      ·
        refine ⟨4812177259173161421034313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12832472691128430456091501 4812177259173161421034313)
        ·
          refine ⟨3609132944379871065775735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4812177259173161421034313 3609132944379871065775735)
          ·
            refine ⟨5413699416569806598663603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609132944379871065775735 5413699416569806598663603)
            ·
              refine ⟨8120549124854709897995405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5413699416569806598663603 8120549124854709897995405)
              ·
                refine ⟨3045205921820516211748277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8120549124854709897995405 3045205921820516211748277)
                ·
                  refine ⟨285488055170673394851401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3045205921820516211748277 285488055170673394851401)
                  ·
                    rfl

theorem cell23_5003874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_5003874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003874 prefixEnd_5003874 := by exact prefixLift 5003874
  have htrace : WordTrace (prefixWord ++ tailWord_5003874) baseStart_5003874 baseEnd_5003874 := by
    simpa [prefixWord, tailWord_5003874, baseEnd_5003874] using wordTrace_append hprefix tailTrace_5003874
  have hstable : (prefixWord ++ tailWord_5003874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003874).length < 2 ^ (prefixWord ++ tailWord_5003874).sum := by decide
  have hdescent : baseEnd_5003874 < baseStart_5003874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003876 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_5003876 : Nat := 118140960795 + 5003876 * 2 ^ 59
def prefixEnd_5003876 : Nat := 4983230072969 + 3 ^ 40 * 5003876 * 2
def baseEnd_5003876 : Nat := 2569393523497369545837599

theorem tailTrace_5003876 : CollatzResearch.WordTrace tailWord_5003876 prefixEnd_5003876 2569393523497369545837599 := by
  unfold tailWord_5003876
  simp only [CollatzResearch.WordTrace]
  refine ⟨91253175609909660414103741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121670900813212880552138321 91253175609909660414103741)
  ·
    refine ⟨34219940853716122655288903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91253175609909660414103741 34219940853716122655288903)
    ·
      refine ⟨51329911280574183982933355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34219940853716122655288903 51329911280574183982933355)
      ·
        refine ⟨76994866920861275974400033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51329911280574183982933355 76994866920861275974400033)
        ·
          refine ⟨57746150190645956980800025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76994866920861275974400033 57746150190645956980800025)
          ·
            refine ⟨43309612642984467735600019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57746150190645956980800025 43309612642984467735600019)
            ·
              refine ⟨64964418964476701603400029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43309612642984467735600019 64964418964476701603400029)
              ·
                refine ⟨24361657111678763101275011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64964418964476701603400029 24361657111678763101275011)
                ·
                  refine ⟨36542485667518144651912517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24361657111678763101275011 36542485667518144651912517)
                  ·
                    refine ⟨6851716062659652122233597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36542485667518144651912517 6851716062659652122233597)
                    ·
                      refine ⟨2569393523497369545837599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6851716062659652122233597 2569393523497369545837599)
                      ·
                        rfl

theorem cell23_5003876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_5003876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003876 prefixEnd_5003876 := by exact prefixLift 5003876
  have htrace : WordTrace (prefixWord ++ tailWord_5003876) baseStart_5003876 baseEnd_5003876 := by
    simpa [prefixWord, tailWord_5003876, baseEnd_5003876] using wordTrace_append hprefix tailTrace_5003876
  have hstable : (prefixWord ++ tailWord_5003876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003876).length < 2 ^ (prefixWord ++ tailWord_5003876).sum := by decide
  have hdescent : baseEnd_5003876 < baseStart_5003876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003883 : List Nat := [1, 1, 1, 1, 2, 2, 1, 9, 1, 4]
def baseStart_5003883 : Nat := 118140960795 + 5003883 * 2 ^ 59
def prefixEnd_5003883 : Nat := 4983230072969 + 3 ^ 40 * 5003883 * 2
def baseEnd_5003883 : Nat := 856465705953983672816689

theorem tailTrace_5003883 : CollatzResearch.WordTrace tailWord_5003883 prefixEnd_5003883 856465705953983672816689 := by
  unfold tailWord_5003883
  simp only [CollatzResearch.WordTrace]
  refine ⟨182506606530793961023712303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121671071020529307349141535 182506606530793961023712303)
  ·
    refine ⟨273759909796190941535568455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182506606530793961023712303 273759909796190941535568455)
    ·
      refine ⟨410639864694286412303352683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273759909796190941535568455 410639864694286412303352683)
      ·
        refine ⟨615959797041429618455029025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410639864694286412303352683 615959797041429618455029025)
        ·
          refine ⟨461969847781072213841271769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615959797041429618455029025 461969847781072213841271769)
          ·
            refine ⟨346477385835804160380953827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461969847781072213841271769 346477385835804160380953827)
            ·
              refine ⟨519716078753706240571430741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346477385835804160380953827 519716078753706240571430741)
              ·
                refine ⟨3045211398947497503348227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 519716078753706240571430741 3045211398947497503348227)
                ·
                  refine ⟨4567817098421246255022341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045211398947497503348227 4567817098421246255022341)
                  ·
                    refine ⟨856465705953983672816689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4567817098421246255022341 856465705953983672816689)
                    ·
                      rfl

theorem cell23_5003883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 4].length) (baseStart_5003883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003883 prefixEnd_5003883 := by exact prefixLift 5003883
  have htrace : WordTrace (prefixWord ++ tailWord_5003883) baseStart_5003883 baseEnd_5003883 := by
    simpa [prefixWord, tailWord_5003883, baseEnd_5003883] using wordTrace_append hprefix tailTrace_5003883
  have hstable : (prefixWord ++ tailWord_5003883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003883).length < 2 ^ (prefixWord ++ tailWord_5003883).sum := by decide
  have hdescent : baseEnd_5003883 < baseStart_5003883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003899 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 6]
def baseStart_5003899 : Nat := 118140960795 + 5003899 * 2 ^ 59
def prefixEnd_5003899 : Nat := 4983230072969 + 3 ^ 40 * 5003899 * 2
def baseEnd_5003899 : Nat := 2569405333552422955849993

theorem tailTrace_5003899 : CollatzResearch.WordTrace tailWord_5003899 prefixEnd_5003899 2569405333552422955849993 := by
  unfold tailWord_5003899
  simp only [CollatzResearch.WordTrace]
  refine ⟨182507190098735995756294751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121671460065823997170863167 182507190098735995756294751)
  ·
    refine ⟨273760785148103993634442127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182507190098735995756294751 273760785148103993634442127)
    ·
      refine ⟨410641177722155990451663191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273760785148103993634442127 410641177722155990451663191)
      ·
        refine ⟨615961766583233985677494787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410641177722155990451663191 615961766583233985677494787)
        ·
          refine ⟨923942649874850978516242181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615961766583233985677494787 923942649874850978516242181)
          ·
            refine ⟨173239246851534558471795409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 923942649874850978516242181 173239246851534558471795409)
            ·
              refine ⟨129929435138650918853846557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173239246851534558471795409 129929435138650918853846557)
              ·
                refine ⟨48723538176994094570192459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129929435138650918853846557 48723538176994094570192459)
                ·
                  refine ⟨73085307265491141855288689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48723538176994094570192459 73085307265491141855288689)
                  ·
                    refine ⟨54813980449118356391466517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73085307265491141855288689 54813980449118356391466517)
                    ·
                      refine ⟨2569405333552422955849993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54813980449118356391466517 2569405333552422955849993)
                      ·
                        rfl

theorem cell23_5003899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_5003899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003899 prefixEnd_5003899 := by exact prefixLift 5003899
  have htrace : WordTrace (prefixWord ++ tailWord_5003899) baseStart_5003899 baseEnd_5003899 := by
    simpa [prefixWord, tailWord_5003899, baseEnd_5003899] using wordTrace_append hprefix tailTrace_5003899
  have hstable : (prefixWord ++ tailWord_5003899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003899).length < 2 ^ (prefixWord ++ tailWord_5003899).sum := by decide
  have hdescent : baseEnd_5003899 < baseStart_5003899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003919 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_5003919 : Nat := 118140960795 + 5003919 * 2 ^ 59
def prefixEnd_5003919 : Nat := 4983230072969 + 3 ^ 40 * 5003919 * 2
def baseEnd_5003919 : Nat := 2569415603165512877599901

theorem tailTrace_5003919 : CollatzResearch.WordTrace tailWord_5003919 prefixEnd_5003919 2569415603165512877599901 := by
  unfold tailWord_5003919
  simp only [CollatzResearch.WordTrace]
  refine ⟨182507919558663539172022811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121671946372442359448015207 182507919558663539172022811)
  ·
    refine ⟨273761879337995308758034217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182507919558663539172022811 273761879337995308758034217)
    ·
      refine ⟨205321409503496481568525663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273761879337995308758034217 205321409503496481568525663)
      ·
        refine ⟨307982114255244722352788495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205321409503496481568525663 307982114255244722352788495)
        ·
          refine ⟨461973171382867083529182743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307982114255244722352788495 461973171382867083529182743)
          ·
            refine ⟨692959757074300625293774115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461973171382867083529182743 692959757074300625293774115)
            ·
              refine ⟨1039439635611450937940661173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692959757074300625293774115 1039439635611450937940661173)
              ·
                refine ⟨97447465838573525431936985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1039439635611450937940661173 97447465838573525431936985)
                ·
                  refine ⟨73085599378930144073952739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97447465838573525431936985 73085599378930144073952739)
                  ·
                    refine ⟨109628399068395216110929109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73085599378930144073952739 109628399068395216110929109)
                    ·
                      refine ⟨2569415603165512877599901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109628399068395216110929109 2569415603165512877599901)
                      ·
                        rfl

theorem cell23_5003919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_5003919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003919 prefixEnd_5003919 := by exact prefixLift 5003919
  have htrace : WordTrace (prefixWord ++ tailWord_5003919) baseStart_5003919 baseEnd_5003919 := by
    simpa [prefixWord, tailWord_5003919, baseEnd_5003919] using wordTrace_append hprefix tailTrace_5003919
  have hstable : (prefixWord ++ tailWord_5003919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003919).length < 2 ^ (prefixWord ++ tailWord_5003919).sum := by decide
  have hdescent : baseEnd_5003919 < baseStart_5003919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5003933 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_5003933 : Nat := 118140960795 + 5003933 * 2 ^ 59
def prefixEnd_5003933 : Nat := 4983230072969 + 3 ^ 40 * 5003933 * 2
def baseEnd_5003933 : Nat := 2569422791894675822824837

theorem tailTrace_5003933 : CollatzResearch.WordTrace tailWord_5003933 prefixEnd_5003933 2569422791894675822824837 := by
  unfold tailWord_5003933
  simp only [CollatzResearch.WordTrace]
  refine ⟨182508430180612819563032453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121672286787075213042021635 182508430180612819563032453)
  ·
    refine ⟨34220330658864903668068585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182508430180612819563032453 34220330658864903668068585)
    ·
      refine ⟨25665247994148677751051439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34220330658864903668068585 25665247994148677751051439)
      ·
        refine ⟨38497871991223016626577159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25665247994148677751051439 38497871991223016626577159)
        ·
          refine ⟨57746807986834524939865739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38497871991223016626577159 57746807986834524939865739)
          ·
            refine ⟨86620211980251787409798609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57746807986834524939865739 86620211980251787409798609)
            ·
              refine ⟨64965158985188840557348957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86620211980251787409798609 64965158985188840557348957)
              ·
                refine ⟨24361934619445815209005859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64965158985188840557348957 24361934619445815209005859)
                ·
                  refine ⟨36542901929168722813508789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24361934619445815209005859 36542901929168722813508789)
                  ·
                    refine ⟨3425897055859567763766449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36542901929168722813508789 3425897055859567763766449)
                    ·
                      refine ⟨2569422791894675822824837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425897055859567763766449 2569422791894675822824837)
                      ·
                        rfl

theorem cell23_5003933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_5003933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5003933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5003933 prefixEnd_5003933 := by exact prefixLift 5003933
  have htrace : WordTrace (prefixWord ++ tailWord_5003933) baseStart_5003933 baseEnd_5003933 := by
    simpa [prefixWord, tailWord_5003933, baseEnd_5003933] using wordTrace_append hprefix tailTrace_5003933
  have hstable : (prefixWord ++ tailWord_5003933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5003933).length < 2 ^ (prefixWord ++ tailWord_5003933).sum := by decide
  have hdescent : baseEnd_5003933 < baseStart_5003933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5003933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004014 : List Nat := [4, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_5004014 : Nat := 118140960795 + 5004014 * 2 ^ 59
def prefixEnd_5004014 : Nat := 4983230072969 + 3 ^ 40 * 5004014 * 2
def baseEnd_5004014 : Nat := 2569464383827690005911965

theorem tailTrace_5004014 : CollatzResearch.WordTrace tailWord_5004014 prefixEnd_5004014 2569464383827690005911965 := by
  unfold tailWord_5004014
  simp only [CollatzResearch.WordTrace]
  refine ⟨22813923061664921299591387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121674256328879580264487397 22813923061664921299591387)
  ·
    refine ⟨34220884592497381949387081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22813923061664921299591387 34220884592497381949387081)
    ·
      refine ⟨25665663444373036462040311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34220884592497381949387081 25665663444373036462040311)
      ·
        refine ⟨38498495166559554693060467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25665663444373036462040311 38498495166559554693060467)
        ·
          refine ⟨57747742749839332039590701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38498495166559554693060467 57747742749839332039590701)
          ·
            refine ⟨21655403531189749514846513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57747742749839332039590701 21655403531189749514846513)
            ·
              refine ⟨16241552648392312136134885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21655403531189749514846513 16241552648392312136134885)
              ·
                refine ⟨3045291121573558525525291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16241552648392312136134885 3045291121573558525525291)
                ·
                  refine ⟨4567936682360337788287937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045291121573558525525291 4567936682360337788287937)
                  ·
                    refine ⟨3425952511770253341215953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4567936682360337788287937 3425952511770253341215953)
                    ·
                      refine ⟨2569464383827690005911965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3425952511770253341215953 2569464383827690005911965)
                      ·
                        rfl

theorem cell23_5004014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_5004014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004014 prefixEnd_5004014 := by exact prefixLift 5004014
  have htrace : WordTrace (prefixWord ++ tailWord_5004014) baseStart_5004014 baseEnd_5004014 := by
    simpa [prefixWord, tailWord_5004014, baseEnd_5004014] using wordTrace_append hprefix tailTrace_5004014
  have hstable : (prefixWord ++ tailWord_5004014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004014).length < 2 ^ (prefixWord ++ tailWord_5004014).sum := by decide
  have hdescent : baseEnd_5004014 < baseStart_5004014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004087 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 2, 2, 2]
def baseStart_5004087 : Nat := 118140960795 + 5004087 * 2 ^ 59
def prefixEnd_5004087 : Nat := 4983230072969 + 3 ^ 40 * 5004087 * 2
def baseEnd_5004087 : Nat := 2569501867915468220299129

theorem tailTrace_5004087 : CollatzResearch.WordTrace tailWord_5004087 prefixEnd_5004087 2569501867915468220299129 := by
  unfold tailWord_5004087
  simp only [CollatzResearch.WordTrace]
  refine ⟨182514047022054903864138515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121676031348036602576092343 182514047022054903864138515)
  ·
    refine ⟨273771070533082355796207773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182514047022054903864138515 273771070533082355796207773)
    ·
      refine ⟨102664151449905883423577915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273771070533082355796207773 102664151449905883423577915)
      ·
        refine ⟨153996227174858825135366873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102664151449905883423577915 153996227174858825135366873)
        ·
          refine ⟨115497170381144118851525155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153996227174858825135366873 115497170381144118851525155)
          ·
            refine ⟨173245755571716178277287733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115497170381144118851525155 173245755571716178277287733)
            ·
              refine ⟨16241789584848391713495725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173245755571716178277287733 16241789584848391713495725)
              ·
                refine ⟨6090671094318146892560897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16241789584848391713495725 6090671094318146892560897)
                ·
                  refine ⟨4568003320738610169420673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6090671094318146892560897 4568003320738610169420673)
                  ·
                    refine ⟨3426002490553957627065505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4568003320738610169420673 3426002490553957627065505)
                    ·
                      refine ⟨2569501867915468220299129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426002490553957627065505 2569501867915468220299129)
                      ·
                        rfl

theorem cell23_5004087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_5004087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004087 prefixEnd_5004087 := by exact prefixLift 5004087
  have htrace : WordTrace (prefixWord ++ tailWord_5004087) baseStart_5004087 baseEnd_5004087 := by
    simpa [prefixWord, tailWord_5004087, baseEnd_5004087] using wordTrace_append hprefix tailTrace_5004087
  have hstable : (prefixWord ++ tailWord_5004087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004087).length < 2 ^ (prefixWord ++ tailWord_5004087).sum := by decide
  have hdescent : baseEnd_5004087 < baseStart_5004087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004096 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_5004096 : Nat := 118140960795 + 5004096 * 2 ^ 59
def prefixEnd_5004096 : Nat := 4983230072969 + 3 ^ 40 * 5004096 * 2
def baseEnd_5004096 : Nat := 2569506489241358685086587

theorem tailTrace_5004096 : CollatzResearch.WordTrace tailWord_5004096 prefixEnd_5004096 2569506489241358685086587 := by
  unfold tailWord_5004096
  simp only [CollatzResearch.WordTrace]
  refine ⟨91257187639511149200608071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121676250186014865600810761 91257187639511149200608071)
  ·
    refine ⟨136885781459266723800912107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91257187639511149200608071 136885781459266723800912107)
    ·
      refine ⟨205328672188900085701368161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136885781459266723800912107 205328672188900085701368161)
      ·
        refine ⟨153996504141675064276026121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205328672188900085701368161 153996504141675064276026121)
        ·
          refine ⟨115497378106256298207019591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153996504141675064276026121 115497378106256298207019591)
          ·
            refine ⟨173246067159384447310529387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115497378106256298207019591 173246067159384447310529387)
            ·
              refine ⟨259869100739076670965794081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173246067159384447310529387 259869100739076670965794081)
              ·
                refine ⟨194901825554307503224345561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259869100739076670965794081 194901825554307503224345561)
                ·
                  refine ⟨146176369165730627418259171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194901825554307503224345561 146176369165730627418259171)
                  ·
                    refine ⟨219264553748595941127388757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146176369165730627418259171 219264553748595941127388757)
                    ·
                      refine ⟨2569506489241358685086587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 219264553748595941127388757 2569506489241358685086587)
                      ·
                        rfl

theorem cell23_5004096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_5004096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004096 prefixEnd_5004096 := by exact prefixLift 5004096
  have htrace : WordTrace (prefixWord ++ tailWord_5004096) baseStart_5004096 baseEnd_5004096 := by
    simpa [prefixWord, tailWord_5004096, baseEnd_5004096] using wordTrace_append hprefix tailTrace_5004096
  have hstable : (prefixWord ++ tailWord_5004096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004096).length < 2 ^ (prefixWord ++ tailWord_5004096).sum := by decide
  have hdescent : baseEnd_5004096 < baseStart_5004096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004103 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_5004103 : Nat := 118140960795 + 5004103 * 2 ^ 59
def prefixEnd_5004103 : Nat := 4983230072969 + 3 ^ 40 * 5004103 * 2
def baseEnd_5004103 : Nat := 2569510083605940157699055

theorem tailTrace_5004103 : CollatzResearch.WordTrace tailWord_5004103 prefixEnd_5004103 2569510083605940157699055 := by
  unfold tailWord_5004103
  simp only [CollatzResearch.WordTrace]
  refine ⟨182514630589996938596720963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121676420393331292397813975 182514630589996938596720963)
  ·
    refine ⟨273771945884995407895081445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182514630589996938596720963 273771945884995407895081445)
    ·
      refine ⟨51332239853436638980327771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273771945884995407895081445 51332239853436638980327771)
      ·
        refine ⟨76998359780154958470491657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51332239853436638980327771 76998359780154958470491657)
        ·
          refine ⟨57748769835116218852868743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76998359780154958470491657 57748769835116218852868743)
          ·
            refine ⟨86623154752674328279303115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57748769835116218852868743 86623154752674328279303115)
            ·
              refine ⟨129934732129011492418954673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86623154752674328279303115 129934732129011492418954673)
              ·
                refine ⟨97451049096758619314216005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129934732129011492418954673 97451049096758619314216005)
                ·
                  refine ⟨18272071705642241121415501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97451049096758619314216005 18272071705642241121415501)
                  ·
                    refine ⟨6852026889615840420530813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18272071705642241121415501 6852026889615840420530813)
                    ·
                      refine ⟨2569510083605940157699055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6852026889615840420530813 2569510083605940157699055)
                      ·
                        rfl

theorem cell23_5004103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_5004103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004103 prefixEnd_5004103 := by exact prefixLift 5004103
  have htrace : WordTrace (prefixWord ++ tailWord_5004103) baseStart_5004103 baseEnd_5004103 := by
    simpa [prefixWord, tailWord_5004103, baseEnd_5004103] using wordTrace_append hprefix tailTrace_5004103
  have hstable : (prefixWord ++ tailWord_5004103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004103).length < 2 ^ (prefixWord ++ tailWord_5004103).sum := by decide
  have hdescent : baseEnd_5004103 < baseStart_5004103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004133 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_5004133 : Nat := 118140960795 + 5004133 * 2 ^ 59
def prefixEnd_5004133 : Nat := 4983230072969 + 3 ^ 40 * 5004133 * 2
def baseEnd_5004133 : Nat := 2569525488025575040323917

theorem tailTrace_5004133 : CollatzResearch.WordTrace tailWord_5004133 prefixEnd_5004133 2569525488025575040323917 := by
  unfold tailWord_5004133
  simp only [CollatzResearch.WordTrace]
  refine ⟨182515724779888253720313053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121677149853258835813542035 182515724779888253720313053)
  ·
    refine ⟨68443396792458095145117395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182515724779888253720313053 68443396792458095145117395)
    ·
      refine ⟨102665095188687142717676093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68443396792458095145117395 102665095188687142717676093)
      ·
        refine ⟨38499410695757678519128535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102665095188687142717676093 38499410695757678519128535)
        ·
          refine ⟨57749116043636517778692803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38499410695757678519128535 57749116043636517778692803)
          ·
            refine ⟨86623674065454776668039205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57749116043636517778692803 86623674065454776668039205)
            ·
              refine ⟨16241938887272770625257351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86623674065454776668039205 16241938887272770625257351)
              ·
                refine ⟨24362908330909155937886027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16241938887272770625257351 24362908330909155937886027)
                ·
                  refine ⟨36544362496363733906829041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24362908330909155937886027 36544362496363733906829041)
                  ·
                    refine ⟨27408271872272800430121781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36544362496363733906829041 27408271872272800430121781)
                    ·
                      refine ⟨2569525488025575040323917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27408271872272800430121781 2569525488025575040323917)
                      ·
                        rfl

theorem cell23_5004133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_5004133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004133 prefixEnd_5004133 := by exact prefixLift 5004133
  have htrace : WordTrace (prefixWord ++ tailWord_5004133) baseStart_5004133 baseEnd_5004133 := by
    simpa [prefixWord, tailWord_5004133, baseEnd_5004133] using wordTrace_append hprefix tailTrace_5004133
  have hstable : (prefixWord ++ tailWord_5004133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004133).length < 2 ^ (prefixWord ++ tailWord_5004133).sum := by decide
  have hdescent : baseEnd_5004133 < baseStart_5004133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004143 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_5004143 : Nat := 118140960795 + 5004143 * 2 ^ 59
def prefixEnd_5004143 : Nat := 4983230072969 + 3 ^ 40 * 5004143 * 2
def baseEnd_5004143 : Nat := 2569530622832120001198871

theorem tailTrace_5004143 : CollatzResearch.WordTrace tailWord_5004143 prefixEnd_5004143 2569530622832120001198871 := by
  unfold tailWord_5004143
  simp only [CollatzResearch.WordTrace]
  refine ⟨182516089509852025428177083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121677393006568016952118055 182516089509852025428177083)
  ·
    refine ⟨273774134264778038142265625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182516089509852025428177083 273774134264778038142265625)
    ·
      refine ⟨205330600698583528606699219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273774134264778038142265625 205330600698583528606699219)
      ·
        refine ⟨307995901047875292910048829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205330600698583528606699219 307995901047875292910048829)
        ·
          refine ⟨115498462892953234841268311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307995901047875292910048829 115498462892953234841268311)
          ·
            refine ⟨173247694339429852261902467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115498462892953234841268311 173247694339429852261902467)
            ·
              refine ⟨259871541509144778392853701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173247694339429852261902467 259871541509144778392853701)
              ·
                refine ⟨48725914032964645948660069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259871541509144778392853701 48725914032964645948660069)
                ·
                  refine ⟨9136108881180871115373763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48725914032964645948660069 9136108881180871115373763)
                  ·
                    refine ⟨13704163321771306673060645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9136108881180871115373763 13704163321771306673060645)
                    ·
                      refine ⟨2569530622832120001198871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13704163321771306673060645 2569530622832120001198871)
                      ·
                        rfl

theorem cell23_5004143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_5004143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004143 prefixEnd_5004143 := by exact prefixLift 5004143
  have htrace : WordTrace (prefixWord ++ tailWord_5004143) baseStart_5004143 baseEnd_5004143 := by
    simpa [prefixWord, tailWord_5004143, baseEnd_5004143] using wordTrace_append hprefix tailTrace_5004143
  have hstable : (prefixWord ++ tailWord_5004143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004143).length < 2 ^ (prefixWord ++ tailWord_5004143).sum := by decide
  have hdescent : baseEnd_5004143 < baseStart_5004143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004183 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 8]
def baseStart_5004183 : Nat := 118140960795 + 5004183 * 2 ^ 59
def prefixEnd_5004183 : Nat := 4983230072969 + 3 ^ 40 * 5004183 * 2
def baseEnd_5004183 : Nat := 285505684673144427188743

theorem tailTrace_5004183 : CollatzResearch.WordTrace tailWord_5004183 prefixEnd_5004183 285505684673144427188743 := by
  unfold tailWord_5004183
  simp only [CollatzResearch.WordTrace]
  refine ⟨182517548429707112259633203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121678365619804741506422135 182517548429707112259633203)
  ·
    refine ⟨273776322644560668389449805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182517548429707112259633203 273776322644560668389449805)
    ·
      refine ⟨102666120991710250646043677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273776322644560668389449805 102666120991710250646043677)
      ·
        refine ⟨38499795371891343992266379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102666120991710250646043677 38499795371891343992266379)
        ·
          refine ⟨57749693057837015988399569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38499795371891343992266379 57749693057837015988399569)
          ·
            refine ⟨43312269793377761991299677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57749693057837015988399569 43312269793377761991299677)
            ·
              refine ⟨16242101172516660746737379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43312269793377761991299677 16242101172516660746737379)
              ·
                refine ⟨24363151758774991120106069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16242101172516660746737379 24363151758774991120106069)
                ·
                  refine ⟨285505684673144427188743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24363151758774991120106069 285505684673144427188743)
                  ·
                    rfl

theorem cell23_5004183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 8].length) (baseStart_5004183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004183 prefixEnd_5004183 := by exact prefixLift 5004183
  have htrace : WordTrace (prefixWord ++ tailWord_5004183) baseStart_5004183 baseEnd_5004183 := by
    simpa [prefixWord, tailWord_5004183, baseEnd_5004183] using wordTrace_append hprefix tailTrace_5004183
  have hstable : (prefixWord ++ tailWord_5004183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004183).length < 2 ^ (prefixWord ++ tailWord_5004183).sum := by decide
  have hdescent : baseEnd_5004183 < baseStart_5004183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004221 : List Nat := [1, 4, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_5004221 : Nat := 118140960795 + 5004221 * 2 ^ 59
def prefixEnd_5004221 : Nat := 4983230072969 + 3 ^ 40 * 5004221 * 2
def baseEnd_5004221 : Nat := 856523558107723565341171

theorem tailTrace_5004221 : CollatzResearch.WordTrace tailWord_5004221 prefixEnd_5004221 856523558107723565341171 := by
  unfold tailWord_5004221
  simp only [CollatzResearch.WordTrace]
  refine ⟨182518934403569444749516517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121679289602379629833011011 182518934403569444749516517)
  ·
    refine ⟨34222300200669270890534347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182518934403569444749516517 34222300200669270890534347)
    ·
      refine ⟨51333450301003906335801521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34222300200669270890534347 51333450301003906335801521)
      ·
        refine ⟨38500087725752929751851141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51333450301003906335801521 38500087725752929751851141)
        ·
          refine ⟨7218766448578674328472089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38500087725752929751851141 7218766448578674328472089)
          ·
            refine ⟨5414074836434005746354067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7218766448578674328472089 5414074836434005746354067)
            ·
              refine ⟨8121112254651008619531101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414074836434005746354067 8121112254651008619531101)
              ·
                refine ⟨3045417095494128232324163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8121112254651008619531101 3045417095494128232324163)
                ·
                  refine ⟨4568125643241192348486245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045417095494128232324163 4568125643241192348486245)
                  ·
                    refine ⟨856523558107723565341171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4568125643241192348486245 856523558107723565341171)
                    ·
                      rfl

theorem cell23_5004221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_5004221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004221 prefixEnd_5004221 := by exact prefixLift 5004221
  have htrace : WordTrace (prefixWord ++ tailWord_5004221) baseStart_5004221 baseEnd_5004221 := by
    simpa [prefixWord, tailWord_5004221, baseEnd_5004221] using wordTrace_append hprefix tailTrace_5004221
  have hstable : (prefixWord ++ tailWord_5004221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004221).length < 2 ^ (prefixWord ++ tailWord_5004221).sum := by decide
  have hdescent : baseEnd_5004221 < baseStart_5004221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004244 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5004244 : Nat := 118140960795 + 5004244 * 2 ^ 59
def prefixEnd_5004244 : Nat := 4983230072969 + 3 ^ 40 * 5004244 * 2
def baseEnd_5004244 : Nat := 2569582484378224106035907

theorem tailTrace_5004244 : CollatzResearch.WordTrace tailWord_5004244 prefixEnd_5004244 2569582484378224106035907 := by
  unfold tailWord_5004244
  simp only [CollatzResearch.WordTrace]
  refine ⟨91259886641243059838801893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121679848854990746451735857 91259886641243059838801893)
  ·
    refine ⟨17111228745233073719775355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91259886641243059838801893 17111228745233073719775355)
    ·
      refine ⟨25666843117849610579663033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17111228745233073719775355 25666843117849610579663033)
      ·
        refine ⟨19250132338387207934747275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25666843117849610579663033 19250132338387207934747275)
        ·
          refine ⟨28875198507580811902120913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19250132338387207934747275 28875198507580811902120913)
          ·
            refine ⟨21656398880685608926590685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28875198507580811902120913 21656398880685608926590685)
            ·
              refine ⟨8121149580257103347471507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21656398880685608926590685 8121149580257103347471507)
              ·
                refine ⟨12181724370385655021207261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121149580257103347471507 12181724370385655021207261)
                ·
                  refine ⟨4568146638894620632952723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12181724370385655021207261 4568146638894620632952723)
                  ·
                    refine ⟨6852219958341930949429085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568146638894620632952723 6852219958341930949429085)
                    ·
                      refine ⟨2569582484378224106035907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6852219958341930949429085 2569582484378224106035907)
                      ·
                        rfl

theorem cell23_5004244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5004244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004244 prefixEnd_5004244 := by exact prefixLift 5004244
  have htrace : WordTrace (prefixWord ++ tailWord_5004244) baseStart_5004244 baseEnd_5004244 := by
    simpa [prefixWord, tailWord_5004244, baseEnd_5004244] using wordTrace_append hprefix tailTrace_5004244
  have hstable : (prefixWord ++ tailWord_5004244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004244).length < 2 ^ (prefixWord ++ tailWord_5004244).sum := by decide
  have hdescent : baseEnd_5004244 < baseStart_5004244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004260 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_5004260 : Nat := 118140960795 + 5004260 * 2 ^ 59
def prefixEnd_5004260 : Nat := 4983230072969 + 3 ^ 40 * 5004260 * 2
def baseEnd_5004260 : Nat := 856530233356232014478611

theorem tailTrace_5004260 : CollatzResearch.WordTrace tailWord_5004260 prefixEnd_5004260 856530233356232014478611 := by
  unfold tailWord_5004260
  simp only [CollatzResearch.WordTrace]
  refine ⟨91260178425214077205093117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121680237900285436273457489 91260178425214077205093117)
  ·
    refine ⟨34222566909455278951909919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91260178425214077205093117 34222566909455278951909919)
    ·
      refine ⟨51333850364182918427864879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34222566909455278951909919 51333850364182918427864879)
      ·
        refine ⟨77000775546274377641797319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51333850364182918427864879 77000775546274377641797319)
        ·
          refine ⟨115501163319411566462695979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77000775546274377641797319 115501163319411566462695979)
          ·
            refine ⟨173251744979117349694043969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115501163319411566462695979 173251744979117349694043969)
            ·
              refine ⟨129938808734338012270532977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173251744979117349694043969 129938808734338012270532977)
              ·
                refine ⟨97454106550753509202899733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129938808734338012270532977 97454106550753509202899733)
                ·
                  refine ⟨4568161244566570743885925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97454106550753509202899733 4568161244566570743885925)
                  ·
                    refine ⟨856530233356232014478611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4568161244566570743885925 856530233356232014478611)
                    ·
                      rfl

theorem cell23_5004260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_5004260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004260 prefixEnd_5004260 := by exact prefixLift 5004260
  have htrace : WordTrace (prefixWord ++ tailWord_5004260) baseStart_5004260 baseEnd_5004260 := by
    simpa [prefixWord, tailWord_5004260, baseEnd_5004260] using wordTrace_append hprefix tailTrace_5004260
  have hstable : (prefixWord ++ tailWord_5004260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004260).length < 2 ^ (prefixWord ++ tailWord_5004260).sum := by decide
  have hdescent : baseEnd_5004260 < baseStart_5004260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004284 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_5004284 : Nat := 118140960795 + 5004284 * 2 ^ 59
def prefixEnd_5004284 : Nat := 4983230072969 + 3 ^ 40 * 5004284 * 2
def baseEnd_5004284 : Nat := 2569603023604403949535723

theorem tailTrace_5004284 : CollatzResearch.WordTrace tailWord_5004284 prefixEnd_5004284 2569603023604403949535723 := by
  unfold tailWord_5004284
  simp only [CollatzResearch.WordTrace]
  refine ⟨91260616101170603254529953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121680821468227471006039937 91260616101170603254529953)
  ·
    refine ⟨68445462075877952440897465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91260616101170603254529953 68445462075877952440897465)
    ·
      refine ⟨51334096556908464330673099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68445462075877952440897465 51334096556908464330673099)
      ·
        refine ⟨77001144835362696496009649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51334096556908464330673099 77001144835362696496009649)
        ·
          refine ⟨57750858626522022372007237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77001144835362696496009649 57750858626522022372007237)
          ·
            refine ⟨10828285992472879194751357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57750858626522022372007237 10828285992472879194751357)
            ·
              refine ⟨4060607247177329698031759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10828285992472879194751357 4060607247177329698031759)
              ·
                refine ⟨6090910870765994547047639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4060607247177329698031759 6090910870765994547047639)
                ·
                  refine ⟨9136366306148991820571459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6090910870765994547047639 9136366306148991820571459)
                  ·
                    refine ⟨13704549459223487730857189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9136366306148991820571459 13704549459223487730857189)
                    ·
                      refine ⟨2569603023604403949535723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13704549459223487730857189 2569603023604403949535723)
                      ·
                        rfl

theorem cell23_5004284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_5004284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004284 prefixEnd_5004284 := by exact prefixLift 5004284
  have htrace : WordTrace (prefixWord ++ tailWord_5004284) baseStart_5004284 baseEnd_5004284 := by
    simpa [prefixWord, tailWord_5004284, baseEnd_5004284] using wordTrace_append hprefix tailTrace_5004284
  have hstable : (prefixWord ++ tailWord_5004284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004284).length < 2 ^ (prefixWord ++ tailWord_5004284).sum := by decide
  have hdescent : baseEnd_5004284 < baseStart_5004284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004334 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5004334 : Nat := 118140960795 + 5004334 * 2 ^ 59
def prefixEnd_5004334 : Nat := 4983230072969 + 3 ^ 40 * 5004334 * 2
def baseEnd_5004334 : Nat := 2569628697637128753910493

theorem tailTrace_5004334 : CollatzResearch.WordTrace tailWord_5004334 prefixEnd_5004334 2569628697637128753910493 := by
  unfold tailWord_5004334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22815381981520008131047507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121682037234773376698920037 22815381981520008131047507)
  ·
    refine ⟨34223072972280012196571261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22815381981520008131047507 34223072972280012196571261)
    ·
      refine ⟨12833652364605004573714223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34223072972280012196571261 12833652364605004573714223)
      ·
        refine ⟨19250478546907506860571335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12833652364605004573714223 19250478546907506860571335)
        ·
          refine ⟨28875717820361260290857003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19250478546907506860571335 28875717820361260290857003)
          ·
            refine ⟨43313576730541890436285505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28875717820361260290857003 43313576730541890436285505)
            ·
              refine ⟨32485182547906417827214129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43313576730541890436285505 32485182547906417827214129)
              ·
                refine ⟨24363886910929813370410597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32485182547906417827214129 24363886910929813370410597)
                ·
                  refine ⟨4568228795799340006951987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24363886910929813370410597 4568228795799340006951987)
                  ·
                    refine ⟨6852343193699010010427981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568228795799340006951987 6852343193699010010427981)
                    ·
                      refine ⟨2569628697637128753910493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6852343193699010010427981 2569628697637128753910493)
                      ·
                        rfl

theorem cell23_5004334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5004334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004334 prefixEnd_5004334 := by exact prefixLift 5004334
  have htrace : WordTrace (prefixWord ++ tailWord_5004334) baseStart_5004334 baseEnd_5004334 := by
    simpa [prefixWord, tailWord_5004334, baseEnd_5004334] using wordTrace_append hprefix tailTrace_5004334
  have hstable : (prefixWord ++ tailWord_5004334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004334).length < 2 ^ (prefixWord ++ tailWord_5004334).sum := by decide
  have hdescent : baseEnd_5004334 < baseStart_5004334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004357 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 3, 4, 2]
def baseStart_5004357 : Nat := 118140960795 + 5004357 * 2 ^ 59
def prefixEnd_5004357 : Nat := 4983230072969 + 3 ^ 40 * 5004357 * 2
def baseEnd_5004357 : Nat := 2569640507692182163922887

theorem tailTrace_5004357 : CollatzResearch.WordTrace tailWord_5004357 prefixEnd_5004357 2569640507692182163922887 := by
  unfold tailWord_5004357
  simp only [CollatzResearch.WordTrace]
  refine ⟨182523894731076739976467325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121682596487384493317644883 182523894731076739976467325)
  ·
    refine ⟨68446460524153777491175247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182523894731076739976467325 68446460524153777491175247)
    ·
      refine ⟨102669690786230666236762871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68446460524153777491175247 102669690786230666236762871)
      ·
        refine ⟨154004536179345999355144307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102669690786230666236762871 154004536179345999355144307)
        ·
          refine ⟨231006804269018999032716461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154004536179345999355144307 231006804269018999032716461)
          ·
            refine ⟨86627551600882124637268673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231006804269018999032716461 86627551600882124637268673)
            ·
              refine ⟨64970663700661593477951505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86627551600882124637268673 64970663700661593477951505)
              ·
                refine ⟨48727997775496195108463629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64970663700661593477951505 48727997775496195108463629)
                ·
                  refine ⟨18272999165811073165673861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48727997775496195108463629 18272999165811073165673861)
                  ·
                    refine ⟨3426187343589576218563849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18272999165811073165673861 3426187343589576218563849)
                    ·
                      refine ⟨2569640507692182163922887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426187343589576218563849 2569640507692182163922887)
                      ·
                        rfl

theorem cell23_5004357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_5004357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004357 prefixEnd_5004357 := by exact prefixLift 5004357
  have htrace : WordTrace (prefixWord ++ tailWord_5004357) baseStart_5004357 baseEnd_5004357 := by
    simpa [prefixWord, tailWord_5004357, baseEnd_5004357] using wordTrace_append hprefix tailTrace_5004357
  have hstable : (prefixWord ++ tailWord_5004357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004357).length < 2 ^ (prefixWord ++ tailWord_5004357).sum := by decide
  have hdescent : baseEnd_5004357 < baseStart_5004357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004444 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_5004444 : Nat := 118140960795 + 5004444 * 2 ^ 59
def prefixEnd_5004444 : Nat := 4983230072969 + 3 ^ 40 * 5004444 * 2
def baseEnd_5004444 : Nat := 856561726836374441178329

theorem tailTrace_5004444 : CollatzResearch.WordTrace tailWord_5004444 prefixEnd_5004444 856561726836374441178329 := by
  unfold tailWord_5004444
  simp only [CollatzResearch.WordTrace]
  refine ⟨91263533940880776917442193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121684711921174369223256257 91263533940880776917442193)
  ·
    refine ⟨68447650455660582688081645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91263533940880776917442193 68447650455660582688081645)
    ·
      refine ⟨25667868920872718508030617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68447650455660582688081645 25667868920872718508030617)
      ·
        refine ⟨19250901690654538881022963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25667868920872718508030617 19250901690654538881022963)
        ·
          refine ⟨28876352535981808321534445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19250901690654538881022963 28876352535981808321534445)
          ·
            refine ⟨10828632200993178120575417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28876352535981808321534445 10828632200993178120575417)
            ·
              refine ⟨8121474150744883590431563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10828632200993178120575417 8121474150744883590431563)
              ·
                refine ⟨12182211226117325385647345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121474150744883590431563 12182211226117325385647345)
                ·
                  refine ⟨9136658419587994039235509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12182211226117325385647345 9136658419587994039235509)
                  ·
                    refine ⟨856561726836374441178329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9136658419587994039235509 856561726836374441178329)
                    ·
                      rfl

theorem cell23_5004444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_5004444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004444 prefixEnd_5004444 := by exact prefixLift 5004444
  have htrace : WordTrace (prefixWord ++ tailWord_5004444) baseStart_5004444 baseEnd_5004444 := by
    simpa [prefixWord, tailWord_5004444, baseEnd_5004444] using wordTrace_append hprefix tailTrace_5004444
  have hstable : (prefixWord ++ tailWord_5004444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004444).length < 2 ^ (prefixWord ++ tailWord_5004444).sum := by decide
  have hdescent : baseEnd_5004444 < baseStart_5004444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004481 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5004481 : Nat := 118140960795 + 5004481 * 2 ^ 59
def prefixEnd_5004481 : Nat := 4983230072969 + 3 ^ 40 * 5004481 * 2
def baseEnd_5004481 : Nat := 2569704179293339678772317

theorem tailTrace_5004481 : CollatzResearch.WordTrace tailWord_5004481 prefixEnd_5004481 2569704179293339678772317 := by
  unfold tailWord_5004481
  simp only [CollatzResearch.WordTrace]
  refine ⟨182528417382627509153981297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121685611588418339435987531 182528417382627509153981297)
  ·
    refine ⟨136896313036970631865485973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182528417382627509153981297 136896313036970631865485973)
    ·
      refine ⟨6417014673607998368694655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 136896313036970631865485973 6417014673607998368694655)
      ·
        refine ⟨9625522010411997553041983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417014673607998368694655 9625522010411997553041983)
        ·
          refine ⟨14438283015617996329562975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9625522010411997553041983 14438283015617996329562975)
          ·
            refine ⟨21657424523426994494344463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14438283015617996329562975 21657424523426994494344463)
            ·
              refine ⟨32486136785140491741516695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21657424523426994494344463 32486136785140491741516695)
              ·
                refine ⟨48729205177710737612275043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32486136785140491741516695 48729205177710737612275043)
                ·
                  refine ⟨73093807766566106418412565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48729205177710737612275043 73093807766566106418412565)
                  ·
                    refine ⟨3426272239057786238363089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73093807766566106418412565 3426272239057786238363089)
                    ·
                      refine ⟨2569704179293339678772317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426272239057786238363089 2569704179293339678772317)
                      ·
                        rfl

theorem cell23_5004481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5004481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004481 prefixEnd_5004481 := by exact prefixLift 5004481
  have htrace : WordTrace (prefixWord ++ tailWord_5004481) baseStart_5004481 baseEnd_5004481 := by
    simpa [prefixWord, tailWord_5004481, baseEnd_5004481] using wordTrace_append hprefix tailTrace_5004481
  have hstable : (prefixWord ++ tailWord_5004481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004481).length < 2 ^ (prefixWord ++ tailWord_5004481).sum := by decide
  have hdescent : baseEnd_5004481 < baseStart_5004481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004501 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5004501 : Nat := 118140960795 + 5004501 * 2 ^ 59
def prefixEnd_5004501 : Nat := 4983230072969 + 3 ^ 40 * 5004501 * 2
def baseEnd_5004501 : Nat := 2569714448906429600522225

theorem tailTrace_5004501 : CollatzResearch.WordTrace tailWord_5004501 prefixEnd_5004501 2569714448906429600522225 := by
  unfold tailWord_5004501
  simp only [CollatzResearch.WordTrace]
  refine ⟨182529146842555052569709357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121686097895036701713139571 182529146842555052569709357)
  ·
    refine ⟨68448430065958144713641009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182529146842555052569709357 68448430065958144713641009)
    ·
      refine ⟨51336322549468608535230757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68448430065958144713641009 51336322549468608535230757)
      ·
        refine ⟨9625560478025364100355767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51336322549468608535230757 9625560478025364100355767)
        ·
          refine ⟨14438340717038046150533651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9625560478025364100355767 14438340717038046150533651)
          ·
            refine ⟨21657511075557069225800477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14438340717038046150533651 21657511075557069225800477)
            ·
              refine ⟨8121566653333900959675179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21657511075557069225800477 8121566653333900959675179)
              ·
                refine ⟨12182349980000851439512769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121566653333900959675179 12182349980000851439512769)
                ·
                  refine ⟨9136762485000638579634577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12182349980000851439512769 9136762485000638579634577)
                  ·
                    refine ⟨6852571863750478934725933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9136762485000638579634577 6852571863750478934725933)
                    ·
                      refine ⟨2569714448906429600522225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6852571863750478934725933 2569714448906429600522225)
                      ·
                        rfl

theorem cell23_5004501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5004501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004501 prefixEnd_5004501 := by exact prefixLift 5004501
  have htrace : WordTrace (prefixWord ++ tailWord_5004501) baseStart_5004501 baseEnd_5004501 := by
    simpa [prefixWord, tailWord_5004501, baseEnd_5004501] using wordTrace_append hprefix tailTrace_5004501
  have hstable : (prefixWord ++ tailWord_5004501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004501).length < 2 ^ (prefixWord ++ tailWord_5004501).sum := by decide
  have hdescent : baseEnd_5004501 < baseStart_5004501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004531 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 3]
def baseStart_5004531 : Nat := 118140960795 + 5004531 * 2 ^ 59
def prefixEnd_5004531 : Nat := 4983230072969 + 3 ^ 40 * 5004531 * 2
def baseEnd_5004531 : Nat := 2569729853326064483147087

theorem tailTrace_5004531 : CollatzResearch.WordTrace tailWord_5004531 prefixEnd_5004531 2569729853326064483147087 := by
  unfold tailWord_5004531
  simp only [CollatzResearch.WordTrace]
  refine ⟨182530241032446367693301447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121686827354964245128867631 182530241032446367693301447)
  ·
    refine ⟨273795361548669551539952171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182530241032446367693301447 273795361548669551539952171)
    ·
      refine ⟨410693042323004327309928257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273795361548669551539952171 410693042323004327309928257)
      ·
        refine ⟨308019781742253245482446193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410693042323004327309928257 308019781742253245482446193)
        ·
          refine ⟨231014836306689934111834645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308019781742253245482446193 231014836306689934111834645)
          ·
            refine ⟨10828820451876090661492249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 231014836306689934111834645 10828820451876090661492249)
            ·
              refine ⟨8121615338907067996119187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10828820451876090661492249 8121615338907067996119187)
              ·
                refine ⟨12182423008360601994178781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121615338907067996119187 12182423008360601994178781)
                ·
                  refine ⟨4568408628135225747817043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12182423008360601994178781 4568408628135225747817043)
                  ·
                    refine ⟨6852612942202838621725565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568408628135225747817043 6852612942202838621725565)
                    ·
                      refine ⟨2569729853326064483147087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6852612942202838621725565 2569729853326064483147087)
                      ·
                        rfl

theorem cell23_5004531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 1, 3].length) (baseStart_5004531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004531 prefixEnd_5004531 := by exact prefixLift 5004531
  have htrace : WordTrace (prefixWord ++ tailWord_5004531) baseStart_5004531 baseEnd_5004531 := by
    simpa [prefixWord, tailWord_5004531, baseEnd_5004531] using wordTrace_append hprefix tailTrace_5004531
  have hstable : (prefixWord ++ tailWord_5004531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004531).length < 2 ^ (prefixWord ++ tailWord_5004531).sum := by decide
  have hdescent : baseEnd_5004531 < baseStart_5004531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004554 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_5004554 : Nat := 118140960795 + 5004554 * 2 ^ 59
def prefixEnd_5004554 : Nat := 4983230072969 + 3 ^ 40 * 5004554 * 2
def baseEnd_5004554 : Nat := 2569741663381117893159481

theorem tailTrace_5004554 : CollatzResearch.WordTrace tailWord_5004554 prefixEnd_5004554 2569741663381117893159481 := by
  unfold tailWord_5004554
  simp only [CollatzResearch.WordTrace]
  refine ⟨45632769977840760655347179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121687386607575361747592477 45632769977840760655347179)
  ·
    refine ⟨68449154966761140983020769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45632769977840760655347179 68449154966761140983020769)
    ·
      refine ⟨51336866225070855737265577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68449154966761140983020769 51336866225070855737265577)
      ·
        refine ⟨38502649668803141802949183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51336866225070855737265577 38502649668803141802949183)
        ·
          refine ⟨57753974503204712704423775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38502649668803141802949183 57753974503204712704423775)
          ·
            refine ⟨86630961754807069056635663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57753974503204712704423775 86630961754807069056635663)
            ·
              refine ⟨129946442632210603584953495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86630961754807069056635663 129946442632210603584953495)
              ·
                refine ⟨194919663948315905377430243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129946442632210603584953495 194919663948315905377430243)
                ·
                  refine ⟨292379495922473858066145365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194919663948315905377430243 292379495922473858066145365)
                  ·
                    refine ⟨3426322217841490524212641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 292379495922473858066145365 3426322217841490524212641)
                    ·
                      refine ⟨2569741663381117893159481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426322217841490524212641 2569741663381117893159481)
                      ·
                        rfl

theorem cell23_5004554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_5004554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004554 prefixEnd_5004554 := by exact prefixLift 5004554
  have htrace : WordTrace (prefixWord ++ tailWord_5004554) baseStart_5004554 baseEnd_5004554 := by
    simpa [prefixWord, tailWord_5004554, baseEnd_5004554] using wordTrace_append hprefix tailTrace_5004554
  have hstable : (prefixWord ++ tailWord_5004554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004554).length < 2 ^ (prefixWord ++ tailWord_5004554).sum := by decide
  have hdescent : baseEnd_5004554 < baseStart_5004554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004584 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5004584 : Nat := 118140960795 + 5004584 * 2 ^ 59
def prefixEnd_5004584 : Nat := 4983230072969 + 3 ^ 40 * 5004584 * 2
def baseEnd_5004584 : Nat := 2569757067800752775784343

theorem tailTrace_5004584 : CollatzResearch.WordTrace tailWord_5004584 prefixEnd_5004584 2569757067800752775784343 := by
  unfold tailWord_5004584
  simp only [CollatzResearch.WordTrace]
  refine ⟨91266087050627178872490403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121688116067502905163320537 91266087050627178872490403)
  ·
    refine ⟨136899130575940768308735605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91266087050627178872490403 136899130575940768308735605)
    ·
      refine ⟨12834293491494447028943963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136899130575940768308735605 12834293491494447028943963)
      ·
        refine ⟨19251440237241670543415945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12834293491494447028943963 19251440237241670543415945)
        ·
          refine ⟨14438580177931252907561959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19251440237241670543415945 14438580177931252907561959)
          ·
            refine ⟨21657870266896879361342939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14438580177931252907561959 21657870266896879361342939)
            ·
              refine ⟨32486805400345319042014409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21657870266896879361342939 32486805400345319042014409)
              ·
                refine ⟨24365104050258989281510807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32486805400345319042014409 24365104050258989281510807)
                ·
                  refine ⟨36547656075388483922266211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24365104050258989281510807 36547656075388483922266211)
                  ·
                    refine ⟨54821484113082725883399317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36547656075388483922266211 54821484113082725883399317)
                    ·
                      refine ⟨2569757067800752775784343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54821484113082725883399317 2569757067800752775784343)
                      ·
                        rfl

theorem cell23_5004584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5004584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004584 prefixEnd_5004584 := by exact prefixLift 5004584
  have htrace : WordTrace (prefixWord ++ tailWord_5004584) baseStart_5004584 baseEnd_5004584 := by
    simpa [prefixWord, tailWord_5004584, baseEnd_5004584] using wordTrace_append hprefix tailTrace_5004584
  have hstable : (prefixWord ++ tailWord_5004584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004584).length < 2 ^ (prefixWord ++ tailWord_5004584).sum := by decide
  have hdescent : baseEnd_5004584 < baseStart_5004584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004594 : List Nat := [3, 2, 1, 1, 4, 2, 2, 8]
def baseStart_5004594 : Nat := 118140960795 + 5004594 * 2 ^ 59
def prefixEnd_5004594 : Nat := 4983230072969 + 3 ^ 40 * 5004594 * 2
def baseEnd_5004594 : Nat := 95176377874344360617011

theorem tailTrace_5004594 : CollatzResearch.WordTrace tailWord_5004594 prefixEnd_5004594 95176377874344360617011 := by
  unfold tailWord_5004594
  simp only [CollatzResearch.WordTrace]
  refine ⟨45633134707804532363211209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121688359220812086301896557 45633134707804532363211209)
  ·
    refine ⟨34224851030853399272408407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45633134707804532363211209 34224851030853399272408407)
    ·
      refine ⟨51337276546280098908612611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34224851030853399272408407 51337276546280098908612611)
      ·
        refine ⟨77005914819420148362918917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51337276546280098908612611 77005914819420148362918917)
        ·
          refine ⟨14438609028641277818047297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77005914819420148362918917 14438609028641277818047297)
          ·
            refine ⟨10828956771480958363535473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14438609028641277818047297 10828956771480958363535473)
            ·
              refine ⟨8121717578610718772651605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10828956771480958363535473 8121717578610718772651605)
              ·
                refine ⟨95176377874344360617011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8121717578610718772651605 95176377874344360617011)
                ·
                  rfl

theorem cell23_5004594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 8].length) (baseStart_5004594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004594 prefixEnd_5004594 := by exact prefixLift 5004594
  have htrace : WordTrace (prefixWord ++ tailWord_5004594) baseStart_5004594 baseEnd_5004594 := by
    simpa [prefixWord, tailWord_5004594, baseEnd_5004594] using wordTrace_append hprefix tailTrace_5004594
  have hstable : (prefixWord ++ tailWord_5004594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004594).length < 2 ^ (prefixWord ++ tailWord_5004594).sum := by decide
  have hdescent : baseEnd_5004594 < baseStart_5004594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004605 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5004605 : Nat := 118140960795 + 5004605 * 2 ^ 59
def prefixEnd_5004605 : Nat := 4983230072969 + 3 ^ 40 * 5004605 * 2
def baseEnd_5004605 : Nat := 2569767850894497193621747

theorem tailTrace_5004605 : CollatzResearch.WordTrace tailWord_5004605 prefixEnd_5004605 2569767850894497193621747 := by
  unfold tailWord_5004605
  simp only [CollatzResearch.WordTrace]
  refine ⟨182532940034178278331495269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121688626689452185554330179 182532940034178278331495269)
  ·
    refine ⟨34224926256408427187155363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182532940034178278331495269 34224926256408427187155363)
    ·
      refine ⟨51337389384612640780733045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34224926256408427187155363 51337389384612640780733045)
      ·
        refine ⟨4812880254807435073193723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51337389384612640780733045 4812880254807435073193723)
        ·
          refine ⟨7219320382211152609790585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4812880254807435073193723 7219320382211152609790585)
          ·
            refine ⟨5414490286658364457342939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7219320382211152609790585 5414490286658364457342939)
            ·
              refine ⟨8121735429987546686014409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414490286658364457342939 8121735429987546686014409)
              ·
                refine ⟨6091301572490660014510807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8121735429987546686014409 6091301572490660014510807)
                ·
                  refine ⟨9136952358735990021766211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6091301572490660014510807 9136952358735990021766211)
                  ·
                    refine ⟨13705428538103985032649317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9136952358735990021766211 13705428538103985032649317)
                    ·
                      refine ⟨2569767850894497193621747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13705428538103985032649317 2569767850894497193621747)
                      ·
                        rfl

theorem cell23_5004605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5004605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004605 prefixEnd_5004605 := by exact prefixLift 5004605
  have htrace : WordTrace (prefixWord ++ tailWord_5004605) baseStart_5004605 baseEnd_5004605 := by
    simpa [prefixWord, tailWord_5004605, baseEnd_5004605] using wordTrace_append hprefix tailTrace_5004605
  have hstable : (prefixWord ++ tailWord_5004605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004605).length < 2 ^ (prefixWord ++ tailWord_5004605).sum := by decide
  have hdescent : baseEnd_5004605 < baseStart_5004605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004617 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_5004617 : Nat := 118140960795 + 5004617 * 2 ^ 59
def prefixEnd_5004617 : Nat := 4983230072969 + 3 ^ 40 * 5004617 * 2
def baseEnd_5004617 : Nat := 2569774012662351146671691

theorem tailTrace_5004617 : CollatzResearch.WordTrace tailWord_5004617 prefixEnd_5004617 2569774012662351146671691 := by
  unfold tailWord_5004617
  simp only [CollatzResearch.WordTrace]
  refine ⟨182533377710134804380932105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121688918473423202920621403 182533377710134804380932105)
  ·
    refine ⟨136900033282601103285699079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182533377710134804380932105 136900033282601103285699079)
    ·
      refine ⟨205350049923901654928548619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136900033282601103285699079 205350049923901654928548619)
      ·
        refine ⟨308025074885852482392822929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205350049923901654928548619 308025074885852482392822929)
        ·
          refine ⟨231018806164389361794617197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308025074885852482392822929 231018806164389361794617197)
          ·
            refine ⟨86632052311646010672981449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231018806164389361794617197 86632052311646010672981449)
            ·
              refine ⟨64974039233734508004736087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86632052311646010672981449 64974039233734508004736087)
              ·
                refine ⟨97461058850601762007104131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64974039233734508004736087 97461058850601762007104131)
                ·
                  refine ⟨146191588275902643010656197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97461058850601762007104131 146191588275902643010656197)
                  ·
                    refine ⟨27410922801731745564498037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146191588275902643010656197 27410922801731745564498037)
                    ·
                      refine ⟨2569774012662351146671691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27410922801731745564498037 2569774012662351146671691)
                      ·
                        rfl

theorem cell23_5004617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_5004617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004617 prefixEnd_5004617 := by exact prefixLift 5004617
  have htrace : WordTrace (prefixWord ++ tailWord_5004617) baseStart_5004617 baseEnd_5004617 := by
    simpa [prefixWord, tailWord_5004617, baseEnd_5004617] using wordTrace_append hprefix tailTrace_5004617
  have hstable : (prefixWord ++ tailWord_5004617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004617).length < 2 ^ (prefixWord ++ tailWord_5004617).sum := by decide
  have hdescent : baseEnd_5004617 < baseStart_5004617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004644 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_5004644 : Nat := 118140960795 + 5004644 * 2 ^ 59
def prefixEnd_5004644 : Nat := 4983230072969 + 3 ^ 40 * 5004644 * 2
def baseEnd_5004644 : Nat := 2569787876640022541034067

theorem tailTrace_5004644 : CollatzResearch.WordTrace tailWord_5004644 prefixEnd_5004644 2569787876640022541034067 := by
  unfold tailWord_5004644
  simp only [CollatzResearch.WordTrace]
  refine ⟨91267181240518493996082493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121689574987357991994776657 91267181240518493996082493)
  ·
    refine ⟨34225192965194435248530935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91267181240518493996082493 34225192965194435248530935)
    ·
      refine ⟨51337789447791652872796403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34225192965194435248530935 51337789447791652872796403)
      ·
        refine ⟨77006684171687479309194605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51337789447791652872796403 77006684171687479309194605)
        ·
          refine ⟨28877506564382804740947977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77006684171687479309194605 28877506564382804740947977)
          ·
            refine ⟨21658129923287103555710983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28877506564382804740947977 21658129923287103555710983)
            ·
              refine ⟨32487194884930655333566475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21658129923287103555710983 32487194884930655333566475)
              ·
                refine ⟨48730792327395983000349713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32487194884930655333566475 48730792327395983000349713)
                ·
                  refine ⟨36548094245546987250262285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48730792327395983000349713 36548094245546987250262285)
                  ·
                    refine ⟨13705535342080120218848357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36548094245546987250262285 13705535342080120218848357)
                    ·
                      refine ⟨2569787876640022541034067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13705535342080120218848357 2569787876640022541034067)
                      ·
                        rfl

theorem cell23_5004644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_5004644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004644 prefixEnd_5004644 := by exact prefixLift 5004644
  have htrace : WordTrace (prefixWord ++ tailWord_5004644) baseStart_5004644 baseEnd_5004644 := by
    simpa [prefixWord, tailWord_5004644, baseEnd_5004644] using wordTrace_append hprefix tailTrace_5004644
  have hstable : (prefixWord ++ tailWord_5004644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004644).length < 2 ^ (prefixWord ++ tailWord_5004644).sum := by decide
  have hdescent : baseEnd_5004644 < baseStart_5004644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004701 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 7]
def baseStart_5004701 : Nat := 118140960795 + 5004701 * 2 ^ 59
def prefixEnd_5004701 : Nat := 4983230072969 + 3 ^ 40 * 5004701 * 2
def baseEnd_5004701 : Nat := 285535238337480979780145

theorem tailTrace_5004701 : CollatzResearch.WordTrace tailWord_5004701 prefixEnd_5004701 285535238337480979780145 := by
  unfold tailWord_5004701
  simp only [CollatzResearch.WordTrace]
  refine ⟨182536441441830486726989957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121690960961220324484659971 182536441441830486726989957)
  ·
    refine ⟨34225582770343216261310617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182536441441830486726989957 34225582770343216261310617)
    ·
      refine ⟨25669187077757412195982963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34225582770343216261310617 25669187077757412195982963)
      ·
        refine ⟨38503780616636118293974445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25669187077757412195982963 38503780616636118293974445)
        ·
          refine ⟨14438917731238544360240417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38503780616636118293974445 14438917731238544360240417)
          ·
            refine ⟨10829188298428908270180313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14438917731238544360240417 10829188298428908270180313)
            ·
              refine ⟨8121891223821681202635235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10829188298428908270180313 8121891223821681202635235)
              ·
                refine ⟨12182836835732521803952853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121891223821681202635235 12182836835732521803952853)
                ·
                  refine ⟨285535238337480979780145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12182836835732521803952853 285535238337480979780145)
                  ·
                    rfl

theorem cell23_5004701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_5004701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004701 prefixEnd_5004701 := by exact prefixLift 5004701
  have htrace : WordTrace (prefixWord ++ tailWord_5004701) baseStart_5004701 baseEnd_5004701 := by
    simpa [prefixWord, tailWord_5004701, baseEnd_5004701] using wordTrace_append hprefix tailTrace_5004701
  have hstable : (prefixWord ++ tailWord_5004701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004701).length < 2 ^ (prefixWord ++ tailWord_5004701).sum := by decide
  have hdescent : baseEnd_5004701 < baseStart_5004701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004711 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_5004711 : Nat := 118140960795 + 5004711 * 2 ^ 59
def prefixEnd_5004711 : Nat := 4983230072969 + 3 ^ 40 * 5004711 * 2
def baseEnd_5004711 : Nat := 2569822279843873778896259

theorem tailTrace_5004711 : CollatzResearch.WordTrace tailWord_5004711 prefixEnd_5004711 2569822279843873778896259 := by
  unfold tailWord_5004711
  simp only [CollatzResearch.WordTrace]
  refine ⟨182536806171794258434853987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121691204114529505623235991 182536806171794258434853987)
  ·
    refine ⟨273805209257691387652280981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182536806171794258434853987 273805209257691387652280981)
    ·
      refine ⟨12834619183954283796200671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 273805209257691387652280981 12834619183954283796200671)
      ·
        refine ⟨19251928775931425694301007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12834619183954283796200671 19251928775931425694301007)
        ·
          refine ⟨28877893163897138541451511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19251928775931425694301007 28877893163897138541451511)
          ·
            refine ⟨43316839745845707812177267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28877893163897138541451511 43316839745845707812177267)
            ·
              refine ⟨64975259618768561718265901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43316839745845707812177267 64975259618768561718265901)
              ·
                refine ⟨24365722357038210644349713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64975259618768561718265901 24365722357038210644349713)
                ·
                  refine ⟨18274291767778657983262285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24365722357038210644349713 18274291767778657983262285)
                  ·
                    refine ⟨6852859412916996743723357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18274291767778657983262285 6852859412916996743723357)
                    ·
                      refine ⟨2569822279843873778896259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6852859412916996743723357 2569822279843873778896259)
                      ·
                        rfl

theorem cell23_5004711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_5004711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004711 prefixEnd_5004711 := by exact prefixLift 5004711
  have htrace : WordTrace (prefixWord ++ tailWord_5004711) baseStart_5004711 baseEnd_5004711 := by
    simpa [prefixWord, tailWord_5004711, baseEnd_5004711] using wordTrace_append hprefix tailTrace_5004711
  have hstable : (prefixWord ++ tailWord_5004711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004711).length < 2 ^ (prefixWord ++ tailWord_5004711).sum := by decide
  have hdescent : baseEnd_5004711 < baseStart_5004711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004712 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5004712 : Nat := 118140960795 + 5004712 * 2 ^ 59
def prefixEnd_5004712 : Nat := 4983230072969 + 3 ^ 40 * 5004712 * 2
def baseEnd_5004712 : Nat := 2569822793324528274983755

theorem tailTrace_5004712 : CollatzResearch.WordTrace tailWord_5004712 prefixEnd_5004712 2569822793324528274983755 := by
  unfold tailWord_5004712
  simp only [CollatzResearch.WordTrace]
  refine ⟨91268421322395317802820195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121691228429860423737093593 91268421322395317802820195)
  ·
    refine ⟨136902631983592976704230293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91268421322395317802820195 136902631983592976704230293)
    ·
      refine ⟨6417310874230920783010795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 136902631983592976704230293 6417310874230920783010795)
      ·
        refine ⟨9625966311346381174516193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417310874230920783010795 9625966311346381174516193)
        ·
          refine ⟨7219474733509785880887145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9625966311346381174516193 7219474733509785880887145)
          ·
            refine ⟨5414606050132339410665359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7219474733509785880887145 5414606050132339410665359)
            ·
              refine ⟨8121909075198509115998039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414606050132339410665359 8121909075198509115998039)
              ·
                refine ⟨12182863612797763673997059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121909075198509115998039 12182863612797763673997059)
                ·
                  refine ⟨18274295419196645510995589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12182863612797763673997059 18274295419196645510995589)
                  ·
                    refine ⟨3426430391099371033311673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18274295419196645510995589 3426430391099371033311673)
                    ·
                      refine ⟨2569822793324528274983755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426430391099371033311673 2569822793324528274983755)
                      ·
                        rfl

theorem cell23_5004712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5004712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004712 prefixEnd_5004712 := by exact prefixLift 5004712
  have htrace : WordTrace (prefixWord ++ tailWord_5004712) baseStart_5004712 baseEnd_5004712 := by
    simpa [prefixWord, tailWord_5004712, baseEnd_5004712] using wordTrace_append hprefix tailTrace_5004712
  have hstable : (prefixWord ++ tailWord_5004712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004712).length < 2 ^ (prefixWord ++ tailWord_5004712).sum := by decide
  have hdescent : baseEnd_5004712 < baseStart_5004712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004751 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 4, 4, 2]
def baseStart_5004751 : Nat := 118140960795 + 5004751 * 2 ^ 59
def prefixEnd_5004751 : Nat := 4983230072969 + 3 ^ 40 * 5004751 * 2
def baseEnd_5004751 : Nat := 2569842819070053622396075

theorem tailTrace_5004751 : CollatzResearch.WordTrace tailWord_5004751 prefixEnd_5004751 2569842819070053622396075 := by
  unfold tailWord_5004751
  simp only [CollatzResearch.WordTrace]
  refine ⟨182538265091649345266310107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121692176727766230177540071 182538265091649345266310107)
  ·
    refine ⟨273807397637474017899465161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182538265091649345266310107 273807397637474017899465161)
    ·
      refine ⟨205355548228105513424598871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273807397637474017899465161 205355548228105513424598871)
      ·
        refine ⟨308033322342158270136898307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205355548228105513424598871 308033322342158270136898307)
        ·
          refine ⟨462049983513237405205347461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308033322342158270136898307 462049983513237405205347461)
          ·
            refine ⟨86634371908732013476002649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 462049983513237405205347461 86634371908732013476002649)
            ·
              refine ⟨64975778931549010107001987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86634371908732013476002649 64975778931549010107001987)
              ·
                refine ⟨97463668397323515160502981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64975778931549010107001987 97463668397323515160502981)
                ·
                  refine ⟨18274437824498159092594309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97463668397323515160502981 18274437824498159092594309)
                  ·
                    refine ⟨3426457092093404829861433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18274437824498159092594309 3426457092093404829861433)
                    ·
                      refine ⟨2569842819070053622396075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426457092093404829861433 2569842819070053622396075)
                      ·
                        rfl

theorem cell23_5004751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 4, 2].length) (baseStart_5004751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004751 prefixEnd_5004751 := by exact prefixLift 5004751
  have htrace : WordTrace (prefixWord ++ tailWord_5004751) baseStart_5004751 baseEnd_5004751 := by
    simpa [prefixWord, tailWord_5004751, baseEnd_5004751] using wordTrace_append hprefix tailTrace_5004751
  have hstable : (prefixWord ++ tailWord_5004751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004751).length < 2 ^ (prefixWord ++ tailWord_5004751).sum := by decide
  have hdescent : baseEnd_5004751 < baseStart_5004751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004758 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5004758 : Nat := 118140960795 + 5004758 * 2 ^ 59
def prefixEnd_5004758 : Nat := 4983230072969 + 3 ^ 40 * 5004758 * 2
def baseEnd_5004758 : Nat := 2569846413434635095008543

theorem tailTrace_5004758 : CollatzResearch.WordTrace tailWord_5004758 prefixEnd_5004758 2569846413434635095008543 := by
  unfold tailWord_5004758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11408657525163999091363433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121692346935082656974543285 11408657525163999091363433)
  ·
    refine ⟨8556493143872999318522575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11408657525163999091363433 8556493143872999318522575)
    ·
      refine ⟨12834739715809498977783863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8556493143872999318522575 12834739715809498977783863)
      ·
        refine ⟨19252109573714248466675795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12834739715809498977783863 19252109573714248466675795)
        ·
          refine ⟨28878164360571372700013693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19252109573714248466675795 28878164360571372700013693)
          ·
            refine ⟨10829311635214264762505135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28878164360571372700013693 10829311635214264762505135)
            ·
              refine ⟨16243967452821397143757703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10829311635214264762505135 16243967452821397143757703)
              ·
                refine ⟨24365951179232095715636555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16243967452821397143757703 24365951179232095715636555)
                ·
                  refine ⟨36548926768848143573454833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24365951179232095715636555 36548926768848143573454833)
                  ·
                    refine ⟨27411695076636107680091125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36548926768848143573454833 27411695076636107680091125)
                    ·
                      refine ⟨2569846413434635095008543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27411695076636107680091125 2569846413434635095008543)
                      ·
                        rfl

theorem cell23_5004758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5004758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004758 prefixEnd_5004758 := by exact prefixLift 5004758
  have htrace : WordTrace (prefixWord ++ tailWord_5004758) baseStart_5004758 baseEnd_5004758 := by
    simpa [prefixWord, tailWord_5004758, baseEnd_5004758] using wordTrace_append hprefix tailTrace_5004758
  have hstable : (prefixWord ++ tailWord_5004758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004758).length < 2 ^ (prefixWord ++ tailWord_5004758).sum := by decide
  have hdescent : baseEnd_5004758 < baseStart_5004758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004821 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_5004821 : Nat := 118140960795 + 5004821 * 2 ^ 59
def prefixEnd_5004821 : Nat := 4983230072969 + 3 ^ 40 * 5004821 * 2
def baseEnd_5004821 : Nat := 856626254238622782840251

theorem tailTrace_5004821 : CollatzResearch.WordTrace tailWord_5004821 prefixEnd_5004821 856626254238622782840251 := by
  unfold tailWord_5004821
  simp only [CollatzResearch.WordTrace]
  refine ⟨182540818201395747221358317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121693878800930498147572211 182540818201395747221358317)
  ·
    refine ⟨68452806825523405208009369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182540818201395747221358317 68452806825523405208009369)
    ·
      refine ⟨51339605119142553906007027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68452806825523405208009369 51339605119142553906007027)
      ·
        refine ⟨77009407678713830859010541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51339605119142553906007027 77009407678713830859010541)
        ·
          refine ⟨28878527879517686572128953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77009407678713830859010541 28878527879517686572128953)
          ·
            refine ⟨21658895909638264929096715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28878527879517686572128953 21658895909638264929096715)
            ·
              refine ⟨32488343864457397393645073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21658895909638264929096715 32488343864457397393645073)
              ·
                refine ⟨24366257898343048045233805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32488343864457397393645073 24366257898343048045233805)
                ·
                  refine ⟨9137346711878643016962677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24366257898343048045233805 9137346711878643016962677)
                  ·
                    refine ⟨856626254238622782840251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9137346711878643016962677 856626254238622782840251)
                    ·
                      rfl

theorem cell23_5004821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_5004821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004821 prefixEnd_5004821 := by exact prefixLift 5004821
  have htrace : WordTrace (prefixWord ++ tailWord_5004821) baseStart_5004821 baseEnd_5004821 := by
    simpa [prefixWord, tailWord_5004821, baseEnd_5004821] using wordTrace_append hprefix tailTrace_5004821
  have hstable : (prefixWord ++ tailWord_5004821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004821).length < 2 ^ (prefixWord ++ tailWord_5004821).sum := by decide
  have hdescent : baseEnd_5004821 < baseStart_5004821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004828 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_5004828 : Nat := 118140960795 + 5004828 * 2 ^ 59
def prefixEnd_5004828 : Nat := 4983230072969 + 3 ^ 40 * 5004828 * 2
def baseEnd_5004828 : Nat := 2569882357080449821133221

theorem tailTrace_5004828 : CollatzResearch.WordTrace tailWord_5004828 prefixEnd_5004828 2569882357080449821133221 := by
  unfold tailWord_5004828
  simp only [CollatzResearch.WordTrace]
  refine ⟨91270536756185193708431569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121694049008246924944575425 91270536756185193708431569)
  ·
    refine ⟨68452902567138895281323677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91270536756185193708431569 68452902567138895281323677)
    ·
      refine ⟨25669838462677085730496379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68452902567138895281323677 25669838462677085730496379)
      ·
        refine ⟨38504757694015628595744569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25669838462677085730496379 38504757694015628595744569)
        ·
          refine ⟨28878568270511721446808427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38504757694015628595744569 28878568270511721446808427)
          ·
            refine ⟨43317852405767582170212641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28878568270511721446808427 43317852405767582170212641)
            ·
              refine ⟨32488389304325686627659481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43317852405767582170212641 32488389304325686627659481)
              ·
                refine ⟨24366291978244264970744611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32488389304325686627659481 24366291978244264970744611)
                ·
                  refine ⟨36549437967366397456116917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24366291978244264970744611 36549437967366397456116917)
                  ·
                    refine ⟨3426509809440599761510961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36549437967366397456116917 3426509809440599761510961)
                    ·
                      refine ⟨2569882357080449821133221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426509809440599761510961 2569882357080449821133221)
                      ·
                        rfl

theorem cell23_5004828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_5004828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004828 prefixEnd_5004828 := by exact prefixLift 5004828
  have htrace : WordTrace (prefixWord ++ tailWord_5004828) baseStart_5004828 baseEnd_5004828 := by
    simpa [prefixWord, tailWord_5004828, baseEnd_5004828] using wordTrace_append hprefix tailTrace_5004828
  have hstable : (prefixWord ++ tailWord_5004828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004828).length < 2 ^ (prefixWord ++ tailWord_5004828).sum := by decide
  have hdescent : baseEnd_5004828 < baseStart_5004828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004835 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 3]
def baseStart_5004835 : Nat := 118140960795 + 5004835 * 2 ^ 59
def prefixEnd_5004835 : Nat := 4983230072969 + 3 ^ 40 * 5004835 * 2
def baseEnd_5004835 : Nat := 2569885951445031293745689

theorem tailTrace_5004835 : CollatzResearch.WordTrace tailWord_5004835 prefixEnd_5004835 2569885951445031293745689 := by
  unfold tailWord_5004835
  simp only [CollatzResearch.WordTrace]
  refine ⟨182541328823345027612367959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121694219215563351741578639 182541328823345027612367959)
  ·
    refine ⟨273811993235017541418551939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182541328823345027612367959 273811993235017541418551939)
    ·
      refine ⟨410717989852526312127827909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273811993235017541418551939 410717989852526312127827909)
      ·
        refine ⟨77009623097348683523967733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 410717989852526312127827909 77009623097348683523967733)
        ·
          refine ⟨7219652165376439080371975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77009623097348683523967733 7219652165376439080371975)
          ·
            refine ⟨10829478248064658620557963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219652165376439080371975 10829478248064658620557963)
            ·
              refine ⟨16244217372096987930836945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10829478248064658620557963 16244217372096987930836945)
              ·
                refine ⟨12183163029072740948127709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16244217372096987930836945 12183163029072740948127709)
                ·
                  refine ⟨4568686135902277855547891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12183163029072740948127709 4568686135902277855547891)
                  ·
                    refine ⟨6853029203853416783321837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568686135902277855547891 6853029203853416783321837)
                    ·
                      refine ⟨2569885951445031293745689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6853029203853416783321837 2569885951445031293745689)
                      ·
                        rfl

theorem cell23_5004835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_5004835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004835 prefixEnd_5004835 := by exact prefixLift 5004835
  have htrace : WordTrace (prefixWord ++ tailWord_5004835) baseStart_5004835 baseEnd_5004835 := by
    simpa [prefixWord, tailWord_5004835, baseEnd_5004835] using wordTrace_append hprefix tailTrace_5004835
  have hstable : (prefixWord ++ tailWord_5004835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004835).length < 2 ^ (prefixWord ++ tailWord_5004835).sum := by decide
  have hdescent : baseEnd_5004835 < baseStart_5004835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004851 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 1, 6]
def baseStart_5004851 : Nat := 118140960795 + 5004851 * 2 ^ 59
def prefixEnd_5004851 : Nat := 4983230072969 + 3 ^ 40 * 5004851 * 2
def baseEnd_5004851 : Nat := 856631389045167743715205

theorem tailTrace_5004851 : CollatzResearch.WordTrace tailWord_5004851 prefixEnd_5004851 856631389045167743715205 := by
  unfold tailWord_5004851
  simp only [CollatzResearch.WordTrace]
  refine ⟨182541912391287062344950407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121694608260858041563300271 182541912391287062344950407)
  ·
    refine ⟨273812868586930593517425611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182541912391287062344950407 273812868586930593517425611)
    ·
      refine ⟨410719302880395890276138417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273812868586930593517425611 410719302880395890276138417)
      ·
        refine ⟨308039477160296917707103813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410719302880395890276138417 308039477160296917707103813)
        ·
          refine ⟨57757401967555672070081965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 308039477160296917707103813 57757401967555672070081965)
          ·
            refine ⟨21659025737833377026280737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57757401967555672070081965 21659025737833377026280737)
            ·
              refine ⟨16244269303375032769710553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21659025737833377026280737 16244269303375032769710553)
              ·
                refine ⟨12183201977531274577282915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16244269303375032769710553 12183201977531274577282915)
                ·
                  refine ⟨18274802966296911865924373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12183201977531274577282915 18274802966296911865924373)
                  ·
                    refine ⟨856631389045167743715205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18274802966296911865924373 856631389045167743715205)
                    ·
                      rfl

theorem cell23_5004851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 6].length) (baseStart_5004851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004851 prefixEnd_5004851 := by exact prefixLift 5004851
  have htrace : WordTrace (prefixWord ++ tailWord_5004851) baseStart_5004851 baseEnd_5004851 := by
    simpa [prefixWord, tailWord_5004851, baseEnd_5004851] using wordTrace_append hprefix tailTrace_5004851
  have hstable : (prefixWord ++ tailWord_5004851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004851).length < 2 ^ (prefixWord ++ tailWord_5004851).sum := by decide
  have hdescent : baseEnd_5004851 < baseStart_5004851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004855 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 1, 5]
def baseStart_5004855 : Nat := 118140960795 + 5004855 * 2 ^ 59
def prefixEnd_5004855 : Nat := 4983230072969 + 3 ^ 40 * 5004855 * 2
def baseEnd_5004855 : Nat := 856632073686040405165199

theorem tailTrace_5004855 : CollatzResearch.WordTrace tailWord_5004855 prefixEnd_5004855 856632073686040405165199 := by
  unfold tailWord_5004855
  simp only [CollatzResearch.WordTrace]
  refine ⟨182542058283272571028096019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121694705522181714018730679 182542058283272571028096019)
  ·
    refine ⟨273813087424908856542144029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182542058283272571028096019 273813087424908856542144029)
    ·
      refine ⟨102679907784340821203304011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273813087424908856542144029 102679907784340821203304011)
      ·
        refine ⟨154019861676511231804956017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102679907784340821203304011 154019861676511231804956017)
        ·
          refine ⟨115514896257383423853717013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154019861676511231804956017 115514896257383423853717013)
          ·
            refine ⟨5414760762064847993142985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115514896257383423853717013 5414760762064847993142985)
            ·
              refine ⟨4061070571548635994857239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5414760762064847993142985 4061070571548635994857239)
              ·
                refine ⟨6091605857322953992285859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4061070571548635994857239 6091605857322953992285859)
                ·
                  refine ⟨9137408785984430988428789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6091605857322953992285859 9137408785984430988428789)
                  ·
                    refine ⟨856632073686040405165199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9137408785984430988428789 856632073686040405165199)
                    ·
                      rfl

theorem cell23_5004855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_5004855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004855 prefixEnd_5004855 := by exact prefixLift 5004855
  have htrace : WordTrace (prefixWord ++ tailWord_5004855) baseStart_5004855 baseEnd_5004855 := by
    simpa [prefixWord, tailWord_5004855, baseEnd_5004855] using wordTrace_append hprefix tailTrace_5004855
  have hstable : (prefixWord ++ tailWord_5004855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004855).length < 2 ^ (prefixWord ++ tailWord_5004855).sum := by decide
  have hdescent : baseEnd_5004855 < baseStart_5004855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004858 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_5004858 : Nat := 118140960795 + 5004858 * 2 ^ 59
def prefixEnd_5004858 : Nat := 4983230072969 + 3 ^ 40 * 5004858 * 2
def baseEnd_5004858 : Nat := 2569897761500084703758083

theorem tailTrace_5004858 : CollatzResearch.WordTrace tailWord_5004858 prefixEnd_5004858 2569897761500084703758083 := by
  unfold tailWord_5004858
  simp only [CollatzResearch.WordTrace]
  refine ⟨45635541925565425635113807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121694778468174468360303485 45635541925565425635113807)
  ·
    refine ⟨68453312888348138452670711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45635541925565425635113807 68453312888348138452670711)
    ·
      refine ⟨102679969332522207679006067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68453312888348138452670711 102679969332522207679006067)
      ·
        refine ⟨154019953998783311518509101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102679969332522207679006067 154019953998783311518509101)
        ·
          refine ⟨57757482749543741819440913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154019953998783311518509101 57757482749543741819440913)
          ·
            refine ⟨43318112062157806364580685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57757482749543741819440913 43318112062157806364580685)
            ·
              refine ⟨16244292023309177386717757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43318112062157806364580685 16244292023309177386717757)
              ·
                refine ⟨6091609508740941520019159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16244292023309177386717757 6091609508740941520019159)
                ·
                  refine ⟨9137414263111412280028739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6091609508740941520019159 9137414263111412280028739)
                  ·
                    refine ⟨13706121394667118420043109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9137414263111412280028739 13706121394667118420043109)
                    ·
                      refine ⟨2569897761500084703758083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13706121394667118420043109 2569897761500084703758083)
                      ·
                        rfl

theorem cell23_5004858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_5004858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004858 prefixEnd_5004858 := by exact prefixLift 5004858
  have htrace : WordTrace (prefixWord ++ tailWord_5004858) baseStart_5004858 baseEnd_5004858 := by
    simpa [prefixWord, tailWord_5004858, baseEnd_5004858] using wordTrace_append hprefix tailTrace_5004858
  have hstable : (prefixWord ++ tailWord_5004858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004858).length < 2 ^ (prefixWord ++ tailWord_5004858).sum := by decide
  have hdescent : baseEnd_5004858 < baseStart_5004858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004892 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_5004892 : Nat := 118140960795 + 5004892 * 2 ^ 59
def prefixEnd_5004892 : Nat := 4983230072969 + 3 ^ 40 * 5004892 * 2
def baseEnd_5004892 : Nat := 2569915219842337570732927

theorem tailTrace_5004892 : CollatzResearch.WordTrace tailWord_5004892 prefixEnd_5004892 2569915219842337570732927 := by
  unfold tailWord_5004892
  simp only [CollatzResearch.WordTrace]
  refine ⟨91271703892069263173596465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121695605189425684231461953 91271703892069263173596465)
  ·
    refine ⟨68453777919051947380197349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91271703892069263173596465 68453777919051947380197349)
    ·
      refine ⟨12835083359822240133787003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68453777919051947380197349 12835083359822240133787003)
      ·
        refine ⟨19252625039733360200680505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12835083359822240133787003 19252625039733360200680505)
        ·
          refine ⟨14439468779800020150510379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19252625039733360200680505 14439468779800020150510379)
          ·
            refine ⟨21659203169700030225765569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14439468779800020150510379 21659203169700030225765569)
            ·
              refine ⟨16244402377275022669324177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21659203169700030225765569 16244402377275022669324177)
              ·
                refine ⟨12183301782956267001993133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16244402377275022669324177 12183301782956267001993133)
                ·
                  refine ⟨4568738168608600125747425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12183301782956267001993133 4568738168608600125747425)
                  ·
                    refine ⟨3426553626456450094310569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4568738168608600125747425 3426553626456450094310569)
                    ·
                      refine ⟨2569915219842337570732927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426553626456450094310569 2569915219842337570732927)
                      ·
                        rfl

theorem cell23_5004892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_5004892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004892 prefixEnd_5004892 := by exact prefixLift 5004892
  have htrace : WordTrace (prefixWord ++ tailWord_5004892) baseStart_5004892 baseEnd_5004892 := by
    simpa [prefixWord, tailWord_5004892, baseEnd_5004892] using wordTrace_append hprefix tailTrace_5004892
  have hstable : (prefixWord ++ tailWord_5004892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004892).length < 2 ^ (prefixWord ++ tailWord_5004892).sum := by decide
  have hdescent : baseEnd_5004892 < baseStart_5004892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004921 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_5004921 : Nat := 118140960795 + 5004921 * 2 ^ 59
def prefixEnd_5004921 : Nat := 4983230072969 + 3 ^ 40 * 5004921 * 2
def baseEnd_5004921 : Nat := 2569930110781317957270293

theorem tailTrace_5004921 : CollatzResearch.WordTrace tailWord_5004921 prefixEnd_5004921 2569930110781317957270293 := by
  unfold tailWord_5004921
  simp only [CollatzResearch.WordTrace]
  refine ⟨182544465501033464299998617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121696310334022309533332411 182544465501033464299998617)
  ·
    refine ⟨136908349125775098224998963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182544465501033464299998617 136908349125775098224998963)
    ·
      refine ⟨205362523688662647337498445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136908349125775098224998963 205362523688662647337498445)
      ·
        refine ⟨77010946383248492751561917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205362523688662647337498445 77010946383248492751561917)
        ·
          refine ⟨28879104893718184781835719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77010946383248492751561917 28879104893718184781835719)
          ·
            refine ⟨43318657340577277172753579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28879104893718184781835719 43318657340577277172753579)
            ·
              refine ⟨64977986010865915759130369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43318657340577277172753579 64977986010865915759130369)
              ·
                refine ⟨48733489508149436819347777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64977986010865915759130369 48733489508149436819347777)
                ·
                  refine ⟨36550117131112077614510833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48733489508149436819347777 36550117131112077614510833)
                  ·
                    refine ⟨27412587848334058210883125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36550117131112077614510833 27412587848334058210883125)
                    ·
                      refine ⟨2569930110781317957270293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27412587848334058210883125 2569930110781317957270293)
                      ·
                        rfl

theorem cell23_5004921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_5004921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004921 prefixEnd_5004921 := by exact prefixLift 5004921
  have htrace : WordTrace (prefixWord ++ tailWord_5004921) baseStart_5004921 baseEnd_5004921 := by
    simpa [prefixWord, tailWord_5004921, baseEnd_5004921] using wordTrace_append hprefix tailTrace_5004921
  have hstable : (prefixWord ++ tailWord_5004921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004921).length < 2 ^ (prefixWord ++ tailWord_5004921).sum := by decide
  have hdescent : baseEnd_5004921 < baseStart_5004921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004925 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_5004925 : Nat := 118140960795 + 5004925 * 2 ^ 59
def prefixEnd_5004925 : Nat := 4983230072969 + 3 ^ 40 * 5004925 * 2
def baseEnd_5004925 : Nat := 2569932164703935941620275

theorem tailTrace_5004925 : CollatzResearch.WordTrace tailWord_5004925 prefixEnd_5004925 2569932164703935941620275 := by
  unfold tailWord_5004925
  simp only [CollatzResearch.WordTrace]
  refine ⟨182544611393018972983144229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121696407595345981988762819 182544611393018972983144229)
  ·
    refine ⟨34227114636191057434339543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182544611393018972983144229 34227114636191057434339543)
    ·
      refine ⟨51340671954286586151509315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34227114636191057434339543 51340671954286586151509315)
      ·
        refine ⟨77011007931429879227263973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51340671954286586151509315 77011007931429879227263973)
        ·
          refine ⟨14439563987143102355111995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77011007931429879227263973 14439563987143102355111995)
          ·
            refine ⟨21659345980714653532667993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14439563987143102355111995 21659345980714653532667993)
            ·
              refine ⟨16244509485535990149500995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21659345980714653532667993 16244509485535990149500995)
              ·
                refine ⟨24366764228303985224251493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16244509485535990149500995 24366764228303985224251493)
                ·
                  refine ⟨4568768292806997229547155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24366764228303985224251493 4568768292806997229547155)
                  ·
                    refine ⟨6853152439210495844320733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568768292806997229547155 6853152439210495844320733)
                    ·
                      refine ⟨2569932164703935941620275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6853152439210495844320733 2569932164703935941620275)
                      ·
                        rfl

theorem cell23_5004925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_5004925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004925 prefixEnd_5004925 := by exact prefixLift 5004925
  have htrace : WordTrace (prefixWord ++ tailWord_5004925) baseStart_5004925 baseEnd_5004925 := by
    simpa [prefixWord, tailWord_5004925, baseEnd_5004925] using wordTrace_append hprefix tailTrace_5004925
  have hstable : (prefixWord ++ tailWord_5004925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004925).length < 2 ^ (prefixWord ++ tailWord_5004925).sum := by decide
  have hdescent : baseEnd_5004925 < baseStart_5004925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004931 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 4]
def baseStart_5004931 : Nat := 118140960795 + 5004931 * 2 ^ 59
def prefixEnd_5004931 : Nat := 4983230072969 + 3 ^ 40 * 5004931 * 2
def baseEnd_5004931 : Nat := 2569935245587862918145247

theorem tailTrace_5004931 : CollatzResearch.WordTrace tailWord_5004931 prefixEnd_5004931 2569935245587862918145247 := by
  unfold tailWord_5004931
  simp only [CollatzResearch.WordTrace]
  refine ⟨182544830230997236007862647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121696553487331490671908431 182544830230997236007862647)
  ·
    refine ⟨273817245346495854011793971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182544830230997236007862647 273817245346495854011793971)
    ·
      refine ⟨410725868019743781017690957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273817245346495854011793971 410725868019743781017690957)
      ·
        refine ⟨154022200507403917881634109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410725868019743781017690957 154022200507403917881634109)
        ·
          refine ⟨57758325190276469205612791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154022200507403917881634109 57758325190276469205612791)
          ·
            refine ⟨86637487785414703808419187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57758325190276469205612791 86637487785414703808419187)
            ·
              refine ⟨129956231678122055712628781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86637487785414703808419187 129956231678122055712628781)
              ·
                refine ⟨48733586879295770892235793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129956231678122055712628781 48733586879295770892235793)
                ·
                  refine ⟨36550190159471828169176845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48733586879295770892235793 36550190159471828169176845)
                  ·
                    refine ⟨13706321309801935563441317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36550190159471828169176845 13706321309801935563441317)
                    ·
                      refine ⟨2569935245587862918145247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13706321309801935563441317 2569935245587862918145247)
                      ·
                        rfl

theorem cell23_5004931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_5004931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004931 prefixEnd_5004931 := by exact prefixLift 5004931
  have htrace : WordTrace (prefixWord ++ tailWord_5004931) baseStart_5004931 baseEnd_5004931 := by
    simpa [prefixWord, tailWord_5004931, baseEnd_5004931] using wordTrace_append hprefix tailTrace_5004931
  have hstable : (prefixWord ++ tailWord_5004931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004931).length < 2 ^ (prefixWord ++ tailWord_5004931).sum := by decide
  have hdescent : baseEnd_5004931 < baseStart_5004931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004936 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 2, 4]
def baseStart_5004936 : Nat := 118140960795 + 5004936 * 2 ^ 59
def prefixEnd_5004936 : Nat := 4983230072969 + 3 ^ 40 * 5004936 * 2
def baseEnd_5004936 : Nat := 856645937663711799527575

theorem tailTrace_5004936 : CollatzResearch.WordTrace tailWord_5004936 prefixEnd_5004936 856645937663711799527575 := by
  unfold tailWord_5004936
  simp only [CollatzResearch.WordTrace]
  refine ⟨91272506297989560930897331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121696675063986081241196441 91272506297989560930897331)
  ·
    refine ⟨136908759446984341396345997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91272506297989560930897331 136908759446984341396345997)
    ·
      refine ⟨51340784792619128023629749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136908759446984341396345997 51340784792619128023629749)
      ·
        refine ⟨4813198574308043252215289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51340784792619128023629749 4813198574308043252215289)
        ·
          refine ⟨3609898930731032439161467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4813198574308043252215289 3609898930731032439161467)
          ·
            refine ⟨5414848396096548658742201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609898930731032439161467 5414848396096548658742201)
            ·
              refine ⟨4061136297072411494056651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5414848396096548658742201 4061136297072411494056651)
              ·
                refine ⟨6091704445608617241084977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4061136297072411494056651 6091704445608617241084977)
                ·
                  refine ⟨4568778334206462930813733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6091704445608617241084977 4568778334206462930813733)
                  ·
                    refine ⟨856645937663711799527575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4568778334206462930813733 856645937663711799527575)
                    ·
                      rfl

theorem cell23_5004936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_5004936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004936 prefixEnd_5004936 := by exact prefixLift 5004936
  have htrace : WordTrace (prefixWord ++ tailWord_5004936) baseStart_5004936 baseEnd_5004936 := by
    simpa [prefixWord, tailWord_5004936, baseEnd_5004936] using wordTrace_append hprefix tailTrace_5004936
  have hstable : (prefixWord ++ tailWord_5004936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004936).length < 2 ^ (prefixWord ++ tailWord_5004936).sum := by decide
  have hdescent : baseEnd_5004936 < baseStart_5004936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004942 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_5004942 : Nat := 118140960795 + 5004942 * 2 ^ 59
def prefixEnd_5004942 : Nat := 4983230072969 + 3 ^ 40 * 5004942 * 2
def baseEnd_5004942 : Nat := 2569940893875062375107697

theorem tailTrace_5004942 : CollatzResearch.WordTrace tailWord_5004942 prefixEnd_5004942 2569940893875062375107697 := by
  unfold tailWord_5004942
  simp only [CollatzResearch.WordTrace]
  refine ⟨22818153929244673110814135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121696820955971589924342053 22818153929244673110814135)
  ·
    refine ⟨34227230893867009666221203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22818153929244673110814135 34227230893867009666221203)
    ·
      refine ⟨51340846340800514499331805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34227230893867009666221203 51340846340800514499331805)
      ·
        refine ⟨19252817377800192937249427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51340846340800514499331805 19252817377800192937249427)
        ·
          refine ⟨28879226066700289405874141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19252817377800192937249427 28879226066700289405874141)
          ·
            refine ⟨10829709775012608527202803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28879226066700289405874141 10829709775012608527202803)
            ·
              refine ⟨16244564662518912790804205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10829709775012608527202803 16244564662518912790804205)
              ·
                refine ⟨6091711748444592296551577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16244564662518912790804205 6091711748444592296551577)
                ·
                  refine ⟨4568783811333444222413683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6091711748444592296551577 4568783811333444222413683)
                  ·
                    refine ⟨6853175717000166333620525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568783811333444222413683 6853175717000166333620525)
                    ·
                      refine ⟨2569940893875062375107697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6853175717000166333620525 2569940893875062375107697)
                      ·
                        rfl

theorem cell23_5004942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_5004942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004942 prefixEnd_5004942 := by exact prefixLift 5004942
  have htrace : WordTrace (prefixWord ++ tailWord_5004942) baseStart_5004942 baseEnd_5004942 := by
    simpa [prefixWord, tailWord_5004942, baseEnd_5004942] using wordTrace_append hprefix tailTrace_5004942
  have hstable : (prefixWord ++ tailWord_5004942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004942).length < 2 ^ (prefixWord ++ tailWord_5004942).sum := by decide
  have hdescent : baseEnd_5004942 < baseStart_5004942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004952 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 1, 3, 2]
def baseStart_5004952 : Nat := 118140960795 + 5004952 * 2 ^ 59
def prefixEnd_5004952 : Nat := 4983230072969 + 3 ^ 40 * 5004952 * 2
def baseEnd_5004952 : Nat := 2569946028681607335982651

theorem tailTrace_5004952 : CollatzResearch.WordTrace tailWord_5004952 prefixEnd_5004952 2569946028681607335982651 := by
  unfold tailWord_5004952
  simp only [CollatzResearch.WordTrace]
  refine ⟨91272798081960578297188555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121697064109280771062918073 91272798081960578297188555)
  ·
    refine ⟨136909197122940867445782833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91272798081960578297188555 136909197122940867445782833)
    ·
      refine ⟨102681897842205650584337125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136909197122940867445782833 102681897842205650584337125)
      ·
        refine ⟨19252855845413559484563211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102681897842205650584337125 19252855845413559484563211)
        ·
          refine ⟨28879283768120339226844817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19252855845413559484563211 28879283768120339226844817)
          ·
            refine ⟨21659462826090254420133613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28879283768120339226844817 21659462826090254420133613)
            ·
              refine ⟨8122298559783845407550105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21659462826090254420133613 8122298559783845407550105)
              ·
                refine ⟨6091723919837884055662579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8122298559783845407550105 6091723919837884055662579)
                ·
                  refine ⟨9137585879756826083493869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6091723919837884055662579 9137585879756826083493869)
                  ·
                    refine ⟨3426594704908809781310201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9137585879756826083493869 3426594704908809781310201)
                    ·
                      refine ⟨2569946028681607335982651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426594704908809781310201 2569946028681607335982651)
                      ·
                        rfl

theorem cell23_5004952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_5004952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004952 prefixEnd_5004952 := by exact prefixLift 5004952
  have htrace : WordTrace (prefixWord ++ tailWord_5004952) baseStart_5004952 baseEnd_5004952 := by
    simpa [prefixWord, tailWord_5004952, baseEnd_5004952] using wordTrace_append hprefix tailTrace_5004952
  have hstable : (prefixWord ++ tailWord_5004952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004952).length < 2 ^ (prefixWord ++ tailWord_5004952).sum := by decide
  have hdescent : baseEnd_5004952 < baseStart_5004952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5004965 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 6, 2, 2]
def baseStart_5004965 : Nat := 118140960795 + 5004965 * 2 ^ 59
def prefixEnd_5004965 : Nat := 4983230072969 + 3 ^ 40 * 5004965 * 2
def baseEnd_5004965 : Nat := 2569952703930115785120091

theorem tailTrace_5004965 : CollatzResearch.WordTrace tailWord_5004965 prefixEnd_5004965 2569952703930115785120091 := by
  unfold tailWord_5004965
  simp only [CollatzResearch.WordTrace]
  refine ⟨182546070312874059814600349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121697380208582706543066899 182546070312874059814600349)
  ·
    refine ⟨68454776367327772430475131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182546070312874059814600349 68454776367327772430475131)
    ·
      refine ⟨102682164550991658645712697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68454776367327772430475131 102682164550991658645712697)
      ·
        refine ⟨77011623413243743984284523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102682164550991658645712697 77011623413243743984284523)
        ·
          refine ⟨115517435119865615976426785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77011623413243743984284523 115517435119865615976426785)
          ·
            refine ⟨86638076339899211982320089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115517435119865615976426785 86638076339899211982320089)
            ·
              refine ⟨64978557254924408986740067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86638076339899211982320089 64978557254924408986740067)
              ·
                refine ⟨97467835882386613480110101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64978557254924408986740067 97467835882386613480110101)
                ·
                  refine ⟨4568804806986872506880161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97467835882386613480110101 4568804806986872506880161)
                  ·
                    refine ⟨3426603605240154380160121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4568804806986872506880161 3426603605240154380160121)
                    ·
                      refine ⟨2569952703930115785120091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426603605240154380160121 2569952703930115785120091)
                      ·
                        rfl

theorem cell23_5004965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_5004965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5004965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5004965 prefixEnd_5004965 := by exact prefixLift 5004965
  have htrace : WordTrace (prefixWord ++ tailWord_5004965) baseStart_5004965 baseEnd_5004965 := by
    simpa [prefixWord, tailWord_5004965, baseEnd_5004965] using wordTrace_append hprefix tailTrace_5004965
  have hstable : (prefixWord ++ tailWord_5004965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5004965).length < 2 ^ (prefixWord ++ tailWord_5004965).sum := by decide
  have hdescent : baseEnd_5004965 < baseStart_5004965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5004965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005005 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 9]
def baseStart_5005005 : Nat := 118140960795 + 5005005 * 2 ^ 59
def prefixEnd_5005005 : Nat := 4983230072969 + 3 ^ 40 * 5005005 * 2
def baseEnd_5005005 : Nat := 285552582572921736513323

theorem tailTrace_5005005 : CollatzResearch.WordTrace tailWord_5005005 prefixEnd_5005005 285552582572921736513323 := by
  unfold tailWord_5005005
  simp only [CollatzResearch.WordTrace]
  refine ⟨182547529232729146646056469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121698352821819431097370979 182547529232729146646056469)
  ·
    refine ⟨8556915432784178749033897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182547529232729146646056469 8556915432784178749033897)
    ·
      refine ⟨6417686574588134061775423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8556915432784178749033897 6417686574588134061775423)
      ·
        refine ⟨9626529861882201092663135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417686574588134061775423 9626529861882201092663135)
        ·
          refine ⟨14439794792823301638994703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9626529861882201092663135 14439794792823301638994703)
          ·
            refine ⟨21659692189234952458492055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14439794792823301638994703 21659692189234952458492055)
            ·
              refine ⟨32489538283852428687738083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21659692189234952458492055 32489538283852428687738083)
              ·
                refine ⟨48734307425778643031607125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32489538283852428687738083 48734307425778643031607125)
                ·
                  refine ⟨285552582572921736513323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48734307425778643031607125 285552582572921736513323)
                  ·
                    rfl

theorem cell23_5005005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_5005005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005005 prefixEnd_5005005 := by exact prefixLift 5005005
  have htrace : WordTrace (prefixWord ++ tailWord_5005005) baseStart_5005005 baseEnd_5005005 := by
    simpa [prefixWord, tailWord_5005005, baseEnd_5005005] using wordTrace_append hprefix tailTrace_5005005
  have hstable : (prefixWord ++ tailWord_5005005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005005).length < 2 ^ (prefixWord ++ tailWord_5005005).sum := by decide
  have hdescent : baseEnd_5005005 < baseStart_5005005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005018 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_5005018 : Nat := 118140960795 + 5005018 * 2 ^ 59
def prefixEnd_5005018 : Nat := 4983230072969 + 3 ^ 40 * 5005018 * 2
def baseEnd_5005018 : Nat := 856659972801601359252449

theorem tailTrace_5005018 : CollatzResearch.WordTrace tailWord_5005018 prefixEnd_5005018 856659972801601359252449 := by
  unfold tailWord_5005018
  simp only [CollatzResearch.WordTrace]
  refine ⟨45637000845420512466569927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121698668921121366577519805 45637000845420512466569927)
  ·
    refine ⟨68455501268130768699854891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45637000845420512466569927 68455501268130768699854891)
    ·
      refine ⟨102683251902196153049782337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68455501268130768699854891 102683251902196153049782337)
      ·
        refine ⟨77012438926647114787336753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102683251902196153049782337 77012438926647114787336753)
        ·
          refine ⟨57759329194985336090502565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77012438926647114787336753 57759329194985336090502565)
          ·
            refine ⟨10829874224059750516969231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57759329194985336090502565 10829874224059750516969231)
            ·
              refine ⟨16244811336089625775453847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10829874224059750516969231 16244811336089625775453847)
              ·
                refine ⟨24367217004134438663180771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16244811336089625775453847 24367217004134438663180771)
                ·
                  refine ⟨36550825506201657994771157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24367217004134438663180771 36550825506201657994771157)
                  ·
                    refine ⟨856659972801601359252449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36550825506201657994771157 856659972801601359252449)
                    ·
                      rfl

theorem cell23_5005018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_5005018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005018 prefixEnd_5005018 := by exact prefixLift 5005018
  have htrace : WordTrace (prefixWord ++ tailWord_5005018) baseStart_5005018 baseEnd_5005018 := by
    simpa [prefixWord, tailWord_5005018, baseEnd_5005018] using wordTrace_append hprefix tailTrace_5005018
  have hstable : (prefixWord ++ tailWord_5005018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005018).length < 2 ^ (prefixWord ++ tailWord_5005018).sum := by decide
  have hdescent : baseEnd_5005018 < baseStart_5005018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005055 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 2, 4, 2]
def baseStart_5005055 : Nat := 118140960795 + 5005055 * 2 ^ 59
def prefixEnd_5005055 : Nat := 4983230072969 + 3 ^ 40 * 5005055 * 2
def baseEnd_5005055 : Nat := 2569998917189020432994677

theorem tailTrace_5005055 : CollatzResearch.WordTrace tailWord_5005055 prefixEnd_5005055 2569998917189020432994677 := by
  unfold tailWord_5005055
  simp only [CollatzResearch.WordTrace]
  refine ⟨182549352882548005185376619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121699568588365336790251079 182549352882548005185376619)
  ·
    refine ⟨273824029323822007778064929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182549352882548005185376619 273824029323822007778064929)
    ·
      refine ⟨205368021992866505833548697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273824029323822007778064929 205368021992866505833548697)
      ·
        refine ⟨154026016494649879375161523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205368021992866505833548697 154026016494649879375161523)
        ·
          refine ⟨231039024741974819062742285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154026016494649879375161523 231039024741974819062742285)
          ·
            refine ⟨86639634278240557148528357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231039024741974819062742285 86639634278240557148528357)
            ·
              refine ⟨16244931427170104465349067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86639634278240557148528357 16244931427170104465349067)
              ·
                refine ⟨24367397140755156698023601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16244931427170104465349067 24367397140755156698023601)
                ·
                  refine ⟨18275547855566367523517701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24367397140755156698023601 18275547855566367523517701)
                  ·
                    refine ⟨3426665222918693910659569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18275547855566367523517701 3426665222918693910659569)
                    ·
                      refine ⟨2569998917189020432994677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426665222918693910659569 2569998917189020432994677)
                      ·
                        rfl

theorem cell23_5005055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_5005055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005055 prefixEnd_5005055 := by exact prefixLift 5005055
  have htrace : WordTrace (prefixWord ++ tailWord_5005055) baseStart_5005055 baseEnd_5005055 := by
    simpa [prefixWord, tailWord_5005055, baseEnd_5005055] using wordTrace_append hprefix tailTrace_5005055
  have hstable : (prefixWord ++ tailWord_5005055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005055).length < 2 ^ (prefixWord ++ tailWord_5005055).sum := by decide
  have hdescent : baseEnd_5005055 < baseStart_5005055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005092 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_5005092 : Nat := 118140960795 + 5005092 * 2 ^ 59
def prefixEnd_5005092 : Nat := 4983230072969 + 3 ^ 40 * 5005092 * 2
def baseEnd_5005092 : Nat := 2570017915973236788232007

theorem tailTrace_5005092 : CollatzResearch.WordTrace tailWord_5005092 prefixEnd_5005092 2570017915973236788232007 := by
  unfold tailWord_5005092
  simp only [CollatzResearch.WordTrace]
  refine ⟨91275351191706980252236765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121700468255609307002982353 91275351191706980252236765)
  ·
    refine ⟨34228256696890117594588787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91275351191706980252236765 34228256696890117594588787)
    ·
      refine ⟨51342385045335176391883181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34228256696890117594588787 51342385045335176391883181)
      ·
        refine ⟨19253394392000691146956193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51342385045335176391883181 19253394392000691146956193)
        ·
          refine ⟨14440045794000518360217145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19253394392000691146956193 14440045794000518360217145)
          ·
            refine ⟨10830034345500388770162859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14440045794000518360217145 10830034345500388770162859)
            ·
              refine ⟨16245051518250583155244289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10830034345500388770162859 16245051518250583155244289)
              ·
                refine ⟨12183788638687937366433217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16245051518250583155244289 12183788638687937366433217)
                ·
                  refine ⟨9137841479015953024824913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12183788638687937366433217 9137841479015953024824913)
                  ·
                    refine ⟨6853381109261964768618685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9137841479015953024824913 6853381109261964768618685)
                    ·
                      refine ⟨2570017915973236788232007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6853381109261964768618685 2570017915973236788232007)
                      ·
                        rfl

theorem cell23_5005092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_5005092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005092 prefixEnd_5005092 := by exact prefixLift 5005092
  have htrace : WordTrace (prefixWord ++ tailWord_5005092) baseStart_5005092 baseEnd_5005092 := by
    simpa [prefixWord, tailWord_5005092, baseEnd_5005092] using wordTrace_append hprefix tailTrace_5005092
  have hstable : (prefixWord ++ tailWord_5005092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005092).length < 2 ^ (prefixWord ++ tailWord_5005092).sum := by decide
  have hdescent : baseEnd_5005092 < baseStart_5005092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005112 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 6]
def baseStart_5005112 : Nat := 118140960795 + 5005112 * 2 ^ 59
def prefixEnd_5005112 : Nat := 4983230072969 + 3 ^ 40 * 5005112 * 2
def baseEnd_5005112 : Nat := 285558687287369634442435

theorem tailTrace_5005112 : CollatzResearch.WordTrace tailWord_5005112 prefixEnd_5005112 285558687287369634442435 := by
  unfold tailWord_5005112
  simp only [CollatzResearch.WordTrace]
  refine ⟨91275715921670751960100795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121700954562227669280134393 91275715921670751960100795)
  ·
    refine ⟨136913573882506127940151193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91275715921670751960100795 136913573882506127940151193)
    ·
      refine ⟨102685180411879595955113395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136913573882506127940151193 102685180411879595955113395)
      ·
        refine ⟨154027770617819393932670093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102685180411879595955113395 154027770617819393932670093)
        ·
          refine ⟨57760413981682272724751285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154027770617819393932670093 57760413981682272724751285)
          ·
            refine ⟨5415038810782713067945433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57760413981682272724751285 5415038810782713067945433)
            ·
              refine ⟨4061279108087034800959075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5415038810782713067945433 4061279108087034800959075)
              ·
                refine ⟨6091918662130552201438613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4061279108087034800959075 6091918662130552201438613)
                ·
                  refine ⟨285558687287369634442435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6091918662130552201438613 285558687287369634442435)
                  ·
                    rfl

theorem cell23_5005112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 6].length) (baseStart_5005112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005112 prefixEnd_5005112 := by exact prefixLift 5005112
  have htrace : WordTrace (prefixWord ++ tailWord_5005112) baseStart_5005112 baseEnd_5005112 := by
    simpa [prefixWord, tailWord_5005112, baseEnd_5005112] using wordTrace_append hprefix tailTrace_5005112
  have hstable : (prefixWord ++ tailWord_5005112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005112).length < 2 ^ (prefixWord ++ tailWord_5005112).sum := by decide
  have hdescent : baseEnd_5005112 < baseStart_5005112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005126 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5005126 : Nat := 118140960795 + 5005126 * 2 ^ 59
def prefixEnd_5005126 : Nat := 4983230072969 + 3 ^ 40 * 5005126 * 2
def baseEnd_5005126 : Nat := 2570035374315489655206851

theorem tailTrace_5005126 : CollatzResearch.WordTrace tailWord_5005126 prefixEnd_5005126 2570035374315489655206851 := by
  unfold tailWord_5005126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5704748202040337009725351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121701294976860522874140821 5704748202040337009725351)
  ·
    refine ⟨8557122303060505514588027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5704748202040337009725351 8557122303060505514588027)
    ·
      refine ⟨12835683454590758271882041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8557122303060505514588027 12835683454590758271882041)
      ·
        refine ⟨9626762590943068703911531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12835683454590758271882041 9626762590943068703911531)
        ·
          refine ⟨14440143886414603055867297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9626762590943068703911531 14440143886414603055867297)
          ·
            refine ⟨10830107914810952291900473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14440143886414603055867297 10830107914810952291900473)
            ·
              refine ⟨8122580936108214218925355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10830107914810952291900473 8122580936108214218925355)
              ·
                refine ⟨12183871404162321328388033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8122580936108214218925355 12183871404162321328388033)
                ·
                  refine ⟨9137903553121740996291025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12183871404162321328388033 9137903553121740996291025)
                  ·
                    refine ⟨6853427664841305747218269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9137903553121740996291025 6853427664841305747218269)
                    ·
                      refine ⟨2570035374315489655206851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6853427664841305747218269 2570035374315489655206851)
                      ·
                        rfl

theorem cell23_5005126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5005126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005126 prefixEnd_5005126 := by exact prefixLift 5005126
  have htrace : WordTrace (prefixWord ++ tailWord_5005126) baseStart_5005126 baseEnd_5005126 := by
    simpa [prefixWord, tailWord_5005126, baseEnd_5005126] using wordTrace_append hprefix tailTrace_5005126
  have hstable : (prefixWord ++ tailWord_5005126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005126).length < 2 ^ (prefixWord ++ tailWord_5005126).sum := by decide
  have hdescent : baseEnd_5005126 < baseStart_5005126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005156 : List Nat := [2, 3, 1, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_5005156 : Nat := 118140960795 + 5005156 * 2 ^ 59
def prefixEnd_5005156 : Nat := 4983230072969 + 3 ^ 40 * 5005156 * 2
def baseEnd_5005156 : Nat := 2570050778735124537831713

theorem tailTrace_5005156 : CollatzResearch.WordTrace tailWord_5005156 prefixEnd_5005156 2570050778735124537831713 := by
  unfold tailWord_5005156
  simp only [CollatzResearch.WordTrace]
  refine ⟨91276518327591049717401661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121702024436788066289868881 91276518327591049717401661)
  ·
    refine ⟨34228694372846643644025623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91276518327591049717401661 34228694372846643644025623)
    ·
      refine ⟨51343041559269965466038435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34228694372846643644025623 51343041559269965466038435)
      ·
        refine ⟨77014562338904948199057653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51343041559269965466038435 77014562338904948199057653)
        ·
          refine ⟨7220115219272338893661655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77014562338904948199057653 7220115219272338893661655)
          ·
            refine ⟨10830172828908508340492483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7220115219272338893661655 10830172828908508340492483)
            ·
              refine ⟨16245259243362762510738725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10830172828908508340492483 16245259243362762510738725)
              ·
                refine ⟨3045986108130517970763511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16245259243362762510738725 3045986108130517970763511)
                ·
                  refine ⟨4568979162195776956145267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045986108130517970763511 4568979162195776956145267)
                  ·
                    refine ⟨6853468743293665434217901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568979162195776956145267 6853468743293665434217901)
                    ·
                      refine ⟨2570050778735124537831713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6853468743293665434217901 2570050778735124537831713)
                      ·
                        rfl

theorem cell23_5005156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_5005156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005156 prefixEnd_5005156 := by exact prefixLift 5005156
  have htrace : WordTrace (prefixWord ++ tailWord_5005156) baseStart_5005156 baseEnd_5005156 := by
    simpa [prefixWord, tailWord_5005156, baseEnd_5005156] using wordTrace_append hprefix tailTrace_5005156
  have hstable : (prefixWord ++ tailWord_5005156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005156).length < 2 ^ (prefixWord ++ tailWord_5005156).sum := by decide
  have hdescent : baseEnd_5005156 < baseStart_5005156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005165 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5005165 : Nat := 118140960795 + 5005165 * 2 ^ 59
def prefixEnd_5005165 : Nat := 4983230072969 + 3 ^ 40 * 5005165 * 2
def baseEnd_5005165 : Nat := 2570055400061015002619171

theorem tailTrace_5005165 : CollatzResearch.WordTrace tailWord_5005165 prefixEnd_5005165 2570055400061015002619171 := by
  unfold tailWord_5005165
  simp only [CollatzResearch.WordTrace]
  refine ⟨182553364912149493971880949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121702243274766329314587299 182553364912149493971880949)
  ·
    refine ⟨17114377960514015059863839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182553364912149493971880949 17114377960514015059863839)
    ·
      refine ⟨25671566940771022589795759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17114377960514015059863839 25671566940771022589795759)
      ·
        refine ⟨38507350411156533884693639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25671566940771022589795759 38507350411156533884693639)
        ·
          refine ⟨57761025616734800827040459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38507350411156533884693639 57761025616734800827040459)
          ·
            refine ⟨86641538425102201240560689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57761025616734800827040459 86641538425102201240560689)
            ·
              refine ⟨64981153818826650930420517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86641538425102201240560689 64981153818826650930420517)
              ·
                refine ⟨12183966341029997049453847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64981153818826650930420517 12183966341029997049453847)
                ·
                  refine ⟨18275949511544995574180771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12183966341029997049453847 18275949511544995574180771)
                  ·
                    refine ⟨27413924267317493361271157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18275949511544995574180771 27413924267317493361271157)
                    ·
                      refine ⟨2570055400061015002619171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27413924267317493361271157 2570055400061015002619171)
                      ·
                        rfl

theorem cell23_5005165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5005165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005165 prefixEnd_5005165 := by exact prefixLift 5005165
  have htrace : WordTrace (prefixWord ++ tailWord_5005165) baseStart_5005165 baseEnd_5005165 := by
    simpa [prefixWord, tailWord_5005165, baseEnd_5005165] using wordTrace_append hprefix tailTrace_5005165
  have hstable : (prefixWord ++ tailWord_5005165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005165).length < 2 ^ (prefixWord ++ tailWord_5005165).sum := by decide
  have hdescent : baseEnd_5005165 < baseStart_5005165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005236 : List Nat := [2, 5, 2, 1, 2, 2, 2, 7]
def baseStart_5005236 : Nat := 118140960795 + 5005236 * 2 ^ 59
def prefixEnd_5005236 : Nat := 4983230072969 + 3 ^ 40 * 5005236 * 2
def baseEnd_5005236 : Nat := 95188587303240156475235

theorem tailTrace_5005236 : CollatzResearch.WordTrace tailWord_5005236 prefixEnd_5005236 95188587303240156475235 := by
  unfold tailWord_5005236
  simp only [CollatzResearch.WordTrace]
  refine ⟨91277977247446136548857781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121703969663261515398477041 91277977247446136548857781)
  ·
    refine ⟨8557310366948075301455417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91277977247446136548857781 8557310366948075301455417)
    ·
      refine ⟨6417982775211056476091563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8557310366948075301455417 6417982775211056476091563)
      ·
        refine ⟨9626974162816584714137345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417982775211056476091563 9626974162816584714137345)
        ·
          refine ⟨7220230622112438535603009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9626974162816584714137345 7220230622112438535603009)
          ·
            refine ⟨5415172966584328901702257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7220230622112438535603009 5415172966584328901702257)
            ·
              refine ⟨4061379724938246676276693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5415172966584328901702257 4061379724938246676276693)
              ·
                refine ⟨95188587303240156475235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4061379724938246676276693 95188587303240156475235)
                ·
                  rfl

theorem cell23_5005236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 7].length) (baseStart_5005236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005236 prefixEnd_5005236 := by exact prefixLift 5005236
  have htrace : WordTrace (prefixWord ++ tailWord_5005236) baseStart_5005236 baseEnd_5005236 := by
    simpa [prefixWord, tailWord_5005236, baseEnd_5005236] using wordTrace_append hprefix tailTrace_5005236
  have hstable : (prefixWord ++ tailWord_5005236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005236).length < 2 ^ (prefixWord ++ tailWord_5005236).sum := by decide
  have hdescent : baseEnd_5005236 < baseStart_5005236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005255 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_5005255 : Nat := 118140960795 + 5005255 * 2 ^ 59
def prefixEnd_5005255 : Nat := 4983230072969 + 3 ^ 40 * 5005255 * 2
def baseEnd_5005255 : Nat := 2570101613319919650493757

theorem tailTrace_5005255 : CollatzResearch.WordTrace tailWord_5005255 prefixEnd_5005255 2570101613319919650493757 := by
  unfold tailWord_5005255
  simp only [CollatzResearch.WordTrace]
  refine ⟨182556647481823439342657219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121704431654548959561771479 182556647481823439342657219)
  ·
    refine ⟨273834971222735159013985829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182556647481823439342657219 273834971222735159013985829)
    ·
      refine ⟨51344057104262842315122343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273834971222735159013985829 51344057104262842315122343)
      ·
        refine ⟨77016085656394263472683515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51344057104262842315122343 77016085656394263472683515)
        ·
          refine ⟨115524128484591395209025273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77016085656394263472683515 115524128484591395209025273)
          ·
            refine ⟨86643096363443546406768955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115524128484591395209025273 86643096363443546406768955)
            ·
              refine ⟨129964644545165319610153433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86643096363443546406768955 129964644545165319610153433)
              ·
                refine ⟨97473483408873989707615075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129964644545165319610153433 97473483408873989707615075)
                ·
                  refine ⟨146210225113310984561422613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97473483408873989707615075 146210225113310984561422613)
                  ·
                    refine ⟨6853604302186452401316685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 146210225113310984561422613 6853604302186452401316685)
                    ·
                      refine ⟨2570101613319919650493757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6853604302186452401316685 2570101613319919650493757)
                      ·
                        rfl

theorem cell23_5005255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_5005255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005255 prefixEnd_5005255 := by exact prefixLift 5005255
  have htrace : WordTrace (prefixWord ++ tailWord_5005255) baseStart_5005255 baseEnd_5005255 := by
    simpa [prefixWord, tailWord_5005255, baseEnd_5005255] using wordTrace_append hprefix tailTrace_5005255
  have hstable : (prefixWord ++ tailWord_5005255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005255).length < 2 ^ (prefixWord ++ tailWord_5005255).sum := by decide
  have hdescent : baseEnd_5005255 < baseStart_5005255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005265 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_5005265 : Nat := 118140960795 + 5005265 * 2 ^ 59
def prefixEnd_5005265 : Nat := 4983230072969 + 3 ^ 40 * 5005265 * 2
def baseEnd_5005265 : Nat := 2570106748126464611368711

theorem tailTrace_5005265 : CollatzResearch.WordTrace tailWord_5005265 prefixEnd_5005265 2570106748126464611368711 := by
  unfold tailWord_5005265
  simp only [CollatzResearch.WordTrace]
  refine ⟨182557012211787211050521249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121704674807858140700347499 182557012211787211050521249)
  ·
    refine ⟨136917759158840408287890937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182557012211787211050521249 136917759158840408287890937)
    ·
      refine ⟨102688319369130306215918203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136917759158840408287890937 102688319369130306215918203)
      ·
        refine ⟨154032479053695459323877305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102688319369130306215918203 154032479053695459323877305)
        ·
          refine ⟨115524359290271594492907979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154032479053695459323877305 115524359290271594492907979)
          ·
            refine ⟨173286538935407391739361969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115524359290271594492907979 173286538935407391739361969)
            ·
              refine ⟨129964904201555543804521477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173286538935407391739361969 129964904201555543804521477)
              ·
                refine ⟨24368419537791664463347777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129964904201555543804521477 24368419537791664463347777)
                ·
                  refine ⟨18276314653343748347510833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24368419537791664463347777 18276314653343748347510833)
                  ·
                    refine ⟨13707235990007811260633125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18276314653343748347510833 13707235990007811260633125)
                    ·
                      refine ⟨2570106748126464611368711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13707235990007811260633125 2570106748126464611368711)
                      ·
                        rfl

theorem cell23_5005265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_5005265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005265 prefixEnd_5005265 := by exact prefixLift 5005265
  have htrace : WordTrace (prefixWord ++ tailWord_5005265) baseStart_5005265 baseEnd_5005265 := by
    simpa [prefixWord, tailWord_5005265, baseEnd_5005265] using wordTrace_append hprefix tailTrace_5005265
  have hstable : (prefixWord ++ tailWord_5005265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005265).length < 2 ^ (prefixWord ++ tailWord_5005265).sum := by decide
  have hdescent : baseEnd_5005265 < baseStart_5005265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005355 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 4]
def baseStart_5005355 : Nat := 118140960795 + 5005355 * 2 ^ 59
def prefixEnd_5005355 : Nat := 4983230072969 + 3 ^ 40 * 5005355 * 2
def baseEnd_5005355 : Nat := 2570152961385369259243297

theorem tailTrace_5005355 : CollatzResearch.WordTrace tailWord_5005355 prefixEnd_5005355 2570152961385369259243297 := by
  unfold tailWord_5005355
  simp only [CollatzResearch.WordTrace]
  refine ⟨182560294781461156421297519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121706863187640770947531679 182560294781461156421297519)
  ·
    refine ⟨273840442172191734631946279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182560294781461156421297519 273840442172191734631946279)
    ·
      refine ⟨410760663258287601947919419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273840442172191734631946279 410760663258287601947919419)
      ·
        refine ⟨616140994887431402921879129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410760663258287601947919419 616140994887431402921879129)
        ·
          refine ⟨462105746165573552191409347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 616140994887431402921879129 462105746165573552191409347)
          ·
            refine ⟨693158619248360328287114021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462105746165573552191409347 693158619248360328287114021)
            ·
              refine ⟨129967241109067561553833879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 693158619248360328287114021 129967241109067561553833879)
              ·
                refine ⟨194950861663601342330750819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129967241109067561553833879 194950861663601342330750819)
                ·
                  refine ⟨292426292495402013496126229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194950861663601342330750819 292426292495402013496126229)
                  ·
                    refine ⟨13707482460721969382630917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 292426292495402013496126229 13707482460721969382630917)
                    ·
                      refine ⟨2570152961385369259243297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13707482460721969382630917 2570152961385369259243297)
                      ·
                        rfl

theorem cell23_5005355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 4].length) (baseStart_5005355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005355 prefixEnd_5005355 := by exact prefixLift 5005355
  have htrace : WordTrace (prefixWord ++ tailWord_5005355) baseStart_5005355 baseEnd_5005355 := by
    simpa [prefixWord, tailWord_5005355, baseEnd_5005355] using wordTrace_append hprefix tailTrace_5005355
  have hstable : (prefixWord ++ tailWord_5005355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005355).length < 2 ^ (prefixWord ++ tailWord_5005355).sum := by decide
  have hdescent : baseEnd_5005355 < baseStart_5005355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005385 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_5005385 : Nat := 118140960795 + 5005385 * 2 ^ 59
def prefixEnd_5005385 : Nat := 4983230072969 + 3 ^ 40 * 5005385 * 2
def baseEnd_5005385 : Nat := 2570168365805004141868159

theorem tailTrace_5005385 : CollatzResearch.WordTrace tailWord_5005385 prefixEnd_5005385 2570168365805004141868159 := by
  unfold tailWord_5005385
  simp only [CollatzResearch.WordTrace]
  refine ⟨182561388971352471544889609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121707592647568314363259739 182561388971352471544889609)
  ·
    refine ⟨136921041728514353658667207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182561388971352471544889609 136921041728514353658667207)
    ·
      refine ⟨205381562592771530488000811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136921041728514353658667207 205381562592771530488000811)
      ·
        refine ⟨308072343889157295732001217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205381562592771530488000811 308072343889157295732001217)
        ·
          refine ⟨231054257916867971799000913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308072343889157295732001217 231054257916867971799000913)
          ·
            refine ⟨173290693437650978849250685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231054257916867971799000913 173290693437650978849250685)
            ·
              refine ⟨64984010039119117068469007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173290693437650978849250685 64984010039119117068469007)
              ·
                refine ⟨97476015058678675602703511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64984010039119117068469007 97476015058678675602703511)
                ·
                  refine ⟨146214022588018013404055267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97476015058678675602703511 146214022588018013404055267)
                  ·
                    refine ⟨219321033882027020106082901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146214022588018013404055267 219321033882027020106082901)
                    ·
                      refine ⟨2570168365805004141868159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 219321033882027020106082901 2570168365805004141868159)
                      ·
                        rfl

theorem cell23_5005385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_5005385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005385 prefixEnd_5005385 := by exact prefixLift 5005385
  have htrace : WordTrace (prefixWord ++ tailWord_5005385) baseStart_5005385 baseEnd_5005385 := by
    simpa [prefixWord, tailWord_5005385, baseEnd_5005385] using wordTrace_append hprefix tailTrace_5005385
  have hstable : (prefixWord ++ tailWord_5005385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005385).length < 2 ^ (prefixWord ++ tailWord_5005385).sum := by decide
  have hdescent : baseEnd_5005385 < baseStart_5005385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005412 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_5005412 : Nat := 118140960795 + 5005412 * 2 ^ 59
def prefixEnd_5005412 : Nat := 4983230072969 + 3 ^ 40 * 5005412 * 2
def baseEnd_5005412 : Nat := 856727409927558512076845

theorem tailTrace_5005412 : CollatzResearch.WordTrace tailWord_5005412 prefixEnd_5005412 856727409927558512076845 := by
  unfold tailWord_5005412
  simp only [CollatzResearch.WordTrace]
  refine ⟨91281186871127327578061245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121708249161503103437414993 91281186871127327578061245)
  ·
    refine ⟨34230445076672747841772967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91281186871127327578061245 34230445076672747841772967)
    ·
      refine ⟨51345667615009121762659451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34230445076672747841772967 51345667615009121762659451)
      ·
        refine ⟨77018501422513682643989177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51345667615009121762659451 77018501422513682643989177)
        ·
          refine ⟨57763876066885261982991883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77018501422513682643989177 57763876066885261982991883)
          ·
            refine ⟨86645814100327892974487825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57763876066885261982991883 86645814100327892974487825)
            ·
              refine ⟨64984360575245919730865869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86645814100327892974487825 64984360575245919730865869)
              ·
                refine ⟨24369135215717219899074701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64984360575245919730865869 24369135215717219899074701)
                ·
                  refine ⟨9138425705893957462153013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24369135215717219899074701 9138425705893957462153013)
                  ·
                    refine ⟨856727409927558512076845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9138425705893957462153013 856727409927558512076845)
                    ·
                      rfl

theorem cell23_5005412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_5005412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005412 prefixEnd_5005412 := by exact prefixLift 5005412
  have htrace : WordTrace (prefixWord ++ tailWord_5005412) baseStart_5005412 baseEnd_5005412 := by
    simpa [prefixWord, tailWord_5005412, baseEnd_5005412] using wordTrace_append hprefix tailTrace_5005412
  have hstable : (prefixWord ++ tailWord_5005412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005412).length < 2 ^ (prefixWord ++ tailWord_5005412).sum := by decide
  have hdescent : baseEnd_5005412 < baseStart_5005412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005432 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_5005432 : Nat := 118140960795 + 5005432 * 2 ^ 59
def prefixEnd_5005432 : Nat := 4983230072969 + 3 ^ 40 * 5005432 * 2
def baseEnd_5005432 : Nat := 2570192499395765457980443

theorem tailTrace_5005432 : CollatzResearch.WordTrace tailWord_5005432 prefixEnd_5005432 2570192499395765457980443 := by
  unfold tailWord_5005432
  simp only [CollatzResearch.WordTrace]
  refine ⟨91281551601091099285925275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121708735468121465714567033 91281551601091099285925275)
  ·
    refine ⟨136922327401636648928887913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91281551601091099285925275 136922327401636648928887913)
    ·
      refine ⟨102691745551227486696665935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136922327401636648928887913 102691745551227486696665935)
      ·
        refine ⟨154037618326841230044998903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102691745551227486696665935 154037618326841230044998903)
        ·
          refine ⟨231056427490261845067498355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154037618326841230044998903 231056427490261845067498355)
          ·
            refine ⟨346584641235392767601247533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231056427490261845067498355 346584641235392767601247533)
            ·
              refine ⟨129969240463272287850467825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346584641235392767601247533 129969240463272287850467825)
              ·
                refine ⟨97476930347454215887850869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129969240463272287850467825 97476930347454215887850869)
                ·
                  refine ⟨9138462220073832739486019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97476930347454215887850869 9138462220073832739486019)
                  ·
                    refine ⟨13707693330110749109229029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9138462220073832739486019 13707693330110749109229029)
                    ·
                      refine ⟨2570192499395765457980443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13707693330110749109229029 2570192499395765457980443)
                      ·
                        rfl

theorem cell23_5005432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_5005432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005432 prefixEnd_5005432 := by exact prefixLift 5005432
  have htrace : WordTrace (prefixWord ++ tailWord_5005432) baseStart_5005432 baseEnd_5005432 := by
    simpa [prefixWord, tailWord_5005432, baseEnd_5005432] using wordTrace_append hprefix tailTrace_5005432
  have hstable : (prefixWord ++ tailWord_5005432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005432).length < 2 ^ (prefixWord ++ tailWord_5005432).sum := by decide
  have hdescent : baseEnd_5005432 < baseStart_5005432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005436 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_5005436 : Nat := 118140960795 + 5005436 * 2 ^ 59
def prefixEnd_5005436 : Nat := 4983230072969 + 3 ^ 40 * 5005436 * 2
def baseEnd_5005436 : Nat := 2570194553318383442330425

theorem tailTrace_5005436 : CollatzResearch.WordTrace tailWord_5005436 prefixEnd_5005436 2570194553318383442330425 := by
  unfold tailWord_5005436
  simp only [CollatzResearch.WordTrace]
  refine ⟨91281624547083853627498081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121708832729445138169997441 91281624547083853627498081)
  ·
    refine ⟨68461218410312890220623561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91281624547083853627498081 68461218410312890220623561)
    ·
      refine ⟨51345913807734667665467671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68461218410312890220623561 51345913807734667665467671)
      ·
        refine ⟨77018870711602001498201507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51345913807734667665467671 77018870711602001498201507)
        ·
          refine ⟨115528306067403002247302261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77018870711602001498201507 115528306067403002247302261)
          ·
            refine ⟨10830778693819031460684587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115528306067403002247302261 10830778693819031460684587)
            ·
              refine ⟨16246168040728547191026881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10830778693819031460684587 16246168040728547191026881)
              ·
                refine ⟨12184626030546410393270161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16246168040728547191026881 12184626030546410393270161)
                ·
                  refine ⟨9138469522909807794952621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12184626030546410393270161 9138469522909807794952621)
                  ·
                    refine ⟨3426926071091177923107233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9138469522909807794952621 3426926071091177923107233)
                    ·
                      refine ⟨2570194553318383442330425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426926071091177923107233 2570194553318383442330425)
                      ·
                        rfl

theorem cell23_5005436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_5005436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005436 prefixEnd_5005436 := by exact prefixLift 5005436
  have htrace : WordTrace (prefixWord ++ tailWord_5005436) baseStart_5005436 baseEnd_5005436 := by
    simpa [prefixWord, tailWord_5005436, baseEnd_5005436] using wordTrace_append hprefix tailTrace_5005436
  have hstable : (prefixWord ++ tailWord_5005436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005436).length < 2 ^ (prefixWord ++ tailWord_5005436).sum := by decide
  have hdescent : baseEnd_5005436 < baseStart_5005436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005452 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_5005452 : Nat := 118140960795 + 5005452 * 2 ^ 59
def prefixEnd_5005452 : Nat := 4983230072969 + 3 ^ 40 * 5005452 * 2
def baseEnd_5005452 : Nat := 2570202769008855379730351

theorem tailTrace_5005452 : CollatzResearch.WordTrace tailWord_5005452 prefixEnd_5005452 2570202769008855379730351 := by
  unfold tailWord_5005452
  simp only [CollatzResearch.WordTrace]
  refine ⟨91281916331054870993789305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121709221774739827991719073 91281916331054870993789305)
  ·
    refine ⟨68461437248291153245341979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91281916331054870993789305 68461437248291153245341979)
    ·
      refine ⟨102692155872436729868012969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68461437248291153245341979 102692155872436729868012969)
      ·
        refine ⟨77019116904327547401009727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102692155872436729868012969 77019116904327547401009727)
        ·
          refine ⟨115528675356491321101514591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77019116904327547401009727 115528675356491321101514591)
          ·
            refine ⟨173293013034736981652271887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115528675356491321101514591 173293013034736981652271887)
            ·
              refine ⟨259939519552105472478407831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173293013034736981652271887 259939519552105472478407831)
              ·
                refine ⟨389909279328158208717611747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259939519552105472478407831 389909279328158208717611747)
                ·
                  refine ⟨584863918992237313076417621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389909279328158208717611747 584863918992237313076417621)
                  ·
                    refine ⟨6853874050690281012614269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 584863918992237313076417621 6853874050690281012614269)
                    ·
                      refine ⟨2570202769008855379730351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6853874050690281012614269 2570202769008855379730351)
                      ·
                        rfl

theorem cell23_5005452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_5005452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005452 prefixEnd_5005452 := by exact prefixLift 5005452
  have htrace : WordTrace (prefixWord ++ tailWord_5005452) baseStart_5005452 baseEnd_5005452 := by
    simpa [prefixWord, tailWord_5005452, baseEnd_5005452] using wordTrace_append hprefix tailTrace_5005452
  have hstable : (prefixWord ++ tailWord_5005452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005452).length < 2 ^ (prefixWord ++ tailWord_5005452).sum := by decide
  have hdescent : baseEnd_5005452 < baseStart_5005452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005463 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 1, 5]
def baseStart_5005463 : Nat := 118140960795 + 5005463 * 2 ^ 59
def prefixEnd_5005463 : Nat := 4983230072969 + 3 ^ 40 * 5005463 * 2
def baseEnd_5005463 : Nat := 856736139098684945564267

theorem tailTrace_5005463 : CollatzResearch.WordTrace tailWord_5005463 prefixEnd_5005463 856736139098684945564267 := by
  unfold tailWord_5005463
  simp only [CollatzResearch.WordTrace]
  refine ⟨182564233865069890866229043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121709489243379927244152695 182564233865069890866229043)
  ·
    refine ⟨273846350797604836299343565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182564233865069890866229043 273846350797604836299343565)
    ·
      refine ⟨102692381549101813612253837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273846350797604836299343565 102692381549101813612253837)
      ·
        refine ⟨38509643080913180104595189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102692381549101813612253837 38509643080913180104595189)
        ·
          refine ⟨3610279038835610634805799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38509643080913180104595189 3610279038835610634805799)
          ·
            refine ⟨5415418558253415952208699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610279038835610634805799 5415418558253415952208699)
            ·
              refine ⟨8123127837380123928313049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5415418558253415952208699 8123127837380123928313049)
              ·
                refine ⟨6092345878035092946234787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8123127837380123928313049 6092345878035092946234787)
                ·
                  refine ⟨9138518817052639419352181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6092345878035092946234787 9138518817052639419352181)
                  ·
                    refine ⟨856736139098684945564267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9138518817052639419352181 856736139098684945564267)
                    ·
                      rfl

theorem cell23_5005463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_5005463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005463 prefixEnd_5005463 := by exact prefixLift 5005463
  have htrace : WordTrace (prefixWord ++ tailWord_5005463) baseStart_5005463 baseEnd_5005463 := by
    simpa [prefixWord, tailWord_5005463, baseEnd_5005463] using wordTrace_append hprefix tailTrace_5005463
  have hstable : (prefixWord ++ tailWord_5005463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005463).length < 2 ^ (prefixWord ++ tailWord_5005463).sum := by decide
  have hdescent : baseEnd_5005463 < baseStart_5005463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005466 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5005466 : Nat := 118140960795 + 5005466 * 2 ^ 59
def prefixEnd_5005466 : Nat := 4983230072969 + 3 ^ 40 * 5005466 * 2
def baseEnd_5005466 : Nat := 2570209957738018324955287

theorem tailTrace_5005466 : CollatzResearch.WordTrace tailWord_5005466 prefixEnd_5005466 2570209957738018324955287 := by
  unfold tailWord_5005466
  simp only [CollatzResearch.WordTrace]
  refine ⟨45641085821014755594647063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121709562189372681585725501 45641085821014755594647063)
  ·
    refine ⟨68461628731522133391970595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45641085821014755594647063 68461628731522133391970595)
    ·
      refine ⟨102692443097283200087955893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68461628731522133391970595 102692443097283200087955893)
      ·
        refine ⟨9627416540370300008245865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102692443097283200087955893 9627416540370300008245865)
        ·
          refine ⟨7220562405277725006184399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9627416540370300008245865 7220562405277725006184399)
          ·
            refine ⟨10830843607916587509276599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7220562405277725006184399 10830843607916587509276599)
            ·
              refine ⟨16246265411874881263914899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10830843607916587509276599 16246265411874881263914899)
              ·
                refine ⟨24369398117812321895872349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16246265411874881263914899 24369398117812321895872349)
                ·
                  refine ⟨9138524294179620710952131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24369398117812321895872349 9138524294179620710952131)
                  ·
                    refine ⟨13707786441269431066428197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9138524294179620710952131 13707786441269431066428197)
                    ·
                      refine ⟨2570209957738018324955287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13707786441269431066428197 2570209957738018324955287)
                      ·
                        rfl

theorem cell23_5005466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5005466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005466 prefixEnd_5005466 := by exact prefixLift 5005466
  have htrace : WordTrace (prefixWord ++ tailWord_5005466) baseStart_5005466 baseEnd_5005466 := by
    simpa [prefixWord, tailWord_5005466, baseEnd_5005466] using wordTrace_append hprefix tailTrace_5005466
  have hstable : (prefixWord ++ tailWord_5005466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005466).length < 2 ^ (prefixWord ++ tailWord_5005466).sum := by decide
  have hdescent : baseEnd_5005466 < baseStart_5005466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005470 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_5005470 : Nat := 118140960795 + 5005470 * 2 ^ 59
def prefixEnd_5005470 : Nat := 4983230072969 + 3 ^ 40 * 5005470 * 2
def baseEnd_5005470 : Nat := 2570212011660636309305269

theorem tailTrace_5005470 : CollatzResearch.WordTrace tailWord_5005470 prefixEnd_5005470 2570212011660636309305269 := by
  unfold tailWord_5005470
  simp only [CollatzResearch.WordTrace]
  refine ⟨22820561147005566382716733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121709659450696354041155909 22820561147005566382716733)
  ·
    refine ⟨8557710430127087393518775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22820561147005566382716733 8557710430127087393518775)
    ·
      refine ⟨12836565645190631090278163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8557710430127087393518775 12836565645190631090278163)
      ·
        refine ⟨19254848467785946635417245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12836565645190631090278163 19254848467785946635417245)
        ·
          refine ⟨7220568175419729988281467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19254848467785946635417245 7220568175419729988281467)
          ·
            refine ⟨10830852263129594982422201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7220568175419729988281467 10830852263129594982422201)
            ·
              refine ⟨8123139197347196236816651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10830852263129594982422201 8123139197347196236816651)
              ·
                refine ⟨12184708796020794355224977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8123139197347196236816651 12184708796020794355224977)
                ·
                  refine ⟨9138531597015595766418733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12184708796020794355224977 9138531597015595766418733)
                  ·
                    refine ⟨3426949348880848412407025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9138531597015595766418733 3426949348880848412407025)
                    ·
                      refine ⟨2570212011660636309305269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3426949348880848412407025 2570212011660636309305269)
                      ·
                        rfl

theorem cell23_5005470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_5005470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005470 prefixEnd_5005470 := by exact prefixLift 5005470
  have htrace : WordTrace (prefixWord ++ tailWord_5005470) baseStart_5005470 baseEnd_5005470 := by
    simpa [prefixWord, tailWord_5005470, baseEnd_5005470] using wordTrace_append hprefix tailTrace_5005470
  have hstable : (prefixWord ++ tailWord_5005470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005470).length < 2 ^ (prefixWord ++ tailWord_5005470).sum := by decide
  have hdescent : baseEnd_5005470 < baseStart_5005470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005472 : List Nat := [2, 1, 1, 4, 2, 2, 2, 9]
def baseStart_5005472 : Nat := 118140960795 + 5005472 * 2 ^ 59
def prefixEnd_5005472 : Nat := 4983230072969 + 3 ^ 40 * 5005472 * 2
def baseEnd_5005472 : Nat := 95193075504516492647417

theorem tailTrace_5005472 : CollatzResearch.WordTrace tailWord_5005472 prefixEnd_5005472 95193075504516492647417 := by
  unfold tailWord_5005472
  simp only [CollatzResearch.WordTrace]
  refine ⟨91282281061018642701653335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121709708081358190268871113 91282281061018642701653335)
  ·
    refine ⟨136923421591527964052480003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91282281061018642701653335 136923421591527964052480003)
    ·
      refine ⟨205385132387291946078720005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136923421591527964052480003 205385132387291946078720005)
      ·
        refine ⟨38509712322617239889760001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205385132387291946078720005 38509712322617239889760001)
        ·
          refine ⟨28882284241962929917320001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38509712322617239889760001 28882284241962929917320001)
          ·
            refine ⟨21661713181472197437990001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28882284241962929917320001 21661713181472197437990001)
            ·
              refine ⟨16246284886104148078492501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21661713181472197437990001 16246284886104148078492501)
              ·
                refine ⟨95193075504516492647417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16246284886104148078492501 95193075504516492647417)
                ·
                  rfl

theorem cell23_5005472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 9].length) (baseStart_5005472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005472 prefixEnd_5005472 := by exact prefixLift 5005472
  have htrace : WordTrace (prefixWord ++ tailWord_5005472) baseStart_5005472 baseEnd_5005472 := by
    simpa [prefixWord, tailWord_5005472, baseEnd_5005472] using wordTrace_append hprefix tailTrace_5005472
  have hstable : (prefixWord ++ tailWord_5005472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005472).length < 2 ^ (prefixWord ++ tailWord_5005472).sum := by decide
  have hdescent : baseEnd_5005472 < baseStart_5005472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005489 : List Nat := [1, 2, 2, 5, 3, 10]
def baseStart_5005489 : Nat := 118140960795 + 5005489 * 2 ^ 59
def prefixEnd_5005489 : Nat := 4983230072969 + 3 ^ 40 * 5005489 * 2
def baseEnd_5005489 : Nat := 10577044311905644999867

theorem tailTrace_5005489 : CollatzResearch.WordTrace tailWord_5005489 prefixEnd_5005489 10577044311905644999867 := by
  unfold tailWord_5005489
  simp only [CollatzResearch.WordTrace]
  refine ⟨182565182162975697306675521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121710121441983798204450347 182565182162975697306675521)
  ·
    refine ⟨136923886622231772980006641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182565182162975697306675521 136923886622231772980006641)
    ·
      refine ⟨102692914966673829735004981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136923886622231772980006641 102692914966673829735004981)
      ·
        refine ⟨9627460778125671537656717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102692914966673829735004981 9627460778125671537656717)
        ·
          refine ⟨3610297791797126826621269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9627460778125671537656717 3610297791797126826621269)
          ·
            refine ⟨10577044311905644999867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3610297791797126826621269 10577044311905644999867)
            ·
              rfl

theorem cell23_5005489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 10].length) (baseStart_5005489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005489 prefixEnd_5005489 := by exact prefixLift 5005489
  have htrace : WordTrace (prefixWord ++ tailWord_5005489) baseStart_5005489 baseEnd_5005489 := by
    simpa [prefixWord, tailWord_5005489, baseEnd_5005489] using wordTrace_append hprefix tailTrace_5005489
  have hstable : (prefixWord ++ tailWord_5005489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005489).length < 2 ^ (prefixWord ++ tailWord_5005489).sum := by decide
  have hdescent : baseEnd_5005489 < baseStart_5005489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005512 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_5005512 : Nat := 118140960795 + 5005512 * 2 ^ 59
def prefixEnd_5005512 : Nat := 4983230072969 + 3 ^ 40 * 5005512 * 2
def baseEnd_5005512 : Nat := 2570233577848125144980075

theorem tailTrace_5005512 : CollatzResearch.WordTrace tailWord_5005512 prefixEnd_5005512 2570233577848125144980075 := by
  unfold tailWord_5005512
  simp only [CollatzResearch.WordTrace]
  refine ⟨91283010520946186117381395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121710680694594914823175193 91283010520946186117381395)
  ·
    refine ⟨136924515781419279176072093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91283010520946186117381395 136924515781419279176072093)
    ·
      refine ⟨51346693418032229691027035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136924515781419279176072093 51346693418032229691027035)
      ·
        refine ⟨77020040127048344536540553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51346693418032229691027035 77020040127048344536540553)
        ·
          refine ⟨57765030095286258402405415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77020040127048344536540553 57765030095286258402405415)
          ·
            refine ⟨86647545142929387603608123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57765030095286258402405415 86647545142929387603608123)
            ·
              refine ⟨129971317714394081405412185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86647545142929387603608123 129971317714394081405412185)
              ·
                refine ⟨97478488285795561054059139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129971317714394081405412185 97478488285795561054059139)
                ·
                  refine ⟨146217732428693341581088709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97478488285795561054059139 146217732428693341581088709)
                  ·
                    refine ⟨27415824830380001546454133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146217732428693341581088709 27415824830380001546454133)
                    ·
                      refine ⟨2570233577848125144980075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27415824830380001546454133 2570233577848125144980075)
                      ·
                        rfl

theorem cell23_5005512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_5005512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005512 prefixEnd_5005512 := by exact prefixLift 5005512
  have htrace : WordTrace (prefixWord ++ tailWord_5005512) baseStart_5005512 baseEnd_5005512 := by
    simpa [prefixWord, tailWord_5005512, baseEnd_5005512] using wordTrace_append hprefix tailTrace_5005512
  have hstable : (prefixWord ++ tailWord_5005512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005512).length < 2 ^ (prefixWord ++ tailWord_5005512).sum := by decide
  have hdescent : baseEnd_5005512 < baseStart_5005512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005569 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_5005569 : Nat := 118140960795 + 5005569 * 2 ^ 59
def prefixEnd_5005569 : Nat := 4983230072969 + 3 ^ 40 * 5005569 * 2
def baseEnd_5005569 : Nat := 2570262846245431421967313

theorem tailTrace_5005569 : CollatzResearch.WordTrace tailWord_5005569 prefixEnd_5005569 2570262846245431421967313 := by
  unfold tailWord_5005569
  simp only [CollatzResearch.WordTrace]
  refine ⟨182568100002685870969587761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121712066668457247313058507 182568100002685870969587761)
  ·
    refine ⟨136926075002014403227190821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182568100002685870969587761 136926075002014403227190821)
    ·
      refine ⟨25673639062877700605098279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136926075002014403227190821 25673639062877700605098279)
      ·
        refine ⟨38510458594316550907647419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25673639062877700605098279 38510458594316550907647419)
        ·
          refine ⟨57765687891474826361471129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38510458594316550907647419 57765687891474826361471129)
          ·
            refine ⟨43324265918606119771103347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57765687891474826361471129 43324265918606119771103347)
            ·
              refine ⟨64986398877909179656655021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43324265918606119771103347 64986398877909179656655021)
              ·
                refine ⟨24369899579215942371245633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64986398877909179656655021 24369899579215942371245633)
                ·
                  refine ⟨18277424684411956778434225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24369899579215942371245633 18277424684411956778434225)
                  ·
                    refine ⟨13708068513308967583825669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18277424684411956778434225 13708068513308967583825669)
                    ·
                      refine ⟨2570262846245431421967313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13708068513308967583825669 2570262846245431421967313)
                      ·
                        rfl

theorem cell23_5005569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_5005569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005569 prefixEnd_5005569 := by exact prefixLift 5005569
  have htrace : WordTrace (prefixWord ++ tailWord_5005569) baseStart_5005569 baseEnd_5005569 := by
    simpa [prefixWord, tailWord_5005569, baseEnd_5005569] using wordTrace_append hprefix tailTrace_5005569
  have hstable : (prefixWord ++ tailWord_5005569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005569).length < 2 ^ (prefixWord ++ tailWord_5005569).sum := by decide
  have hdescent : baseEnd_5005569 < baseStart_5005569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005589 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 3]
def baseStart_5005589 : Nat := 118140960795 + 5005589 * 2 ^ 59
def prefixEnd_5005589 : Nat := 4983230072969 + 3 ^ 40 * 5005589 * 2
def baseEnd_5005589 : Nat := 2570273115858521343717221

theorem tailTrace_5005589 : CollatzResearch.WordTrace tailWord_5005589 prefixEnd_5005589 2570273115858521343717221 := by
  unfold tailWord_5005589
  simp only [CollatzResearch.WordTrace]
  refine ⟨182568829462613414385315821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121712552975075609590210547 182568829462613414385315821)
  ·
    refine ⟨68463311048480030394493433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182568829462613414385315821 68463311048480030394493433)
    ·
      refine ⟨51347483286360022795870075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68463311048480030394493433 51347483286360022795870075)
      ·
        refine ⟨77021224929540034193805113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51347483286360022795870075 77021224929540034193805113)
        ·
          refine ⟨57765918697155025645353835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77021224929540034193805113 57765918697155025645353835)
          ·
            refine ⟨86648878045732538468030753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57765918697155025645353835 86648878045732538468030753)
            ·
              refine ⟨64986658534299403851023065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86648878045732538468030753 64986658534299403851023065)
              ·
                refine ⟨48739993900724552888267299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64986658534299403851023065 48739993900724552888267299)
                ·
                  refine ⟨73109990851086829332400949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48739993900724552888267299 73109990851086829332400949)
                  ·
                    refine ⟨6854061642289390249912589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73109990851086829332400949 6854061642289390249912589)
                    ·
                      refine ⟨2570273115858521343717221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6854061642289390249912589 2570273115858521343717221)
                      ·
                        rfl

theorem cell23_5005589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_5005589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005589 prefixEnd_5005589 := by exact prefixLift 5005589
  have htrace : WordTrace (prefixWord ++ tailWord_5005589) baseStart_5005589 baseEnd_5005589 := by
    simpa [prefixWord, tailWord_5005589, baseEnd_5005589] using wordTrace_append hprefix tailTrace_5005589
  have hstable : (prefixWord ++ tailWord_5005589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005589).length < 2 ^ (prefixWord ++ tailWord_5005589).sum := by decide
  have hdescent : baseEnd_5005589 < baseStart_5005589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005619 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 5]
def baseStart_5005619 : Nat := 118140960795 + 5005619 * 2 ^ 59
def prefixEnd_5005619 : Nat := 4983230072969 + 3 ^ 40 * 5005619 * 2
def baseEnd_5005619 : Nat := 2570288520278156226342083

theorem tailTrace_5005619 : CollatzResearch.WordTrace tailWord_5005619 prefixEnd_5005619 2570288520278156226342083 := by
  unfold tailWord_5005619
  simp only [CollatzResearch.WordTrace]
  refine ⟨182569923652504729508907911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121713282435003153005938607 182569923652504729508907911)
  ·
    refine ⟨273854885478757094263361867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182569923652504729508907911 273854885478757094263361867)
    ·
      refine ⟨410782328218135641395042801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273854885478757094263361867 410782328218135641395042801)
      ·
        refine ⟨308086746163601731046282101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410782328218135641395042801 308086746163601731046282101)
        ·
          refine ⟨28883132452837662285588947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 308086746163601731046282101 28883132452837662285588947)
          ·
            refine ⟨43324698679256493428383421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28883132452837662285588947 43324698679256493428383421)
            ·
              refine ⟨16246762004721185035643783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43324698679256493428383421 16246762004721185035643783)
              ·
                refine ⟨24370143007081777553465675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16246762004721185035643783 24370143007081777553465675)
                ·
                  refine ⟨36555214510622666330198513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24370143007081777553465675 36555214510622666330198513)
                  ·
                    refine ⟨27416410882966999747648885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36555214510622666330198513 27416410882966999747648885)
                    ·
                      refine ⟨2570288520278156226342083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27416410882966999747648885 2570288520278156226342083)
                      ·
                        rfl

theorem cell23_5005619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_5005619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005619 prefixEnd_5005619 := by exact prefixLift 5005619
  have htrace : WordTrace (prefixWord ++ tailWord_5005619) baseStart_5005619 baseEnd_5005619 := by
    simpa [prefixWord, tailWord_5005619, baseEnd_5005619] using wordTrace_append hprefix tailTrace_5005619
  have hstable : (prefixWord ++ tailWord_5005619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005619).length < 2 ^ (prefixWord ++ tailWord_5005619).sum := by decide
  have hdescent : baseEnd_5005619 < baseStart_5005619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005646 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_5005646 : Nat := 118140960795 + 5005646 * 2 ^ 59
def prefixEnd_5005646 : Nat := 4983230072969 + 3 ^ 40 * 5005646 * 2
def baseEnd_5005646 : Nat := 2570302384255827620704459

theorem tailTrace_5005646 : CollatzResearch.WordTrace tailWord_5005646 prefixEnd_5005646 2570302384255827620704459 := by
  unfold tailWord_5005646
  simp only [CollatzResearch.WordTrace]
  refine ⟨22821363552925864140017599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121713938948937942080093861 22821363552925864140017599)
  ·
    refine ⟨34232045329388796210026399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22821363552925864140017599 34232045329388796210026399)
    ·
      refine ⟨51348067994083194315039599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34232045329388796210026399 51348067994083194315039599)
      ·
        refine ⟨77022101991124791472559399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51348067994083194315039599 77022101991124791472559399)
        ·
          refine ⟨115533152986687187208839099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77022101991124791472559399 115533152986687187208839099)
          ·
            refine ⟨173299729480030780813258649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115533152986687187208839099 173299729480030780813258649)
            ·
              refine ⟨129974797110023085609943987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173299729480030780813258649 129974797110023085609943987)
              ·
                refine ⟨194962195665034628414915981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129974797110023085609943987 194962195665034628414915981)
                ·
                  refine ⟨73110823374387985655593493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194962195665034628414915981 73110823374387985655593493)
                  ·
                    refine ⟨3427069845674436827605945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73110823374387985655593493 3427069845674436827605945)
                    ·
                      refine ⟨2570302384255827620704459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427069845674436827605945 2570302384255827620704459)
                      ·
                        rfl

theorem cell23_5005646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_5005646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005646 prefixEnd_5005646 := by exact prefixLift 5005646
  have htrace : WordTrace (prefixWord ++ tailWord_5005646) baseStart_5005646 baseEnd_5005646 := by
    simpa [prefixWord, tailWord_5005646, baseEnd_5005646] using wordTrace_append hprefix tailTrace_5005646
  have hstable : (prefixWord ++ tailWord_5005646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005646).length < 2 ^ (prefixWord ++ tailWord_5005646).sum := by decide
  have hdescent : baseEnd_5005646 < baseStart_5005646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005673 : List Nat := [1, 2, 1, 1, 1, 3, 5, 4, 1, 4]
def baseStart_5005673 : Nat := 118140960795 + 5005673 * 2 ^ 59
def prefixEnd_5005673 : Nat := 4983230072969 + 3 ^ 40 * 5005673 * 2
def baseEnd_5005673 : Nat := 856772082744499671688945

theorem tailTrace_5005673 : CollatzResearch.WordTrace tailWord_5005673 prefixEnd_5005673 856772082744499671688945 := by
  unfold tailWord_5005673
  simp only [CollatzResearch.WordTrace]
  refine ⟨182571893194309096731373673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121714595462872731154249115 182571893194309096731373673)
  ·
    refine ⟨136928919895731822548530255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182571893194309096731373673 136928919895731822548530255)
    ·
      refine ⟨205393379843597733822795383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136928919895731822548530255 205393379843597733822795383)
      ·
        refine ⟨308090069765396600734193075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205393379843597733822795383 308090069765396600734193075)
        ·
          refine ⟨462135104648094901101289613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308090069765396600734193075 462135104648094901101289613)
          ·
            refine ⟨173300664243035587912983605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 462135104648094901101289613 173300664243035587912983605)
            ·
              refine ⟨16246937272784586366842213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173300664243035587912983605 16246937272784586366842213)
              ·
                refine ⟨3046300738647109943782915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16246937272784586366842213 3046300738647109943782915)
                ·
                  refine ⟨4569451107970664915674373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046300738647109943782915 4569451107970664915674373)
                  ·
                    refine ⟨856772082744499671688945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4569451107970664915674373 856772082744499671688945)
                    ·
                      rfl

theorem cell23_5005673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 4].length) (baseStart_5005673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005673 prefixEnd_5005673 := by exact prefixLift 5005673
  have htrace : WordTrace (prefixWord ++ tailWord_5005673) baseStart_5005673 baseEnd_5005673 := by
    simpa [prefixWord, tailWord_5005673, baseEnd_5005673] using wordTrace_append hprefix tailTrace_5005673
  have hstable : (prefixWord ++ tailWord_5005673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005673).length < 2 ^ (prefixWord ++ tailWord_5005673).sum := by decide
  have hdescent : baseEnd_5005673 < baseStart_5005673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005730 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_5005730 : Nat := 118140960795 + 5005730 * 2 ^ 59
def prefixEnd_5005730 : Nat := 4983230072969 + 3 ^ 40 * 5005730 * 2
def baseEnd_5005730 : Nat := 2570345516630805292054073

theorem tailTrace_5005730 : CollatzResearch.WordTrace tailWord_5005730 prefixEnd_5005730 2570345516630805292054073 := by
  unfold tailWord_5005730
  simp only [CollatzResearch.WordTrace]
  refine ⟨45643493038775648866549661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121715981436735063644132429 45643493038775648866549661)
  ·
    refine ⟨17116309889540868324956123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45643493038775648866549661 17116309889540868324956123)
    ·
      refine ⟨25674464834311302487434185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17116309889540868324956123 25674464834311302487434185)
      ·
        refine ⟨19255848625733476865575639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25674464834311302487434185 19255848625733476865575639)
        ·
          refine ⟨28883772938600215298363459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19255848625733476865575639 28883772938600215298363459)
          ·
            refine ⟨43325659407900322947545189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28883772938600215298363459 43325659407900322947545189)
            ·
              refine ⟨8123561138981310552664723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43325659407900322947545189 8123561138981310552664723)
              ·
                refine ⟨12185341708471965828997085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8123561138981310552664723 12185341708471965828997085)
                ·
                  refine ⟨4569503140676987185873907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12185341708471965828997085 4569503140676987185873907)
                  ·
                    refine ⟨6854254711015480778810861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4569503140676987185873907 6854254711015480778810861)
                    ·
                      refine ⟨2570345516630805292054073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6854254711015480778810861 2570345516630805292054073)
                      ·
                        rfl

theorem cell23_5005730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_5005730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005730 prefixEnd_5005730 := by exact prefixLift 5005730
  have htrace : WordTrace (prefixWord ++ tailWord_5005730) baseStart_5005730 baseEnd_5005730 := by
    simpa [prefixWord, tailWord_5005730, baseEnd_5005730] using wordTrace_append hprefix tailTrace_5005730
  have hstable : (prefixWord ++ tailWord_5005730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005730).length < 2 ^ (prefixWord ++ tailWord_5005730).sum := by decide
  have hdescent : baseEnd_5005730 < baseStart_5005730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005753 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 4]
def baseStart_5005753 : Nat := 118140960795 + 5005753 * 2 ^ 59
def prefixEnd_5005753 : Nat := 4983230072969 + 3 ^ 40 * 5005753 * 2
def baseEnd_5005753 : Nat := 2570357326685858702066467

theorem tailTrace_5005753 : CollatzResearch.WordTrace tailWord_5005753 prefixEnd_5005753 2570357326685858702066467 := by
  unfold tailWord_5005753
  simp only [CollatzResearch.WordTrace]
  refine ⟨182574811034019270394285913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121716540689346180262857275 182574811034019270394285913)
  ·
    refine ⟨136931108275514452795714435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182574811034019270394285913 136931108275514452795714435)
    ·
      refine ⟨205396662413271679193571653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136931108275514452795714435 205396662413271679193571653)
      ·
        refine ⟨38511874202488439848794685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205396662413271679193571653 38511874202488439848794685)
        ·
          refine ⟨14441952825933164943298007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38511874202488439848794685 14441952825933164943298007)
          ·
            refine ⟨21662929238899747414947011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14441952825933164943298007 21662929238899747414947011)
            ·
              refine ⟨32494393858349621122420517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21662929238899747414947011 32494393858349621122420517)
              ·
                refine ⟨6092698848440553960453847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32494393858349621122420517 6092698848440553960453847)
                ·
                  refine ⟨9139048272660830940680771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6092698848440553960453847 9139048272660830940680771)
                  ·
                    refine ⟨13708572408991246411021157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9139048272660830940680771 13708572408991246411021157)
                    ·
                      refine ⟨2570357326685858702066467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13708572408991246411021157 2570357326685858702066467)
                      ·
                        rfl

theorem cell23_5005753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_5005753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005753 prefixEnd_5005753 := by exact prefixLift 5005753
  have htrace : WordTrace (prefixWord ++ tailWord_5005753) baseStart_5005753 baseEnd_5005753 := by
    simpa [prefixWord, tailWord_5005753, baseEnd_5005753] using wordTrace_append hprefix tailTrace_5005753
  have hstable : (prefixWord ++ tailWord_5005753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005753).length < 2 ^ (prefixWord ++ tailWord_5005753).sum := by decide
  have hdescent : baseEnd_5005753 < baseStart_5005753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005843 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 3, 4, 2]
def baseStart_5005843 : Nat := 118140960795 + 5005843 * 2 ^ 59
def prefixEnd_5005843 : Nat := 4983230072969 + 3 ^ 40 * 5005843 * 2
def baseEnd_5005843 : Nat := 2570403539944763349941053

theorem tailTrace_5005843 : CollatzResearch.WordTrace tailWord_5005843 prefixEnd_5005843 2570403539944763349941053 := by
  unfold tailWord_5005843
  simp only [CollatzResearch.WordTrace]
  refine ⟨182578093603693215765062183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121718729069128810510041455 182578093603693215765062183)
  ·
    refine ⟨273867140405539823647593275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182578093603693215765062183 273867140405539823647593275)
    ·
      refine ⟨410800710608309735471389913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273867140405539823647593275 410800710608309735471389913)
      ·
        refine ⟨308100532956232301603542435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410800710608309735471389913 308100532956232301603542435)
        ·
          refine ⟨462150799434348452405313653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308100532956232301603542435 462150799434348452405313653)
          ·
            refine ⟨43326637446970167412998155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 462150799434348452405313653 43326637446970167412998155)
            ·
              refine ⟨64989956170455251119497233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43326637446970167412998155 64989956170455251119497233)
              ·
                refine ⟨48742467127841438339622925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64989956170455251119497233 48742467127841438339622925)
                ·
                  refine ⟨18278425172940539377358597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48742467127841438339622925 18278425172940539377358597)
                  ·
                    refine ⟨3427204719926351133254737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18278425172940539377358597 3427204719926351133254737)
                    ·
                      refine ⟨2570403539944763349941053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427204719926351133254737 2570403539944763349941053)
                      ·
                        rfl

theorem cell23_5005843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 4, 2].length) (baseStart_5005843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005843 prefixEnd_5005843 := by exact prefixLift 5005843
  have htrace : WordTrace (prefixWord ++ tailWord_5005843) baseStart_5005843 baseEnd_5005843 := by
    simpa [prefixWord, tailWord_5005843, baseEnd_5005843] using wordTrace_append hprefix tailTrace_5005843
  have hstable : (prefixWord ++ tailWord_5005843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005843).length < 2 ^ (prefixWord ++ tailWord_5005843).sum := by decide
  have hdescent : baseEnd_5005843 < baseStart_5005843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005853 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_5005853 : Nat := 118140960795 + 5005853 * 2 ^ 59
def prefixEnd_5005853 : Nat := 4983230072969 + 3 ^ 40 * 5005853 * 2
def baseEnd_5005853 : Nat := 856802891583769436938669

theorem tailTrace_5005853 : CollatzResearch.WordTrace tailWord_5005853 prefixEnd_5005853 856802891583769436938669 := by
  unfold tailWord_5005853
  simp only [CollatzResearch.WordTrace]
  refine ⟨182578458333656987472926213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121718972222437991648617475 182578458333656987472926213)
  ·
    refine ⟨34233460937560685151173665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182578458333656987472926213 34233460937560685151173665)
    ·
      refine ⟨25675095703170513863380249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34233460937560685151173665 25675095703170513863380249)
      ·
        refine ⟨19256321777377885397535187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25675095703170513863380249 19256321777377885397535187)
        ·
          refine ⟨28884482666066828096302781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19256321777377885397535187 28884482666066828096302781)
          ·
            refine ⟨10831680999775060536113543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28884482666066828096302781 10831680999775060536113543)
            ·
              refine ⟨16247521499662590804170315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10831680999775060536113543 16247521499662590804170315)
              ·
                refine ⟨24371282249493886206255473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16247521499662590804170315 24371282249493886206255473)
                ·
                  refine ⟨18278461687120414654691605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24371282249493886206255473 18278461687120414654691605)
                  ·
                    refine ⟨856802891583769436938669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18278461687120414654691605 856802891583769436938669)
                    ·
                      rfl

theorem cell23_5005853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_5005853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005853 prefixEnd_5005853 := by exact prefixLift 5005853
  have htrace : WordTrace (prefixWord ++ tailWord_5005853) baseStart_5005853 baseEnd_5005853 := by
    simpa [prefixWord, tailWord_5005853, baseEnd_5005853] using wordTrace_append hprefix tailTrace_5005853
  have hstable : (prefixWord ++ tailWord_5005853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005853).length < 2 ^ (prefixWord ++ tailWord_5005853).sum := by decide
  have hdescent : baseEnd_5005853 < baseStart_5005853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005893 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 3]
def baseStart_5005893 : Nat := 118140960795 + 5005893 * 2 ^ 59
def prefixEnd_5005893 : Nat := 4983230072969 + 3 ^ 40 * 5005893 * 2
def baseEnd_5005893 : Nat := 2570429213977488154315823

theorem tailTrace_5005893 : CollatzResearch.WordTrace tailWord_5005893 prefixEnd_5005893 2570429213977488154315823 := by
  unfold tailWord_5005893
  simp only [CollatzResearch.WordTrace]
  refine ⟨182579917253512074304382333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121719944835674716202921555 182579917253512074304382333)
  ·
    refine ⟨68467468970067027864143375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182579917253512074304382333 68467468970067027864143375)
    ·
      refine ⟨102701203455100541796215063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68467468970067027864143375 102701203455100541796215063)
      ·
        refine ⟨154051805182650812694322595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102701203455100541796215063 154051805182650812694322595)
        ·
          refine ⟨231077707773976219041483893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154051805182650812694322595 231077707773976219041483893)
          ·
            refine ⟨21663535103810270535139115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231077707773976219041483893 21663535103810270535139115)
            ·
              refine ⟨32495302655715405802708673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21663535103810270535139115 32495302655715405802708673)
              ·
                refine ⟨24371476991786554352031505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32495302655715405802708673 24371476991786554352031505)
                ·
                  refine ⟨18278607743839915764023629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24371476991786554352031505 18278607743839915764023629)
                  ·
                    refine ⟨6854477903939968411508861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18278607743839915764023629 6854477903939968411508861)
                    ·
                      refine ⟨2570429213977488154315823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6854477903939968411508861 2570429213977488154315823)
                      ·
                        rfl

theorem cell23_5005893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_5005893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005893 prefixEnd_5005893 := by exact prefixLift 5005893
  have htrace : WordTrace (prefixWord ++ tailWord_5005893) baseStart_5005893 baseEnd_5005893 := by
    simpa [prefixWord, tailWord_5005893, baseEnd_5005893] using wordTrace_append hprefix tailTrace_5005893
  have hstable : (prefixWord ++ tailWord_5005893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005893).length < 2 ^ (prefixWord ++ tailWord_5005893).sum := by decide
  have hdescent : baseEnd_5005893 < baseStart_5005893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005903 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 1, 7, 2]
def baseStart_5005903 : Nat := 118140960795 + 5005903 * 2 ^ 59
def prefixEnd_5005903 : Nat := 4983230072969 + 3 ^ 40 * 5005903 * 2
def baseEnd_5005903 : Nat := 2570434348784033115190777

theorem tailTrace_5005903 : CollatzResearch.WordTrace tailWord_5005903 prefixEnd_5005903 2570434348784033115190777 := by
  unfold tailWord_5005903
  simp only [CollatzResearch.WordTrace]
  refine ⟨182580281983475846012246363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121720187988983897341497575 182580281983475846012246363)
  ·
    refine ⟨273870422975213769018369545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182580281983475846012246363 273870422975213769018369545)
    ·
      refine ⟨205402817231410326763777159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273870422975213769018369545 205402817231410326763777159)
      ·
        refine ⟨308104225847115490145665739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205402817231410326763777159 308104225847115490145665739)
        ·
          refine ⟨462156338770673235218498609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308104225847115490145665739 462156338770673235218498609)
          ·
            refine ⟨346617254078004926413873957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462156338770673235218498609 346617254078004926413873957)
            ·
              refine ⟨64990735139625923702601367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 346617254078004926413873957 64990735139625923702601367)
              ·
                refine ⟨97486102709438885553902051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64990735139625923702601367 97486102709438885553902051)
                ·
                  refine ⟨146229154064158328330853077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97486102709438885553902051 146229154064158328330853077)
                  ·
                    refine ⟨3427245798378710820254369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 146229154064158328330853077 3427245798378710820254369)
                    ·
                      refine ⟨2570434348784033115190777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427245798378710820254369 2570434348784033115190777)
                      ·
                        rfl

theorem cell23_5005903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 7, 2].length) (baseStart_5005903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005903 prefixEnd_5005903 := by exact prefixLift 5005903
  have htrace : WordTrace (prefixWord ++ tailWord_5005903) baseStart_5005903 baseEnd_5005903 := by
    simpa [prefixWord, tailWord_5005903, baseEnd_5005903] using wordTrace_append hprefix tailTrace_5005903
  have hstable : (prefixWord ++ tailWord_5005903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005903).length < 2 ^ (prefixWord ++ tailWord_5005903).sum := by decide
  have hdescent : baseEnd_5005903 < baseStart_5005903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5005943 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 5, 4]
def baseStart_5005943 : Nat := 118140960795 + 5005943 * 2 ^ 59
def prefixEnd_5005943 : Nat := 4983230072969 + 3 ^ 40 * 5005943 * 2
def baseEnd_5005943 : Nat := 856818296003404319563531

theorem tailTrace_5005943 : CollatzResearch.WordTrace tailWord_5005943 prefixEnd_5005943 856818296003404319563531 := by
  unfold tailWord_5005943
  simp only [CollatzResearch.WordTrace]
  refine ⟨182581740903330932843702483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121721160602220621895801655 182581740903330932843702483)
  ·
    refine ⟨273872611354996399265553725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182581740903330932843702483 273872611354996399265553725)
    ·
      refine ⟨102702229258123649724582647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273872611354996399265553725 102702229258123649724582647)
      ·
        refine ⟨154053343887185474586873971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102702229258123649724582647 154053343887185474586873971)
        ·
          refine ⟨231080015830778211880310957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154053343887185474586873971 231080015830778211880310957)
          ·
            refine ⟨86655005936541829455116609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231080015830778211880310957 86655005936541829455116609)
            ·
              refine ⟨64991254452406372091337457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86655005936541829455116609 64991254452406372091337457)
              ·
                refine ⟨48743440839304779068503093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64991254452406372091337457 48743440839304779068503093)
                ·
                  refine ⟨4569697578684823037672165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48743440839304779068503093 4569697578684823037672165)
                  ·
                    refine ⟨856818296003404319563531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4569697578684823037672165 856818296003404319563531)
                    ·
                      rfl

theorem cell23_5005943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_5005943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5005943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5005943 prefixEnd_5005943 := by exact prefixLift 5005943
  have htrace : WordTrace (prefixWord ++ tailWord_5005943) baseStart_5005943 baseEnd_5005943 := by
    simpa [prefixWord, tailWord_5005943, baseEnd_5005943] using wordTrace_append hprefix tailTrace_5005943
  have hstable : (prefixWord ++ tailWord_5005943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5005943).length < 2 ^ (prefixWord ++ tailWord_5005943).sum := by decide
  have hdescent : baseEnd_5005943 < baseStart_5005943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5005943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006020 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_5006020 : Nat := 118140960795 + 5006020 * 2 ^ 59
def prefixEnd_5006020 : Nat := 4983230072969 + 3 ^ 40 * 5006020 * 2
def baseEnd_5006020 : Nat := 856831475340203052475913

theorem tailTrace_5006020 : CollatzResearch.WordTrace tailWord_5006020 prefixEnd_5006020 856831475340203052475913 := by
  unfold tailWord_5006020
  simp only [CollatzResearch.WordTrace]
  refine ⟨91292274662025987497127757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121723032882701316662837009 91292274662025987497127757)
  ·
    refine ⟨34234602998259745311422909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91292274662025987497127757 34234602998259745311422909)
    ·
      refine ⟨12837976124347404491783591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34234602998259745311422909 12837976124347404491783591)
      ·
        refine ⟨19256964186521106737675387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12837976124347404491783591 19256964186521106737675387)
        ·
          refine ⟨28885446279781660106513081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19256964186521106737675387 28885446279781660106513081)
          ·
            refine ⟨21664084709836245079884811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28885446279781660106513081 21664084709836245079884811)
            ·
              refine ⟨32496127064754367619827217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21664084709836245079884811 32496127064754367619827217)
              ·
                refine ⟨24372095298565775714870413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32496127064754367619827217 24372095298565775714870413)
                ·
                  refine ⟨9139535736962165893076405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24372095298565775714870413 9139535736962165893076405)
                  ·
                    refine ⟨856831475340203052475913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9139535736962165893076405 856831475340203052475913)
                    ·
                      rfl

theorem cell23_5006020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_5006020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006020 prefixEnd_5006020 := by exact prefixLift 5006020
  have htrace : WordTrace (prefixWord ++ tailWord_5006020) baseStart_5006020 baseEnd_5006020 := by
    simpa [prefixWord, tailWord_5006020, baseEnd_5006020] using wordTrace_append hprefix tailTrace_5006020
  have hstable : (prefixWord ++ tailWord_5006020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006020).length < 2 ^ (prefixWord ++ tailWord_5006020).sum := by decide
  have hdescent : baseEnd_5006020 < baseStart_5006020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006034 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_5006034 : Nat := 118140960795 + 5006034 * 2 ^ 59
def prefixEnd_5006034 : Nat := 4983230072969 + 3 ^ 40 * 5006034 * 2
def baseEnd_5006034 : Nat := 2570501614749772102652675

theorem tailTrace_5006034 : CollatzResearch.WordTrace tailWord_5006034 prefixEnd_5006034 2570501614749772102652675 := by
  unfold tailWord_5006034
  simp only [CollatzResearch.WordTrace]
  refine ⟨45646264986500313846316289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121723373297334170256843437 45646264986500313846316289)
  ·
    refine ⟨34234698739875235384737217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45646264986500313846316289 34234698739875235384737217)
    ·
      refine ⟨25676024054906426538552913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34234698739875235384737217 25676024054906426538552913)
      ·
        refine ⟨19257018041179819903914685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25676024054906426538552913 19257018041179819903914685)
        ·
          refine ⟨7221381765442432463968007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19257018041179819903914685 7221381765442432463968007)
          ·
            refine ⟨10832072648163648695952011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7221381765442432463968007 10832072648163648695952011)
            ·
              refine ⟨16248108972245473043928017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10832072648163648695952011 16248108972245473043928017)
              ·
                refine ⟨12186081729184104782946013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16248108972245473043928017 12186081729184104782946013)
                ·
                  refine ⟨4569780648444039293604755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12186081729184104782946013 4569780648444039293604755)
                  ·
                    refine ⟨6854670972666058940407133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4569780648444039293604755 6854670972666058940407133)
                    ·
                      refine ⟨2570501614749772102652675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6854670972666058940407133 2570501614749772102652675)
                      ·
                        rfl

theorem cell23_5006034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_5006034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006034 prefixEnd_5006034 := by exact prefixLift 5006034
  have htrace : WordTrace (prefixWord ++ tailWord_5006034) baseStart_5006034 baseEnd_5006034 := by
    simpa [prefixWord, tailWord_5006034, baseEnd_5006034] using wordTrace_append hprefix tailTrace_5006034
  have hstable : (prefixWord ++ tailWord_5006034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006034).length < 2 ^ (prefixWord ++ tailWord_5006034).sum := by decide
  have hdescent : baseEnd_5006034 < baseStart_5006034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006040 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_5006040 : Nat := 118140960795 + 5006040 * 2 ^ 59
def prefixEnd_5006040 : Nat := 4983230072969 + 3 ^ 40 * 5006040 * 2
def baseEnd_5006040 : Nat := 2570504695633699079177647

theorem tailTrace_5006040 : CollatzResearch.WordTrace tailWord_5006040 prefixEnd_5006040 2570504695633699079177647 := by
  unfold tailWord_5006040
  simp only [CollatzResearch.WordTrace]
  refine ⟨91292639391989759204991787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121723519189319678939989049 91292639391989759204991787)
  ·
    refine ⟨136938959087984638807487681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91292639391989759204991787 136938959087984638807487681)
    ·
      refine ⟨102704219315988479105615761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136938959087984638807487681 102704219315988479105615761)
      ·
        refine ⟨77028164486991359329211821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102704219315988479105615761 77028164486991359329211821)
        ·
          refine ⟨28885561682621759748454433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77028164486991359329211821 28885561682621759748454433)
          ·
            refine ⟨21664171261966319811340825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28885561682621759748454433 21664171261966319811340825)
            ·
              refine ⟨16248128446474739858505619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21664171261966319811340825 16248128446474739858505619)
              ·
                refine ⟨24372192669712109787758429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16248128446474739858505619 24372192669712109787758429)
                ·
                  refine ⟨9139572251142041170409411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24372192669712109787758429 9139572251142041170409411)
                  ·
                    refine ⟨13709358376713061755614117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9139572251142041170409411 13709358376713061755614117)
                    ·
                      refine ⟨2570504695633699079177647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13709358376713061755614117 2570504695633699079177647)
                      ·
                        rfl

theorem cell23_5006040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_5006040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006040 prefixEnd_5006040 := by exact prefixLift 5006040
  have htrace : WordTrace (prefixWord ++ tailWord_5006040) baseStart_5006040 baseEnd_5006040 := by
    simpa [prefixWord, tailWord_5006040, baseEnd_5006040] using wordTrace_append hprefix tailTrace_5006040
  have hstable : (prefixWord ++ tailWord_5006040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006040).length < 2 ^ (prefixWord ++ tailWord_5006040).sum := by decide
  have hdescent : baseEnd_5006040 < baseStart_5006040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006043 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 3]
def baseStart_5006043 : Nat := 118140960795 + 5006043 * 2 ^ 59
def prefixEnd_5006043 : Nat := 4983230072969 + 3 ^ 40 * 5006043 * 2
def baseEnd_5006043 : Nat := 2570506236075662567440133

theorem tailTrace_5006043 : CollatzResearch.WordTrace tailWord_5006043 prefixEnd_5006043 2570506236075662567440133 := by
  unfold tailWord_5006043
  simp only [CollatzResearch.WordTrace]
  refine ⟨182585388202968649922342783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121723592135312433281561855 182585388202968649922342783)
  ·
    refine ⟨273878082304452974883514175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182585388202968649922342783 273878082304452974883514175)
    ·
      refine ⟨410817123456679462325271263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273878082304452974883514175 410817123456679462325271263)
      ·
        refine ⟨616225685185019193487906895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410817123456679462325271263 616225685185019193487906895)
        ·
          refine ⟨924338527777528790231860343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616225685185019193487906895 924338527777528790231860343)
          ·
            refine ⟨1386507791666293185347790515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924338527777528790231860343 1386507791666293185347790515)
            ·
              refine ⟨2079761687499439778021685773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386507791666293185347790515 2079761687499439778021685773)
              ·
                refine ⟨779910632812289916758132165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2079761687499439778021685773 779910632812289916758132165)
                ·
                  refine ⟨146233243652304359392149781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779910632812289916758132165 146233243652304359392149781)
                  ·
                    refine ⟨6854683296201766846507021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 146233243652304359392149781 6854683296201766846507021)
                    ·
                      refine ⟨2570506236075662567440133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6854683296201766846507021 2570506236075662567440133)
                      ·
                        rfl

theorem cell23_5006043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 3].length) (baseStart_5006043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006043 prefixEnd_5006043 := by exact prefixLift 5006043
  have htrace : WordTrace (prefixWord ++ tailWord_5006043) baseStart_5006043 baseEnd_5006043 := by
    simpa [prefixWord, tailWord_5006043, baseEnd_5006043] using wordTrace_append hprefix tailTrace_5006043
  have hstable : (prefixWord ++ tailWord_5006043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006043).length < 2 ^ (prefixWord ++ tailWord_5006043).sum := by decide
  have hdescent : baseEnd_5006043 < baseStart_5006043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006044 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_5006044 : Nat := 118140960795 + 5006044 * 2 ^ 59
def prefixEnd_5006044 : Nat := 4983230072969 + 3 ^ 40 * 5006044 * 2
def baseEnd_5006044 : Nat := 2570506749556317063527629

theorem tailTrace_5006044 : CollatzResearch.WordTrace tailWord_5006044 prefixEnd_5006044 2570506749556317063527629 := by
  unfold tailWord_5006044
  simp only [CollatzResearch.WordTrace]
  refine ⟨91292712337982513546564593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121723616450643351395419457 91292712337982513546564593)
  ·
    refine ⟨68469534253486885159923445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91292712337982513546564593 68469534253486885159923445)
    ·
      refine ⟨6419018836264395483742823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68469534253486885159923445 6419018836264395483742823)
      ·
        refine ⟨9628528254396593225614235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6419018836264395483742823 9628528254396593225614235)
        ·
          refine ⟨14442792381594889838421353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9628528254396593225614235 14442792381594889838421353)
          ·
            refine ⟨10832094286196167378816015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14442792381594889838421353 10832094286196167378816015)
            ·
              refine ⟨16248141429294251068224023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10832094286196167378816015 16248141429294251068224023)
              ·
                refine ⟨24372212143941376602336035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16248141429294251068224023 24372212143941376602336035)
                ·
                  refine ⟨36558318215912064903504053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24372212143941376602336035 36558318215912064903504053)
                  ·
                    refine ⟨3427342332741756084703505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36558318215912064903504053 3427342332741756084703505)
                    ·
                      refine ⟨2570506749556317063527629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427342332741756084703505 2570506749556317063527629)
                      ·
                        rfl

theorem cell23_5006044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_5006044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006044 prefixEnd_5006044 := by exact prefixLift 5006044
  have htrace : WordTrace (prefixWord ++ tailWord_5006044) baseStart_5006044 baseEnd_5006044 := by
    simpa [prefixWord, tailWord_5006044, baseEnd_5006044] using wordTrace_append hprefix tailTrace_5006044
  have hstable : (prefixWord ++ tailWord_5006044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006044).length < 2 ^ (prefixWord ++ tailWord_5006044).sum := by decide
  have hdescent : baseEnd_5006044 < baseStart_5006044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006051 : List Nat := [1, 1, 1, 7, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5006051 : Nat := 118140960795 + 5006051 * 2 ^ 59
def prefixEnd_5006051 : Nat := 4983230072969 + 3 ^ 40 * 5006051 * 2
def baseEnd_5006051 : Nat := 2570510343920898536140097

theorem tailTrace_5006051 : CollatzResearch.WordTrace tailWord_5006051 prefixEnd_5006051 2570510343920898536140097 := by
  unfold tailWord_5006051
  simp only [CollatzResearch.WordTrace]
  refine ⟨182585679986939667288634007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121723786657959778192422671 182585679986939667288634007)
  ·
    refine ⟨273878519980409500932951011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182585679986939667288634007 273878519980409500932951011)
    ·
      refine ⟨410817779970614251399426517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273878519980409500932951011 410817779970614251399426517)
      ·
        refine ⟨9628541718061271517174059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 410817779970614251399426517 9628541718061271517174059)
        ·
          refine ⟨14442812577091907275761089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9628541718061271517174059 14442812577091907275761089)
          ·
            refine ⟨10832109432818930456820817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14442812577091907275761089 10832109432818930456820817)
            ·
              refine ⟨8124082074614197842615613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10832109432818930456820817 8124082074614197842615613)
              ·
                refine ⟨3046530777980324190980855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8124082074614197842615613 3046530777980324190980855)
                ·
                  refine ⟨4569796166970486286471283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046530777980324190980855 4569796166970486286471283)
                  ·
                    refine ⟨6854694250455729429706925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4569796166970486286471283 6854694250455729429706925)
                    ·
                      refine ⟨2570510343920898536140097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6854694250455729429706925 2570510343920898536140097)
                      ·
                        rfl

theorem cell23_5006051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5006051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006051 prefixEnd_5006051 := by exact prefixLift 5006051
  have htrace : WordTrace (prefixWord ++ tailWord_5006051) baseStart_5006051 baseEnd_5006051 := by
    simpa [prefixWord, tailWord_5006051, baseEnd_5006051] using wordTrace_append hprefix tailTrace_5006051
  have hstable : (prefixWord ++ tailWord_5006051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006051).length < 2 ^ (prefixWord ++ tailWord_5006051).sum := by decide
  have hdescent : baseEnd_5006051 < baseStart_5006051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006057 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 1, 1, 4]
def baseStart_5006057 : Nat := 118140960795 + 5006057 * 2 ^ 59
def prefixEnd_5006057 : Nat := 4983230072969 + 3 ^ 40 * 5006057 * 2
def baseEnd_5006057 : Nat := 2570513424804825512665069

theorem tailTrace_5006057 : CollatzResearch.WordTrace tailWord_5006057 prefixEnd_5006057 2570513424804825512665069 := by
  unfold tailWord_5006057
  simp only [CollatzResearch.WordTrace]
  refine ⟨182585898824917930313352425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121723932549945286875568283 182585898824917930313352425)
  ·
    refine ⟨136939424118688447735014319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182585898824917930313352425 136939424118688447735014319)
    ·
      refine ⟨205409136178032671602521479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136939424118688447735014319 205409136178032671602521479)
      ·
        refine ⟨308113704267049007403782219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205409136178032671602521479 308113704267049007403782219)
        ·
          refine ⟨462170556400573511105673329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308113704267049007403782219 462170556400573511105673329)
          ·
            refine ⟨346627917300430133329254997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462170556400573511105673329 346627917300430133329254997)
            ·
              refine ⟨4062045905864415624952207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 346627917300430133329254997 4062045905864415624952207)
              ·
                refine ⟨6093068858796623437428311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4062045905864415624952207 6093068858796623437428311)
                ·
                  refine ⟨9139603288194935156142467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6093068858796623437428311 9139603288194935156142467)
                  ·
                    refine ⟨13709404932292402734213701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9139603288194935156142467 13709404932292402734213701)
                    ·
                      refine ⟨2570513424804825512665069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13709404932292402734213701 2570513424804825512665069)
                      ·
                        rfl

theorem cell23_5006057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 1, 4].length) (baseStart_5006057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006057 prefixEnd_5006057 := by exact prefixLift 5006057
  have htrace : WordTrace (prefixWord ++ tailWord_5006057) baseStart_5006057 baseEnd_5006057 := by
    simpa [prefixWord, tailWord_5006057, baseEnd_5006057] using wordTrace_append hprefix tailTrace_5006057
  have hstable : (prefixWord ++ tailWord_5006057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006057).length < 2 ^ (prefixWord ++ tailWord_5006057).sum := by decide
  have hdescent : baseEnd_5006057 < baseStart_5006057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006063 : List Nat := [1, 1, 2, 1, 5, 3, 10]
def baseStart_5006063 : Nat := 118140960795 + 5006063 * 2 ^ 59
def prefixEnd_5006063 : Nat := 4983230072969 + 3 ^ 40 * 5006063 * 2
def baseEnd_5006063 : Nat := 31734771675169783817161

theorem tailTrace_5006063 : CollatzResearch.WordTrace tailWord_5006063 prefixEnd_5006063 31734771675169783817161 := by
  unfold tailWord_5006063
  simp only [CollatzResearch.WordTrace]
  refine ⟨182586117662896193338070843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121724078441930795558713895 182586117662896193338070843)
  ·
    refine ⟨273879176494344290007106265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182586117662896193338070843 273879176494344290007106265)
    ·
      refine ⟨205409382370758217505329699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273879176494344290007106265 205409382370758217505329699)
      ·
        refine ⟨308114073556137326257994549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205409382370758217505329699 308114073556137326257994549)
        ·
          refine ⟨28885694395887874336686989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 308114073556137326257994549 28885694395887874336686989)
          ·
            refine ⟨10832135398457952876257621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28885694395887874336686989 10832135398457952876257621)
            ·
              refine ⟨31734771675169783817161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10832135398457952876257621 31734771675169783817161)
              ·
                rfl

theorem cell23_5006063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 10].length) (baseStart_5006063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006063 prefixEnd_5006063 := by exact prefixLift 5006063
  have htrace : WordTrace (prefixWord ++ tailWord_5006063) baseStart_5006063 baseEnd_5006063 := by
    simpa [prefixWord, tailWord_5006063, baseEnd_5006063] using wordTrace_append hprefix tailTrace_5006063
  have hstable : (prefixWord ++ tailWord_5006063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006063).length < 2 ^ (prefixWord ++ tailWord_5006063).sum := by decide
  have hdescent : baseEnd_5006063 < baseStart_5006063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006068 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5006068 : Nat := 118140960795 + 5006068 * 2 ^ 59
def prefixEnd_5006068 : Nat := 4983230072969 + 3 ^ 40 * 5006068 * 2
def baseEnd_5006068 : Nat := 2570519073092024969627519

theorem tailTrace_5006068 : CollatzResearch.WordTrace tailWord_5006068 prefixEnd_5006068 2570519073092024969627519 := by
  unfold tailWord_5006068
  simp only [CollatzResearch.WordTrace]
  refine ⟨91293150013939039596001429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121724200018585386128001905 91293150013939039596001429)
  ·
    refine ⟨4279366406903392481062567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91293150013939039596001429 4279366406903392481062567)
    ·
      refine ⟨6419049610355088721593851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4279366406903392481062567 6419049610355088721593851)
      ·
        refine ⟨9628574415532633082390777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6419049610355088721593851 9628574415532633082390777)
        ·
          refine ⟨7221430811649474811793083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9628574415532633082390777 7221430811649474811793083)
          ·
            refine ⟨10832146217474212217689625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7221430811649474811793083 10832146217474212217689625)
            ·
              refine ⟨8124109663105659163267219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10832146217474212217689625 8124109663105659163267219)
              ·
                refine ⟨12186164494658488744900829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8124109663105659163267219 12186164494658488744900829)
                ·
                  refine ⟨4569811685496933279337811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12186164494658488744900829 4569811685496933279337811)
                  ·
                    refine ⟨6854717528245399919006717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4569811685496933279337811 6854717528245399919006717)
                    ·
                      refine ⟨2570519073092024969627519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6854717528245399919006717 2570519073092024969627519)
                      ·
                        rfl

theorem cell23_5006068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5006068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006068 prefixEnd_5006068 := by exact prefixLift 5006068
  have htrace : WordTrace (prefixWord ++ tailWord_5006068) baseStart_5006068 baseEnd_5006068 := by
    simpa [prefixWord, tailWord_5006068, baseEnd_5006068] using wordTrace_append hprefix tailTrace_5006068
  have hstable : (prefixWord ++ tailWord_5006068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006068).length < 2 ^ (prefixWord ++ tailWord_5006068).sum := by decide
  have hdescent : baseEnd_5006068 < baseStart_5006068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006070 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_5006070 : Nat := 118140960795 + 5006070 * 2 ^ 59
def prefixEnd_5006070 : Nat := 4983230072969 + 3 ^ 40 * 5006070 * 2
def baseEnd_5006070 : Nat := 2570520100053333961802509

theorem tailTrace_5006070 : CollatzResearch.WordTrace tailWord_5006070 prefixEnd_5006070 2570520100053333961802509 := by
  unfold tailWord_5006070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411648310866927095848479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121724248649247222355717109 11411648310866927095848479)
  ·
    refine ⟨17117472466300390643772719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11411648310866927095848479 17117472466300390643772719)
    ·
      refine ⟨25676208699450585965659079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17117472466300390643772719 25676208699450585965659079)
      ·
        refine ⟨38514313049175878948488619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25676208699450585965659079 38514313049175878948488619)
        ·
          refine ⟨57771469573763818422732929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38514313049175878948488619 57771469573763818422732929)
          ·
            refine ⟨43328602180322863817049697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57771469573763818422732929 43328602180322863817049697)
            ·
              refine ⟨32496451635242147862787273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43328602180322863817049697 32496451635242147862787273)
              ·
                refine ⟨24372338726431610897090455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32496451635242147862787273 24372338726431610897090455)
                ·
                  refine ⟨36558508089647416345635683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24372338726431610897090455 36558508089647416345635683)
                  ·
                    refine ⟨54837762134471124518453525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36558508089647416345635683 54837762134471124518453525)
                    ·
                      refine ⟨2570520100053333961802509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54837762134471124518453525 2570520100053333961802509)
                      ·
                        rfl

theorem cell23_5006070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_5006070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006070 prefixEnd_5006070 := by exact prefixLift 5006070
  have htrace : WordTrace (prefixWord ++ tailWord_5006070) baseStart_5006070 baseEnd_5006070 := by
    simpa [prefixWord, tailWord_5006070, baseEnd_5006070] using wordTrace_append hprefix tailTrace_5006070
  have hstable : (prefixWord ++ tailWord_5006070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006070).length < 2 ^ (prefixWord ++ tailWord_5006070).sum := by decide
  have hdescent : baseEnd_5006070 < baseStart_5006070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006084 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_5006084 : Nat := 118140960795 + 5006084 * 2 ^ 59
def prefixEnd_5006084 : Nat := 4983230072969 + 3 ^ 40 * 5006084 * 2
def baseEnd_5006084 : Nat := 856842429594165635675815

theorem tailTrace_5006084 : CollatzResearch.WordTrace tailWord_5006084 prefixEnd_5006084 856842429594165635675815 := by
  unfold tailWord_5006084
  simp only [CollatzResearch.WordTrace]
  refine ⟨91293441797910056962292653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121724589063880075949723537 91293441797910056962292653)
  ·
    refine ⟨34235040674216271360859745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91293441797910056962292653 34235040674216271360859745)
    ·
      refine ⟨25676280505662203520644809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34235040674216271360859745 25676280505662203520644809)
      ·
        refine ⟨19257210379246652640483607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25676280505662203520644809 19257210379246652640483607)
        ·
          refine ⟨28885815568869978960725411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19257210379246652640483607 28885815568869978960725411)
          ·
            refine ⟨43328723353304968441088117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28885815568869978960725411 43328723353304968441088117)
            ·
              refine ⟨4062067814372340791352011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43328723353304968441088117 4062067814372340791352011)
              ·
                refine ⟨6093101721558511187028017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4062067814372340791352011 6093101721558511187028017)
                ·
                  refine ⟨4569826291168883390271013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6093101721558511187028017 4569826291168883390271013)
                  ·
                    refine ⟨856842429594165635675815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4569826291168883390271013 856842429594165635675815)
                    ·
                      rfl

theorem cell23_5006084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_5006084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006084 prefixEnd_5006084 := by exact prefixLift 5006084
  have htrace : WordTrace (prefixWord ++ tailWord_5006084) baseStart_5006084 baseEnd_5006084 := by
    simpa [prefixWord, tailWord_5006084, baseEnd_5006084] using wordTrace_append hprefix tailTrace_5006084
  have hstable : (prefixWord ++ tailWord_5006084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006084).length < 2 ^ (prefixWord ++ tailWord_5006084).sum := by decide
  have hdescent : baseEnd_5006084 < baseStart_5006084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006087 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_5006087 : Nat := 118140960795 + 5006087 * 2 ^ 59
def prefixEnd_5006087 : Nat := 4983230072969 + 3 ^ 40 * 5006087 * 2
def baseEnd_5006087 : Nat := 2570528829224460395289931

theorem tailTrace_5006087 : CollatzResearch.WordTrace tailWord_5006087 prefixEnd_5006087 2570528829224460395289931 := by
  unfold tailWord_5006087
  simp only [CollatzResearch.WordTrace]
  refine ⟨182586993014809245436944515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121724662009872830291296343 182586993014809245436944515)
  ·
    refine ⟨273880489522213868155416773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182586993014809245436944515 273880489522213868155416773)
    ·
      refine ⟨51352591785415100279140645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273880489522213868155416773 51352591785415100279140645)
      ·
        refine ⟨9628610959765331302338871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51352591785415100279140645 9628610959765331302338871)
        ·
          refine ⟨14442916439647996953508307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9628610959765331302338871 14442916439647996953508307)
          ·
            refine ⟨21664374659471995430262461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14442916439647996953508307 21664374659471995430262461)
            ·
              refine ⟨8124140497301998286348423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21664374659471995430262461 8124140497301998286348423)
              ·
                refine ⟨12186210745952997429522635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8124140497301998286348423 12186210745952997429522635)
                ·
                  refine ⟨18279316118929496144283953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12186210745952997429522635 18279316118929496144283953)
                  ·
                    refine ⟨13709487089197122108212965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18279316118929496144283953 13709487089197122108212965)
                    ·
                      refine ⟨2570528829224460395289931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13709487089197122108212965 2570528829224460395289931)
                      ·
                        rfl

theorem cell23_5006087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_5006087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006087 prefixEnd_5006087 := by exact prefixLift 5006087
  have htrace : WordTrace (prefixWord ++ tailWord_5006087) baseStart_5006087 baseEnd_5006087 := by
    simpa [prefixWord, tailWord_5006087, baseEnd_5006087] using wordTrace_append hprefix tailTrace_5006087
  have hstable : (prefixWord ++ tailWord_5006087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006087).length < 2 ^ (prefixWord ++ tailWord_5006087).sum := by decide
  have hdescent : baseEnd_5006087 < baseStart_5006087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006108 : List Nat := [2, 2, 3, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_5006108 : Nat := 118140960795 + 5006108 * 2 ^ 59
def prefixEnd_5006108 : Nat := 4983230072969 + 3 ^ 40 * 5006108 * 2
def baseEnd_5006108 : Nat := 2570539612318204813127335

theorem tailTrace_5006108 : CollatzResearch.WordTrace tailWord_5006108 prefixEnd_5006108 2570539612318204813127335 := by
  unfold tailWord_5006108
  simp only [CollatzResearch.WordTrace]
  refine ⟨91293879473866583011729489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121725172631822110682305985 91293879473866583011729489)
  ·
    refine ⟨68470409605399937258797117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91293879473866583011729489 68470409605399937258797117)
    ·
      refine ⟨25676403602024976472048919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68470409605399937258797117 25676403602024976472048919)
      ·
        refine ⟨38514605403037464708073379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25676403602024976472048919 38514605403037464708073379)
        ·
          refine ⟨57771908104556197062110069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38514605403037464708073379 57771908104556197062110069)
          ·
            refine ⟨5416116384802143474572819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57771908104556197062110069 5416116384802143474572819)
            ·
              refine ⟨8124174577203215211859229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5416116384802143474572819 8124174577203215211859229)
              ·
                refine ⟨3046565466451205704447211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8124174577203215211859229 3046565466451205704447211)
                ·
                  refine ⟨4569848199676808556670817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046565466451205704447211 4569848199676808556670817)
                  ·
                    refine ⟨3427386149757606417503113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4569848199676808556670817 3427386149757606417503113)
                    ·
                      refine ⟨2570539612318204813127335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427386149757606417503113 2570539612318204813127335)
                      ·
                        rfl

theorem cell23_5006108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_5006108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006108 prefixEnd_5006108 := by exact prefixLift 5006108
  have htrace : WordTrace (prefixWord ++ tailWord_5006108) baseStart_5006108 baseEnd_5006108 := by
    simpa [prefixWord, tailWord_5006108, baseEnd_5006108] using wordTrace_append hprefix tailTrace_5006108
  have hstable : (prefixWord ++ tailWord_5006108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006108).length < 2 ^ (prefixWord ++ tailWord_5006108).sum := by decide
  have hdescent : baseEnd_5006108 < baseStart_5006108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006120 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5006120 : Nat := 118140960795 + 5006120 * 2 ^ 59
def prefixEnd_5006120 : Nat := 4983230072969 + 3 ^ 40 * 5006120 * 2
def baseEnd_5006120 : Nat := 2570545774086058766177279

theorem tailTrace_5006120 : CollatzResearch.WordTrace tailWord_5006120 prefixEnd_5006120 2570545774086058766177279 := by
  unfold tailWord_5006120
  simp only [CollatzResearch.WordTrace]
  refine ⟨91294098311844846036447907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121725464415793128048597209 91294098311844846036447907)
  ·
    refine ⟨136941147467767269054671861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91294098311844846036447907 136941147467767269054671861)
    ·
      refine ⟨12838232575103181473875487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136941147467767269054671861 12838232575103181473875487)
      ·
        refine ⟨19257348862654772210813231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12838232575103181473875487 19257348862654772210813231)
        ·
          refine ⟨28886023293982158316219847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19257348862654772210813231 28886023293982158316219847)
          ·
            refine ⟨43329034940973237474329771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28886023293982158316219847 43329034940973237474329771)
            ·
              refine ⟨64993552411459856211494657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43329034940973237474329771 64993552411459856211494657)
              ·
                refine ⟨48745164308594892158620993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64993552411459856211494657 48745164308594892158620993)
                ·
                  refine ⟨36558873231446169118965745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48745164308594892158620993 36558873231446169118965745)
                  ·
                    refine ⟨27419154923584626839224309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36558873231446169118965745 27419154923584626839224309)
                    ·
                      refine ⟨2570545774086058766177279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27419154923584626839224309 2570545774086058766177279)
                      ·
                        rfl

theorem cell23_5006120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5006120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006120 prefixEnd_5006120 := by exact prefixLift 5006120
  have htrace : WordTrace (prefixWord ++ tailWord_5006120) baseStart_5006120 baseEnd_5006120 := by
    simpa [prefixWord, tailWord_5006120, baseEnd_5006120] using wordTrace_append hprefix tailTrace_5006120
  have hstable : (prefixWord ++ tailWord_5006120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006120).length < 2 ^ (prefixWord ++ tailWord_5006120).sum := by decide
  have hdescent : baseEnd_5006120 < baseStart_5006120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006125 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5006125 : Nat := 118140960795 + 5006125 * 2 ^ 59
def prefixEnd_5006125 : Nat := 4983230072969 + 3 ^ 40 * 5006125 * 2
def baseEnd_5006125 : Nat := 2570548341489331246614757

theorem tailTrace_5006125 : CollatzResearch.WordTrace tailWord_5006125 prefixEnd_5006125 2570548341489331246614757 := by
  unfold tailWord_5006125
  simp only [CollatzResearch.WordTrace]
  refine ⟨182588378988671577926827829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121725585992447718617885219 182588378988671577926827829)
  ·
    refine ⟨17117660530187960430640109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182588378988671577926827829 17117660530187960430640109)
    ·
      refine ⟨6419122698820485161490041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17117660530187960430640109 6419122698820485161490041)
      ·
        refine ⟨4814342024115363871117531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6419122698820485161490041 4814342024115363871117531)
        ·
          refine ⟨7221513036173045806676297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814342024115363871117531 7221513036173045806676297)
          ·
            refine ⟨5416134777129784355007223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7221513036173045806676297 5416134777129784355007223)
            ·
              refine ⟨8124202165694676532510835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5416134777129784355007223 8124202165694676532510835)
              ·
                refine ⟨12186303248542014798766253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8124202165694676532510835 12186303248542014798766253)
                ·
                  refine ⟨4569863718203255549537345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12186303248542014798766253 4569863718203255549537345)
                  ·
                    refine ⟨3427397788652441662153009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4569863718203255549537345 3427397788652441662153009)
                    ·
                      refine ⟨2570548341489331246614757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427397788652441662153009 2570548341489331246614757)
                      ·
                        rfl

theorem cell23_5006125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5006125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006125 prefixEnd_5006125 := by exact prefixLift 5006125
  have htrace : WordTrace (prefixWord ++ tailWord_5006125) baseStart_5006125 baseEnd_5006125 := by
    simpa [prefixWord, tailWord_5006125, baseEnd_5006125] using wordTrace_append hprefix tailTrace_5006125
  have hstable : (prefixWord ++ tailWord_5006125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006125).length < 2 ^ (prefixWord ++ tailWord_5006125).sum := by decide
  have hdescent : baseEnd_5006125 < baseStart_5006125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006130 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_5006130 : Nat := 118140960795 + 5006130 * 2 ^ 59
def prefixEnd_5006130 : Nat := 4983230072969 + 3 ^ 40 * 5006130 * 2
def baseEnd_5006130 : Nat := 2570550908892603727052233

theorem tailTrace_5006130 : CollatzResearch.WordTrace tailWord_5006130 prefixEnd_5006130 2570550908892603727052233 := by
  unfold tailWord_5006130
  simp only [CollatzResearch.WordTrace]
  refine ⟨45647140338413365945189961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121725707569102309187173229 45647140338413365945189961)
  ·
    refine ⟨34235355253810024458892471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45647140338413365945189961 34235355253810024458892471)
    ·
      refine ⟨51353032880715036688338707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34235355253810024458892471 51353032880715036688338707)
      ·
        refine ⟨77029549321072555032508061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51353032880715036688338707 77029549321072555032508061)
        ·
          refine ⟨28886080995402208137190523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77029549321072555032508061 28886080995402208137190523)
          ·
            refine ⟨43329121493103312205785785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28886080995402208137190523 43329121493103312205785785)
            ·
              refine ⟨32496841119827484154339339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43329121493103312205785785 32496841119827484154339339)
              ·
                refine ⟨48745261679741226231509009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32496841119827484154339339 48745261679741226231509009)
                ·
                  refine ⟨36558946259805919673631757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48745261679741226231509009 36558946259805919673631757)
                  ·
                    refine ⟨13709604847427219877611909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36558946259805919673631757 13709604847427219877611909)
                    ·
                      refine ⟨2570550908892603727052233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13709604847427219877611909 2570550908892603727052233)
                      ·
                        rfl

theorem cell23_5006130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_5006130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006130 prefixEnd_5006130 := by exact prefixLift 5006130
  have htrace : WordTrace (prefixWord ++ tailWord_5006130) baseStart_5006130 baseEnd_5006130 := by
    simpa [prefixWord, tailWord_5006130, baseEnd_5006130] using wordTrace_append hprefix tailTrace_5006130
  have hstable : (prefixWord ++ tailWord_5006130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006130).length < 2 ^ (prefixWord ++ tailWord_5006130).sum := by decide
  have hdescent : baseEnd_5006130 < baseStart_5006130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006141 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5006141 : Nat := 118140960795 + 5006141 * 2 ^ 59
def prefixEnd_5006141 : Nat := 4983230072969 + 3 ^ 40 * 5006141 * 2
def baseEnd_5006141 : Nat := 2570556557179803184014683

theorem tailTrace_5006141 : CollatzResearch.WordTrace tailWord_5006141 prefixEnd_5006141 2570556557179803184014683 := by
  unfold tailWord_5006141
  simp only [CollatzResearch.WordTrace]
  refine ⟨182588962556613612659410277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121725975037742408439606851 182588962556613612659410277)
  ·
    refine ⟨34235430479365052373639427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182588962556613612659410277 34235430479365052373639427)
    ·
      refine ⟨51353145719047578560459141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34235430479365052373639427 51353145719047578560459141)
      ·
        refine ⟨9628714822321420980086089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51353145719047578560459141 9628714822321420980086089)
        ·
          refine ⟨7221536116741065735064567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9628714822321420980086089 7221536116741065735064567)
          ·
            refine ⟨10832304175111598602596851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7221536116741065735064567 10832304175111598602596851)
            ·
              refine ⟨16248456262667397903895277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10832304175111598602596851 16248456262667397903895277)
              ·
                refine ⟨6093171098500274213960729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16248456262667397903895277 6093171098500274213960729)
                ·
                  refine ⟨4569878323875205660470547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6093171098500274213960729 4569878323875205660470547)
                  ·
                    refine ⟨6854817485812808490705821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4569878323875205660470547 6854817485812808490705821)
                    ·
                      refine ⟨2570556557179803184014683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6854817485812808490705821 2570556557179803184014683)
                      ·
                        rfl

theorem cell23_5006141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5006141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006141 prefixEnd_5006141 := by exact prefixLift 5006141
  have htrace : WordTrace (prefixWord ++ tailWord_5006141) baseStart_5006141 baseEnd_5006141 := by
    simpa [prefixWord, tailWord_5006141, baseEnd_5006141] using wordTrace_append hprefix tailTrace_5006141
  have hstable : (prefixWord ++ tailWord_5006141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006141).length < 2 ^ (prefixWord ++ tailWord_5006141).sum := by decide
  have hdescent : baseEnd_5006141 < baseStart_5006141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006147 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 1, 4, 2]
def baseStart_5006147 : Nat := 118140960795 + 5006147 * 2 ^ 59
def prefixEnd_5006147 : Nat := 4983230072969 + 3 ^ 40 * 5006147 * 2
def baseEnd_5006147 : Nat := 2570559638063730160539655

theorem tailTrace_5006147 : CollatzResearch.WordTrace tailWord_5006147 prefixEnd_5006147 2570559638063730160539655 := by
  unfold tailWord_5006147
  simp only [CollatzResearch.WordTrace]
  refine ⟨182589181394591875684128695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121726120929727917122752463 182589181394591875684128695)
  ·
    refine ⟨273883772091887813526193043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182589181394591875684128695 273883772091887813526193043)
    ·
      refine ⟨410825658137831720289289565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273883772091887813526193043 410825658137831720289289565)
      ·
        refine ⟨154059621801686895108483587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410825658137831720289289565 154059621801686895108483587)
        ·
          refine ⟨231089432702530342662725381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154059621801686895108483587 231089432702530342662725381)
          ·
            refine ⟨43329268631724439249261009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231089432702530342662725381 43329268631724439249261009)
            ·
              refine ⟨32496951473793329436945757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43329268631724439249261009 32496951473793329436945757)
              ·
                refine ⟨12186356802672498538854659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32496951473793329436945757 12186356802672498538854659)
                ·
                  refine ⟨18279535204008747808281989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12186356802672498538854659 18279535204008747808281989)
                  ·
                    refine ⟨3427412850751640214052873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18279535204008747808281989 3427412850751640214052873)
                    ·
                      refine ⟨2570559638063730160539655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427412850751640214052873 2570559638063730160539655)
                      ·
                        rfl

theorem cell23_5006147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_5006147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006147 prefixEnd_5006147 := by exact prefixLift 5006147
  have htrace : WordTrace (prefixWord ++ tailWord_5006147) baseStart_5006147 baseEnd_5006147 := by
    simpa [prefixWord, tailWord_5006147, baseEnd_5006147] using wordTrace_append hprefix tailTrace_5006147
  have hstable : (prefixWord ++ tailWord_5006147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006147).length < 2 ^ (prefixWord ++ tailWord_5006147).sum := by decide
  have hdescent : baseEnd_5006147 < baseStart_5006147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006197 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_5006197 : Nat := 118140960795 + 5006197 * 2 ^ 59
def prefixEnd_5006197 : Nat := 4983230072969 + 3 ^ 40 * 5006197 * 2
def baseEnd_5006197 : Nat := 2570585312096454964914425

theorem tailTrace_5006197 : CollatzResearch.WordTrace tailWord_5006197 prefixEnd_5006197 2570585312096454964914425 := by
  unfold tailWord_5006197
  simp only [CollatzResearch.WordTrace]
  refine ⟨182591005044410734223448845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121727336696273822815632563 182591005044410734223448845)
  ·
    refine ⟨68471626891654025333793317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182591005044410734223448845 68471626891654025333793317)
    ·
      refine ⟨12838430042185129750086247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68471626891654025333793317 12838430042185129750086247)
      ·
        refine ⟨19257645063277694625129371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12838430042185129750086247 19257645063277694625129371)
        ·
          refine ⟨28886467594916541937694057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19257645063277694625129371 28886467594916541937694057)
          ·
            refine ⟨21664850696187406453270543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28886467594916541937694057 21664850696187406453270543)
            ·
              refine ⟨32497276044281109679905815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21664850696187406453270543 32497276044281109679905815)
              ·
                refine ⟨48745914066421664519858723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32497276044281109679905815 48745914066421664519858723)
                ·
                  refine ⟨73118871099632496779788085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48745914066421664519858723 73118871099632496779788085)
                  ·
                    refine ⟨6854894165590546573105133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73118871099632496779788085 6854894165590546573105133)
                    ·
                      refine ⟨2570585312096454964914425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6854894165590546573105133 2570585312096454964914425)
                      ·
                        rfl

theorem cell23_5006197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_5006197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006197 prefixEnd_5006197 := by exact prefixLift 5006197
  have htrace : WordTrace (prefixWord ++ tailWord_5006197) baseStart_5006197 baseEnd_5006197 := by
    simpa [prefixWord, tailWord_5006197, baseEnd_5006197] using wordTrace_append hprefix tailTrace_5006197
  have hstable : (prefixWord ++ tailWord_5006197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006197).length < 2 ^ (prefixWord ++ tailWord_5006197).sum := by decide
  have hdescent : baseEnd_5006197 < baseStart_5006197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006198 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5006198 : Nat := 118140960795 + 5006198 * 2 ^ 59
def prefixEnd_5006198 : Nat := 4983230072969 + 3 ^ 40 * 5006198 * 2
def baseEnd_5006198 : Nat := 2570585825577109461001921

theorem tailTrace_5006198 : CollatzResearch.WordTrace tailWord_5006198 prefixEnd_5006198 2570585825577109461001921 := by
  unfold tailWord_5006198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411940094837944462139703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121727361011604740929490165 11411940094837944462139703)
  ·
    refine ⟨17117910142256916693209555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11411940094837944462139703 17117910142256916693209555)
    ·
      refine ⟨25676865213385375039814333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17117910142256916693209555 25676865213385375039814333)
      ·
        refine ⟨9628824455019515639930375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25676865213385375039814333 9628824455019515639930375)
        ·
          refine ⟨14443236682529273459895563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9628824455019515639930375 14443236682529273459895563)
          ·
            refine ⟨21664855023793910189843345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14443236682529273459895563 21664855023793910189843345)
            ·
              refine ⟨16248641267845432642382509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21664855023793910189843345 16248641267845432642382509)
              ·
                refine ⟨6093240475442037240893441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16248641267845432642382509 6093240475442037240893441)
                ·
                  refine ⟨4569930356581527930670081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6093240475442037240893441 4569930356581527930670081)
                  ·
                    refine ⟨3427447767436145948002561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4569930356581527930670081 3427447767436145948002561)
                    ·
                      refine ⟨2570585825577109461001921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427447767436145948002561 2570585825577109461001921)
                      ·
                        rfl

theorem cell23_5006198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5006198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006198 prefixEnd_5006198 := by exact prefixLift 5006198
  have htrace : WordTrace (prefixWord ++ tailWord_5006198) baseStart_5006198 baseEnd_5006198 := by
    simpa [prefixWord, tailWord_5006198, baseEnd_5006198] using wordTrace_append hprefix tailTrace_5006198
  have hstable : (prefixWord ++ tailWord_5006198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006198).length < 2 ^ (prefixWord ++ tailWord_5006198).sum := by decide
  have hdescent : baseEnd_5006198 < baseStart_5006198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006217 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 2, 5]
def baseStart_5006217 : Nat := 118140960795 + 5006217 * 2 ^ 59
def prefixEnd_5006217 : Nat := 4983230072969 + 3 ^ 40 * 5006217 * 2
def baseEnd_5006217 : Nat := 856865193903181628888111

theorem tailTrace_5006217 : CollatzResearch.WordTrace tailWord_5006217 prefixEnd_5006217 856865193903181628888111 := by
  unfold tailWord_5006217
  simp only [CollatzResearch.WordTrace]
  refine ⟨182591734504338277639176905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121727823002892185092784603 182591734504338277639176905)
  ·
    refine ⟨136943800878253708229382679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182591734504338277639176905 136943800878253708229382679)
    ·
      refine ⟨205415701317380562344074019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136943800878253708229382679 205415701317380562344074019)
      ·
        refine ⟨308123551976070843516111029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205415701317380562344074019 308123551976070843516111029)
        ·
          refine ⟨28886582997756641579635409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 308123551976070843516111029 28886582997756641579635409)
          ·
            refine ⟨21664937248317481184726557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28886582997756641579635409 21664937248317481184726557)
            ·
              refine ⟨8124351468119055444272459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21664937248317481184726557 8124351468119055444272459)
              ·
                refine ⟨12186527202178583166408689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8124351468119055444272459 12186527202178583166408689)
                ·
                  refine ⟨9139895401633937374806517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12186527202178583166408689 9139895401633937374806517)
                  ·
                    refine ⟨856865193903181628888111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9139895401633937374806517 856865193903181628888111)
                    ·
                      rfl

theorem cell23_5006217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_5006217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006217 prefixEnd_5006217 := by exact prefixLift 5006217
  have htrace : WordTrace (prefixWord ++ tailWord_5006217) baseStart_5006217 baseEnd_5006217 := by
    simpa [prefixWord, tailWord_5006217, baseEnd_5006217] using wordTrace_append hprefix tailTrace_5006217
  have hstable : (prefixWord ++ tailWord_5006217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006217).length < 2 ^ (prefixWord ++ tailWord_5006217).sum := by decide
  have hdescent : baseEnd_5006217 < baseStart_5006217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006237 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_5006237 : Nat := 118140960795 + 5006237 * 2 ^ 59
def prefixEnd_5006237 : Nat := 4983230072969 + 3 ^ 40 * 5006237 * 2
def baseEnd_5006237 : Nat := 2570605851322634808414241

theorem tailTrace_5006237 : CollatzResearch.WordTrace tailWord_5006237 prefixEnd_5006237 2570605851322634808414241 := by
  unfold tailWord_5006237
  simp only [CollatzResearch.WordTrace]
  refine ⟨182592463964265821054904965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121728309309510547369936643 182592463964265821054904965)
  ·
    refine ⟨34236086993299841447794681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182592463964265821054904965 34236086993299841447794681)
    ·
      refine ⟨25677065244974881085846011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34236086993299841447794681 25677065244974881085846011)
      ·
        refine ⟨38515597867462321628769017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25677065244974881085846011 38515597867462321628769017)
        ·
          refine ⟨28886698400596741221576763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38515597867462321628769017 28886698400596741221576763)
          ·
            refine ⟨43330047600895111832365145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28886698400596741221576763 43330047600895111832365145)
            ·
              refine ⟨32497535700671333874273859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43330047600895111832365145 32497535700671333874273859)
              ·
                refine ⟨48746303551007000811410789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32497535700671333874273859 48746303551007000811410789)
                ·
                  refine ⟨9139931915813812652139523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48746303551007000811410789 9139931915813812652139523)
                  ·
                    refine ⟨13709897873720718978209285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9139931915813812652139523 13709897873720718978209285)
                    ·
                      refine ⟨2570605851322634808414241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13709897873720718978209285 2570605851322634808414241)
                      ·
                        rfl

theorem cell23_5006237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_5006237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006237 prefixEnd_5006237 := by exact prefixLift 5006237
  have htrace : WordTrace (prefixWord ++ tailWord_5006237) baseStart_5006237 baseEnd_5006237 := by
    simpa [prefixWord, tailWord_5006237, baseEnd_5006237] using wordTrace_append hprefix tailTrace_5006237
  have hstable : (prefixWord ++ tailWord_5006237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006237).length < 2 ^ (prefixWord ++ tailWord_5006237).sum := by decide
  have hdescent : baseEnd_5006237 < baseStart_5006237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006240 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_5006240 : Nat := 118140960795 + 5006240 * 2 ^ 59
def prefixEnd_5006240 : Nat := 4983230072969 + 3 ^ 40 * 5006240 * 2
def baseEnd_5006240 : Nat := 2570607391764598296676727

theorem tailTrace_5006240 : CollatzResearch.WordTrace tailWord_5006240 prefixEnd_5006240 2570607391764598296676727 := by
  unfold tailWord_5006240
  simp only [CollatzResearch.WordTrace]
  refine ⟨91296286691627476283632087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121728382255503301711509449 91296286691627476283632087)
  ·
    refine ⟨136944430037441214425448131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91296286691627476283632087 136944430037441214425448131)
    ·
      refine ⟨205416645056161821638172197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136944430037441214425448131 205416645056161821638172197)
      ·
        refine ⟨38515620948030341557157287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205416645056161821638172197 38515620948030341557157287)
        ·
          refine ⟨57773431422045512335735931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38515620948030341557157287 57773431422045512335735931)
          ·
            refine ⟨86660147133068268503603897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57773431422045512335735931 86660147133068268503603897)
            ·
              refine ⟨64995110349801201377702923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86660147133068268503603897 64995110349801201377702923)
              ·
                refine ⟨97492665524701802066554385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64995110349801201377702923 97492665524701802066554385)
                ·
                  refine ⟨73119499143526351549915789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97492665524701802066554385 73119499143526351549915789)
                  ·
                    refine ⟨27419812178822381831218421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73119499143526351549915789 27419812178822381831218421)
                    ·
                      refine ⟨2570607391764598296676727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27419812178822381831218421 2570607391764598296676727)
                      ·
                        rfl

theorem cell23_5006240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_5006240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006240 prefixEnd_5006240 := by exact prefixLift 5006240
  have htrace : WordTrace (prefixWord ++ tailWord_5006240) baseStart_5006240 baseEnd_5006240 := by
    simpa [prefixWord, tailWord_5006240, baseEnd_5006240] using wordTrace_append hprefix tailTrace_5006240
  have hstable : (prefixWord ++ tailWord_5006240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006240).length < 2 ^ (prefixWord ++ tailWord_5006240).sum := by decide
  have hdescent : baseEnd_5006240 < baseStart_5006240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006294 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_5006294 : Nat := 118140960795 + 5006294 * 2 ^ 59
def prefixEnd_5006294 : Nat := 4983230072969 + 3 ^ 40 * 5006294 * 2
def baseEnd_5006294 : Nat := 285626124413326787266831

theorem tailTrace_5006294 : CollatzResearch.WordTrace tailWord_5006294 prefixEnd_5006294 285626124413326787266831 := by
  unfold tailWord_5006294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11412158932816207486858121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121729695283372879859819957 11412158932816207486858121)
  ·
    refine ⟨8559119199612155615143591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11412158932816207486858121 8559119199612155615143591)
    ·
      refine ⟨12838678799418233422715387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8559119199612155615143591 12838678799418233422715387)
      ·
        refine ⟨19258018199127350134073081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12838678799418233422715387 19258018199127350134073081)
        ·
          refine ⟨14443513649345512600554811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19258018199127350134073081 14443513649345512600554811)
          ·
            refine ⟨21665270474018268900832217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14443513649345512600554811 21665270474018268900832217)
            ·
              refine ⟨16248952855513701675624163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21665270474018268900832217 16248952855513701675624163)
              ·
                refine ⟨24373429283270552513436245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16248952855513701675624163 24373429283270552513436245)
                ·
                  refine ⟨285626124413326787266831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24373429283270552513436245 285626124413326787266831)
                  ·
                    rfl

theorem cell23_5006294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_5006294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006294 prefixEnd_5006294 := by exact prefixLift 5006294
  have htrace : WordTrace (prefixWord ++ tailWord_5006294) baseStart_5006294 baseEnd_5006294 := by
    simpa [prefixWord, tailWord_5006294, baseEnd_5006294] using wordTrace_append hprefix tailTrace_5006294
  have hstable : (prefixWord ++ tailWord_5006294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006294).length < 2 ^ (prefixWord ++ tailWord_5006294).sum := by decide
  have hdescent : baseEnd_5006294 < baseStart_5006294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006298 : List Nat := [3, 1, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_5006298 : Nat := 118140960795 + 5006298 * 2 ^ 59
def prefixEnd_5006298 : Nat := 4983230072969 + 3 ^ 40 * 5006298 * 2
def baseEnd_5006298 : Nat := 856879057880853023250487

theorem tailTrace_5006298 : CollatzResearch.WordTrace tailWord_5006298 prefixEnd_5006298 856879057880853023250487 := by
  unfold tailWord_5006298
  simp only [CollatzResearch.WordTrace]
  refine ⟨45648672204261207118218887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121729792544696552315250365 45648672204261207118218887)
  ·
    refine ⟨68473008306391810677328331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45648672204261207118218887 68473008306391810677328331)
    ·
      refine ⟨102709512459587716015992497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68473008306391810677328331 102709512459587716015992497)
      ·
        refine ⟨77032134344690787011994373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102709512459587716015992497 77032134344690787011994373)
        ·
          refine ⟨14443525189629522564748945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77032134344690787011994373 14443525189629522564748945)
          ·
            refine ⟨10832643892222141923561709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14443525189629522564748945 10832643892222141923561709)
            ·
              refine ⟨4062241459583303221335641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10832643892222141923561709 4062241459583303221335641)
              ·
                refine ⟨3046681094687477416001731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4062241459583303221335641 3046681094687477416001731)
                ·
                  refine ⟨4570021642031216124002597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046681094687477416001731 4570021642031216124002597)
                  ·
                    refine ⟨856879057880853023250487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4570021642031216124002597 856879057880853023250487)
                    ·
                      rfl

theorem cell23_5006298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_5006298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006298 prefixEnd_5006298 := by exact prefixLift 5006298
  have htrace : WordTrace (prefixWord ++ tailWord_5006298) baseStart_5006298 baseEnd_5006298 := by
    simpa [prefixWord, tailWord_5006298, baseEnd_5006298] using wordTrace_append hprefix tailTrace_5006298
  have hstable : (prefixWord ++ tailWord_5006298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006298).length < 2 ^ (prefixWord ++ tailWord_5006298).sum := by decide
  have hdescent : baseEnd_5006298 < baseStart_5006298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006307 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 3, 5]
def baseStart_5006307 : Nat := 118140960795 + 5006307 * 2 ^ 59
def prefixEnd_5006307 : Nat := 4983230072969 + 3 ^ 40 * 5006307 * 2
def baseEnd_5006307 : Nat := 856880598322816511512973

theorem tailTrace_5006307 : CollatzResearch.WordTrace tailWord_5006307 prefixEnd_5006307 856880598322816511512973 := by
  unfold tailWord_5006307
  simp only [CollatzResearch.WordTrace]
  refine ⟨182595017074012223009953175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121730011382674815339968783 182595017074012223009953175)
  ·
    refine ⟨273892525611018334514929763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182595017074012223009953175 273892525611018334514929763)
    ·
      refine ⟨410838788416527501772394645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273892525611018334514929763 410838788416527501772394645)
      ·
        refine ⟨19258068207024726645580999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 410838788416527501772394645 19258068207024726645580999)
        ·
          refine ⟨28887102310537089968371499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19258068207024726645580999 28887102310537089968371499)
          ·
            refine ⟨43330653465805634952557249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28887102310537089968371499 43330653465805634952557249)
            ·
              refine ⟨32497990099354226214417937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43330653465805634952557249 32497990099354226214417937)
              ·
                refine ⟨24373492574515669660813453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32497990099354226214417937 24373492574515669660813453)
                ·
                  refine ⟨9140059715443376122805045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24373492574515669660813453 9140059715443376122805045)
                  ·
                    refine ⟨856880598322816511512973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9140059715443376122805045 856880598322816511512973)
                    ·
                      rfl

theorem cell23_5006307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 5].length) (baseStart_5006307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006307 prefixEnd_5006307 := by exact prefixLift 5006307
  have htrace : WordTrace (prefixWord ++ tailWord_5006307) baseStart_5006307 baseEnd_5006307 := by
    simpa [prefixWord, tailWord_5006307, baseEnd_5006307] using wordTrace_append hprefix tailTrace_5006307
  have hstable : (prefixWord ++ tailWord_5006307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006307).length < 2 ^ (prefixWord ++ tailWord_5006307).sum := by decide
  have hdescent : baseEnd_5006307 < baseStart_5006307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006311 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 6]
def baseStart_5006311 : Nat := 118140960795 + 5006311 * 2 ^ 59
def prefixEnd_5006311 : Nat := 4983230072969 + 3 ^ 40 * 5006311 * 2
def baseEnd_5006311 : Nat := 285627094321229724320989

theorem tailTrace_5006311 : CollatzResearch.WordTrace tailWord_5006311 prefixEnd_5006311 285627094321229724320989 := by
  unfold tailWord_5006311
  simp only [CollatzResearch.WordTrace]
  refine ⟨182595162965997731693098787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121730108643998487795399191 182595162965997731693098787)
  ·
    refine ⟨273892744448996597539648181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182595162965997731693098787 273892744448996597539648181)
    ·
      refine ⟨25677444792093431019342017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 273892744448996597539648181 25677444792093431019342017)
      ·
        refine ⟨19258083594070073264506513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25677444792093431019342017 19258083594070073264506513)
        ·
          refine ⟨14443562695552554948379885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19258083594070073264506513 14443562695552554948379885)
          ·
            refine ⟨5416336010832208105642457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14443562695552554948379885 5416336010832208105642457)
            ·
              refine ⟨4062252008124156079231843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5416336010832208105642457 4062252008124156079231843)
              ·
                refine ⟨6093378012186234118847765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4062252008124156079231843 6093378012186234118847765)
                ·
                  refine ⟨285627094321229724320989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6093378012186234118847765 285627094321229724320989)
                  ·
                    rfl

theorem cell23_5006311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 6].length) (baseStart_5006311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006311 prefixEnd_5006311 := by exact prefixLift 5006311
  have htrace : WordTrace (prefixWord ++ tailWord_5006311) baseStart_5006311 baseEnd_5006311 := by
    simpa [prefixWord, tailWord_5006311, baseEnd_5006311] using wordTrace_append hprefix tailTrace_5006311
  have hstable : (prefixWord ++ tailWord_5006311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006311).length < 2 ^ (prefixWord ++ tailWord_5006311).sum := by decide
  have hdescent : baseEnd_5006311 < baseStart_5006311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006337 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 3, 6]
def baseStart_5006337 : Nat := 118140960795 + 5006337 * 2 ^ 59
def prefixEnd_5006337 : Nat := 4983230072969 + 3 ^ 40 * 5006337 * 2
def baseEnd_5006337 : Nat := 856885733129361472387927

theorem tailTrace_5006337 : CollatzResearch.WordTrace tailWord_5006337 prefixEnd_5006337 856885733129361472387927 := by
  unfold tailWord_5006337
  simp only [CollatzResearch.WordTrace]
  refine ⟨182596111263903538133545265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121730740842602358755696843 182596111263903538133545265)
  ·
    refine ⟨136947083447927653600158949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182596111263903538133545265 136947083447927653600158949)
    ·
      refine ⟨25677578146486435050029803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136947083447927653600158949 25677578146486435050029803)
      ·
        refine ⟨38516367219729652575044705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25677578146486435050029803 38516367219729652575044705)
        ·
          refine ⟨28887275414797239431283529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38516367219729652575044705 28887275414797239431283529)
          ·
            refine ⟨21665456561097929573462647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28887275414797239431283529 21665456561097929573462647)
            ·
              refine ⟨32498184841646894360193971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21665456561097929573462647 32498184841646894360193971)
              ·
                refine ⟨48747277262470341540290957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32498184841646894360193971 48747277262470341540290957)
                ·
                  refine ⟨18280228973426378077609109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48747277262470341540290957 18280228973426378077609109)
                  ·
                    refine ⟨856885733129361472387927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18280228973426378077609109 856885733129361472387927)
                    ·
                      rfl

theorem cell23_5006337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_5006337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006337 prefixEnd_5006337 := by exact prefixLift 5006337
  have htrace : WordTrace (prefixWord ++ tailWord_5006337) baseStart_5006337 baseEnd_5006337 := by
    simpa [prefixWord, tailWord_5006337, baseEnd_5006337] using wordTrace_append hprefix tailTrace_5006337
  have hstable : (prefixWord ++ tailWord_5006337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006337).length < 2 ^ (prefixWord ++ tailWord_5006337).sum := by decide
  have hdescent : baseEnd_5006337 < baseStart_5006337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006367 : List Nat := [1, 1, 2, 4, 1, 3, 3, 8]
def baseStart_5006367 : Nat := 118140960795 + 5006367 * 2 ^ 59
def prefixEnd_5006367 : Nat := 4983230072969 + 3 ^ 40 * 5006367 * 2
def baseEnd_5006367 : Nat := 95210096437322937029209

theorem tailTrace_5006367 : CollatzResearch.WordTrace tailWord_5006367 prefixEnd_5006367 95210096437322937029209 := by
  unfold tailWord_5006367
  simp only [CollatzResearch.WordTrace]
  refine ⟨182597205453794853257137355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121731470302529902171424903 182597205453794853257137355)
  ·
    refine ⟨273895808180692279885706033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182597205453794853257137355 273895808180692279885706033)
    ·
      refine ⟨205421856135519209914279525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273895808180692279885706033 205421856135519209914279525)
      ·
        refine ⟨38516598025409851858927411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205421856135519209914279525 38516598025409851858927411)
        ·
          refine ⟨57774897038114777788391117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38516598025409851858927411 57774897038114777788391117)
          ·
            refine ⟨21665586389293041670646669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57774897038114777788391117 21665586389293041670646669)
            ·
              refine ⟨8124594895984890626492501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21665586389293041670646669 8124594895984890626492501)
              ·
                refine ⟨95210096437322937029209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8124594895984890626492501 95210096437322937029209)
                ·
                  rfl

theorem cell23_5006367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 8].length) (baseStart_5006367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006367 prefixEnd_5006367 := by exact prefixLift 5006367
  have htrace : WordTrace (prefixWord ++ tailWord_5006367) baseStart_5006367 baseEnd_5006367 := by
    simpa [prefixWord, tailWord_5006367, baseEnd_5006367] using wordTrace_append hprefix tailTrace_5006367
  have hstable : (prefixWord ++ tailWord_5006367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006367).length < 2 ^ (prefixWord ++ tailWord_5006367).sum := by decide
  have hdescent : baseEnd_5006367 < baseStart_5006367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006394 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_5006394 : Nat := 118140960795 + 5006394 * 2 ^ 59
def prefixEnd_5006394 : Nat := 4983230072969 + 3 ^ 40 * 5006394 * 2
def baseEnd_5006394 : Nat := 2570686467785390694151019

theorem tailTrace_5006394 : CollatzResearch.WordTrace tailWord_5006394 prefixEnd_5006394 2570686467785390694151019 := by
  unfold tailWord_5006394
  simp only [CollatzResearch.WordTrace]
  refine ⟨45649547556174259217092559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121732126816464691245580157 45649547556174259217092559)
  ·
    refine ⟨68474321334261388825638839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45649547556174259217092559 68474321334261388825638839)
    ·
      refine ⟨102711482001392083238458259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68474321334261388825638839 102711482001392083238458259)
      ·
        refine ⟨154067223002088124857687389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102711482001392083238458259 154067223002088124857687389)
        ·
          refine ⟨57775208625783046821632771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154067223002088124857687389 57775208625783046821632771)
          ·
            refine ⟨86662812938674570232449157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57775208625783046821632771 86662812938674570232449157)
            ·
              refine ⟨16249277426001481918584217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86662812938674570232449157 16249277426001481918584217)
              ·
                refine ⟨12186958069501111438938163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16249277426001481918584217 12186958069501111438938163)
                ·
                  refine ⟨18280437104251667158407245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12186958069501111438938163 18280437104251667158407245)
                  ·
                    refine ⟨6855163914094375184402717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18280437104251667158407245 6855163914094375184402717)
                    ·
                      refine ⟨2570686467785390694151019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6855163914094375184402717 2570686467785390694151019)
                      ·
                        rfl

theorem cell23_5006394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_5006394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006394 prefixEnd_5006394 := by exact prefixLift 5006394
  have htrace : WordTrace (prefixWord ++ tailWord_5006394) baseStart_5006394 baseEnd_5006394 := by
    simpa [prefixWord, tailWord_5006394, baseEnd_5006394] using wordTrace_append hprefix tailTrace_5006394
  have hstable : (prefixWord ++ tailWord_5006394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006394).length < 2 ^ (prefixWord ++ tailWord_5006394).sum := by decide
  have hdescent : baseEnd_5006394 < baseStart_5006394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006398 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5006398 : Nat := 118140960795 + 5006398 * 2 ^ 59
def prefixEnd_5006398 : Nat := 4983230072969 + 3 ^ 40 * 5006398 * 2
def baseEnd_5006398 : Nat := 2570688521708008678501001

theorem tailTrace_5006398 : CollatzResearch.WordTrace tailWord_5006398 prefixEnd_5006398 2570688521708008678501001 := by
  unfold tailWord_5006398
  simp only [CollatzResearch.WordTrace]
  refine ⟨22824792014585318193939481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121732224077788363701010565 22824792014585318193939481)
  ·
    refine ⟨17118594010938988645454611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22824792014585318193939481 17118594010938988645454611)
    ·
      refine ⟨25677891016408482968181917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17118594010938988645454611 25677891016408482968181917)
      ·
        refine ⟨9629209131153181113068219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25677891016408482968181917 9629209131153181113068219)
        ·
          refine ⟨14443813696729771669602329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9629209131153181113068219 14443813696729771669602329)
          ·
            refine ⟨10832860272547328752201747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14443813696729771669602329 10832860272547328752201747)
            ·
              refine ⟨16249290408820993128302621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10832860272547328752201747 16249290408820993128302621)
              ·
                refine ⟨6093483903307872423113483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16249290408820993128302621 6093483903307872423113483)
                ·
                  refine ⟨9140225854961808634670225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6093483903307872423113483 9140225854961808634670225)
                  ·
                    refine ⟨6855169391221356476002669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9140225854961808634670225 6855169391221356476002669)
                    ·
                      refine ⟨2570688521708008678501001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6855169391221356476002669 2570688521708008678501001)
                      ·
                        rfl

theorem cell23_5006398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5006398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006398 prefixEnd_5006398 := by exact prefixLift 5006398
  have htrace : WordTrace (prefixWord ++ tailWord_5006398) baseStart_5006398 baseEnd_5006398 := by
    simpa [prefixWord, tailWord_5006398, baseEnd_5006398] using wordTrace_append hprefix tailTrace_5006398
  have hstable : (prefixWord ++ tailWord_5006398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006398).length < 2 ^ (prefixWord ++ tailWord_5006398).sum := by decide
  have hdescent : baseEnd_5006398 < baseStart_5006398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006417 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_5006417 : Nat := 118140960795 + 5006417 * 2 ^ 59
def prefixEnd_5006417 : Nat := 4983230072969 + 3 ^ 40 * 5006417 * 2
def baseEnd_5006417 : Nat := 2570698277840444104163413

theorem tailTrace_5006417 : CollatzResearch.WordTrace tailWord_5006417 prefixEnd_5006417 2570698277840444104163413 := by
  unfold tailWord_5006417
  simp only [CollatzResearch.WordTrace]
  refine ⟨182599029103613711796457505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121732686069075807864305003 182599029103613711796457505)
  ·
    refine ⟨136949271827710283847343129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182599029103613711796457505 136949271827710283847343129)
    ·
      refine ⟨102711953870782712885507347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136949271827710283847343129 102711953870782712885507347)
      ·
        refine ⟨154067930806174069328261021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102711953870782712885507347 154067930806174069328261021)
        ·
          refine ⟨57775474052315275998097883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154067930806174069328261021 57775474052315275998097883)
          ·
            refine ⟨86663211078472913997146825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57775474052315275998097883 86663211078472913997146825)
            ·
              refine ⟨64997408308854685497860119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86663211078472913997146825 64997408308854685497860119)
              ·
                refine ⟨97496112463282028246790179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64997408308854685497860119 97496112463282028246790179)
                ·
                  refine ⟨146244168694923042370185269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97496112463282028246790179 146244168694923042370185269)
                  ·
                    refine ⟨13710390815149035222204869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 146244168694923042370185269 13710390815149035222204869)
                    ·
                      refine ⟨2570698277840444104163413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13710390815149035222204869 2570698277840444104163413)
                      ·
                        rfl

theorem cell23_5006417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_5006417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006417 prefixEnd_5006417 := by exact prefixLift 5006417
  have htrace : WordTrace (prefixWord ++ tailWord_5006417) baseStart_5006417 baseEnd_5006417 := by
    simpa [prefixWord, tailWord_5006417, baseEnd_5006417] using wordTrace_append hprefix tailTrace_5006417
  have hstable : (prefixWord ++ tailWord_5006417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006417).length < 2 ^ (prefixWord ++ tailWord_5006417).sum := by decide
  have hdescent : baseEnd_5006417 < baseStart_5006417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006422 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5006422 : Nat := 118140960795 + 5006422 * 2 ^ 59
def prefixEnd_5006422 : Nat := 4983230072969 + 3 ^ 40 * 5006422 * 2
def baseEnd_5006422 : Nat := 856900281747905528200297

theorem tailTrace_5006422 : CollatzResearch.WordTrace tailWord_5006422 prefixEnd_5006422 856900281747905528200297 := by
  unfold tailWord_5006422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11412450716787224853149345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121732807645730398433593013 11412450716787224853149345)
  ·
    refine ⟨8559338037590418639862009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11412450716787224853149345 8559338037590418639862009)
    ·
      refine ⟨6419503528192813979896507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8559338037590418639862009 6419503528192813979896507)
      ·
        refine ⟨9629255292289220969844761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6419503528192813979896507 9629255292289220969844761)
        ·
          refine ⟨7221941469216915727383571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9629255292289220969844761 7221941469216915727383571)
          ·
            refine ⟨10832912203825373591075357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7221941469216915727383571 10832912203825373591075357)
            ·
              refine ⟨4062342076434515096653259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10832912203825373591075357 4062342076434515096653259)
              ·
                refine ⟨6093513114651772644979889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4062342076434515096653259 6093513114651772644979889)
                ·
                  refine ⟨4570134835988829483734917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6093513114651772644979889 4570134835988829483734917)
                  ·
                    refine ⟨856900281747905528200297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4570134835988829483734917 856900281747905528200297)
                    ·
                      rfl

theorem cell23_5006422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5006422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006422 prefixEnd_5006422 := by exact prefixLift 5006422
  have htrace : WordTrace (prefixWord ++ tailWord_5006422) baseStart_5006422 baseEnd_5006422 := by
    simpa [prefixWord, tailWord_5006422, baseEnd_5006422] using wordTrace_append hprefix tailTrace_5006422
  have hstable : (prefixWord ++ tailWord_5006422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006422).length < 2 ^ (prefixWord ++ tailWord_5006422).sum := by decide
  have hdescent : baseEnd_5006422 < baseStart_5006422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006467 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 7]
def baseStart_5006467 : Nat := 118140960795 + 5006467 * 2 ^ 59
def prefixEnd_5006467 : Nat := 4983230072969 + 3 ^ 40 * 5006467 * 2
def baseEnd_5006467 : Nat := 2570723951873168908538183

theorem tailTrace_5006467 : CollatzResearch.WordTrace tailWord_5006467 prefixEnd_5006467 2570723951873168908538183 := by
  unfold tailWord_5006467
  simp only [CollatzResearch.WordTrace]
  refine ⟨182600852753432570335777655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121733901835621713557185103 182600852753432570335777655)
  ·
    refine ⟨273901279130148855503666483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182600852753432570335777655 273901279130148855503666483)
    ·
      refine ⟨410851918695223283255499725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273901279130148855503666483 410851918695223283255499725)
      ·
        refine ⟨154069469510708731220812397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410851918695223283255499725 154069469510708731220812397)
        ·
          refine ⟨57776051066515774207804649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154069469510708731220812397 57776051066515774207804649)
          ·
            refine ⟨43332038299886830655853487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57776051066515774207804649 43332038299886830655853487)
            ·
              refine ⟨64998057449830245983780231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43332038299886830655853487 64998057449830245983780231)
              ·
                refine ⟨97497086174745368975670347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64998057449830245983780231 97497086174745368975670347)
                ·
                  refine ⟨146245629262118053463505521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97497086174745368975670347 146245629262118053463505521)
                  ·
                    refine ⟨109684221946588540097629141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146245629262118053463505521 109684221946588540097629141)
                    ·
                      refine ⟨2570723951873168908538183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109684221946588540097629141 2570723951873168908538183)
                      ·
                        rfl

theorem cell23_5006467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_5006467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006467 prefixEnd_5006467 := by exact prefixLift 5006467
  have htrace : WordTrace (prefixWord ++ tailWord_5006467) baseStart_5006467 baseEnd_5006467 := by
    simpa [prefixWord, tailWord_5006467, baseEnd_5006467] using wordTrace_append hprefix tailTrace_5006467
  have hstable : (prefixWord ++ tailWord_5006467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006467).length < 2 ^ (prefixWord ++ tailWord_5006467).sum := by decide
  have hdescent : baseEnd_5006467 < baseStart_5006467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006468 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_5006468 : Nat := 118140960795 + 5006468 * 2 ^ 59
def prefixEnd_5006468 : Nat := 4983230072969 + 3 ^ 40 * 5006468 * 2
def baseEnd_5006468 : Nat := 2570724465353823404625679

theorem tailTrace_5006468 : CollatzResearch.WordTrace tailWord_5006468 prefixEnd_5006468 2570724465353823404625679 := by
  unfold tailWord_5006468
  simp only [CollatzResearch.WordTrace]
  refine ⟨91300444613214473753282029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121733926150952631671042705 91300444613214473753282029)
  ·
    refine ⟨34237666729955427657480761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91300444613214473753282029 34237666729955427657480761)
    ·
      refine ⟨25678250047466570743110571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34237666729955427657480761 25678250047466570743110571)
      ·
        refine ⟨38517375071199856114665857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25678250047466570743110571 38517375071199856114665857)
        ·
          refine ⟨28888031303399892085999393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38517375071199856114665857 28888031303399892085999393)
          ·
            refine ⟨21666023477549919064499545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28888031303399892085999393 21666023477549919064499545)
            ·
              refine ⟨16249517608162439298374659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21666023477549919064499545 16249517608162439298374659)
              ·
                refine ⟨24374276412243658947561989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16249517608162439298374659 24374276412243658947561989)
                ·
                  refine ⟨4570176827295686052667873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24374276412243658947561989 4570176827295686052667873)
                  ·
                    refine ⟨3427632620471764539500905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4570176827295686052667873 3427632620471764539500905)
                    ·
                      refine ⟨2570724465353823404625679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427632620471764539500905 2570724465353823404625679)
                      ·
                        rfl

theorem cell23_5006468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_5006468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006468 prefixEnd_5006468 := by exact prefixLift 5006468
  have htrace : WordTrace (prefixWord ++ tailWord_5006468) baseStart_5006468 baseEnd_5006468 := by
    simpa [prefixWord, tailWord_5006468, baseEnd_5006468] using wordTrace_append hprefix tailTrace_5006468
  have hstable : (prefixWord ++ tailWord_5006468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006468).length < 2 ^ (prefixWord ++ tailWord_5006468).sum := by decide
  have hdescent : baseEnd_5006468 < baseStart_5006468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006514 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_5006514 : Nat := 118140960795 + 5006514 * 2 ^ 59
def prefixEnd_5006514 : Nat := 4983230072969 + 3 ^ 40 * 5006514 * 2
def baseEnd_5006514 : Nat := 2570748085463930224650467

theorem tailTrace_5006514 : CollatzResearch.WordTrace tailWord_5006514 prefixEnd_5006514 2570748085463930224650467 := by
  unfold tailWord_5006514
  simp only [CollatzResearch.WordTrace]
  refine ⟨45650641746065574340684649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121735044656174864908492397 45650641746065574340684649)
  ·
    refine ⟨34237981309549180755513487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45650641746065574340684649 34237981309549180755513487)
    ·
      refine ⟨51356971964323771133270231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34237981309549180755513487 51356971964323771133270231)
      ·
        refine ⟨77035457946485656699905347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51356971964323771133270231 77035457946485656699905347)
        ·
          refine ⟨115553186919728485049858021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77035457946485656699905347 115553186919728485049858021)
          ·
            refine ⟨21666222547449090946848379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115553186919728485049858021 21666222547449090946848379)
            ·
              refine ⟨32499333821173636420272569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21666222547449090946848379 32499333821173636420272569)
              ·
                refine ⟨24374500365880227315204427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32499333821173636420272569 24374500365880227315204427)
                ·
                  refine ⟨36561750548820340972806641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24374500365880227315204427 36561750548820340972806641)
                  ·
                    refine ⟨27421312911615255729604981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36561750548820340972806641 27421312911615255729604981)
                    ·
                      refine ⟨2570748085463930224650467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27421312911615255729604981 2570748085463930224650467)
                      ·
                        rfl

theorem cell23_5006514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_5006514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006514 prefixEnd_5006514 := by exact prefixLift 5006514
  have htrace : WordTrace (prefixWord ++ tailWord_5006514) baseStart_5006514 baseEnd_5006514 := by
    simpa [prefixWord, tailWord_5006514, baseEnd_5006514] using wordTrace_append hprefix tailTrace_5006514
  have hstable : (prefixWord ++ tailWord_5006514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006514).length < 2 ^ (prefixWord ++ tailWord_5006514).sum := by decide
  have hdescent : baseEnd_5006514 < baseStart_5006514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006561 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_5006561 : Nat := 118140960795 + 5006561 * 2 ^ 59
def prefixEnd_5006561 : Nat := 4983230072969 + 3 ^ 40 * 5006561 * 2
def baseEnd_5006561 : Nat := 2570772219054691540762751

theorem tailTrace_5006561 : CollatzResearch.WordTrace tailWord_5006561 prefixEnd_5006561 2570772219054691540762751 := by
  unfold tailWord_5006561
  simp only [CollatzResearch.WordTrace]
  refine ⟨182604281215092024389699537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121736187476728016259799691 182604281215092024389699537)
  ·
    refine ⟨136953210911319018292274653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182604281215092024389699537 136953210911319018292274653)
    ·
      refine ⟨51357454091744631859602995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136953210911319018292274653 51357454091744631859602995)
      ·
        refine ⟨77036181137616947789404493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51357454091744631859602995 77036181137616947789404493)
        ·
          refine ⟨28888567926606355421026685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77036181137616947789404493 28888567926606355421026685)
          ·
            refine ⟨10833212972477383282885007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28888567926606355421026685 10833212972477383282885007)
            ·
              refine ⟨16249819458716074924327511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10833212972477383282885007 16249819458716074924327511)
              ·
                refine ⟨24374729188074112386491267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16249819458716074924327511 24374729188074112386491267)
                ·
                  refine ⟨36562093782111168579736901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24374729188074112386491267 36562093782111168579736901)
                  ·
                    refine ⟨6855392584145844108700669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36562093782111168579736901 6855392584145844108700669)
                    ·
                      refine ⟨2570772219054691540762751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6855392584145844108700669 2570772219054691540762751)
                      ·
                        rfl

theorem cell23_5006561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_5006561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006561 prefixEnd_5006561 := by exact prefixLift 5006561
  have htrace : WordTrace (prefixWord ++ tailWord_5006561) baseStart_5006561 baseEnd_5006561 := by
    simpa [prefixWord, tailWord_5006561, baseEnd_5006561] using wordTrace_append hprefix tailTrace_5006561
  have hstable : (prefixWord ++ tailWord_5006561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006561).length < 2 ^ (prefixWord ++ tailWord_5006561).sum := by decide
  have hdescent : baseEnd_5006561 < baseStart_5006561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006601 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 3, 5, 2]
def baseStart_5006601 : Nat := 118140960795 + 5006601 * 2 ^ 59
def prefixEnd_5006601 : Nat := 4983230072969 + 3 ^ 40 * 5006601 * 2
def baseEnd_5006601 : Nat := 2570792758280871384262567

theorem tailTrace_5006601 : CollatzResearch.WordTrace tailWord_5006601 prefixEnd_5006601 2570792758280871384262567 := by
  unfold tailWord_5006601
  simp only [CollatzResearch.WordTrace]
  refine ⟨182605740134947111221155657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121737160089964740814103771 182605740134947111221155657)
  ·
    refine ⟨136954305101210333415866743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182605740134947111221155657 136954305101210333415866743)
    ·
      refine ⟨205431457651815500123800115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136954305101210333415866743 205431457651815500123800115)
      ·
        refine ⟨308147186477723250185700173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205431457651815500123800115 308147186477723250185700173)
        ·
          refine ⟨115555194929146218819637565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308147186477723250185700173 115555194929146218819637565)
          ·
            refine ⟨43333198098429832057364087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115555194929146218819637565 43333198098429832057364087)
            ·
              refine ⟨64999797147644748086046131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43333198098429832057364087 64999797147644748086046131)
              ·
                refine ⟨97499695721467122129069197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64999797147644748086046131 97499695721467122129069197)
                ·
                  refine ⟨36562385895550170798400949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97499695721467122129069197 36562385895550170798400949)
                  ·
                    refine ⟨3427723677707828512350089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36562385895550170798400949 3427723677707828512350089)
                    ·
                      refine ⟨2570792758280871384262567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427723677707828512350089 2570792758280871384262567)
                      ·
                        rfl

theorem cell23_5006601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 5, 2].length) (baseStart_5006601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006601 prefixEnd_5006601 := by exact prefixLift 5006601
  have htrace : WordTrace (prefixWord ++ tailWord_5006601) baseStart_5006601 baseEnd_5006601 := by
    simpa [prefixWord, tailWord_5006601, baseEnd_5006601] using wordTrace_append hprefix tailTrace_5006601
  have hstable : (prefixWord ++ tailWord_5006601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006601).length < 2 ^ (prefixWord ++ tailWord_5006601).sum := by decide
  have hdescent : baseEnd_5006601 < baseStart_5006601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006618 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2]
def baseStart_5006618 : Nat := 118140960795 + 5006618 * 2 ^ 59
def prefixEnd_5006618 : Nat := 4983230072969 + 3 ^ 40 * 5006618 * 2
def baseEnd_5006618 : Nat := 2570801487451997817749989

theorem tailTrace_5006618 : CollatzResearch.WordTrace tailWord_5006618 prefixEnd_5006618 2570801487451997817749989 := by
  unfold tailWord_5006618
  simp only [CollatzResearch.WordTrace]
  refine ⟨45651590043971380781131127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121737573450590348749683005 45651590043971380781131127)
  ·
    refine ⟨68477385065957071171696691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45651590043971380781131127 68477385065957071171696691)
    ·
      refine ⟨102716077598935606757545037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68477385065957071171696691 102716077598935606757545037)
      ·
        refine ⟨38518529099600852534079389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102716077598935606757545037 38518529099600852534079389)
        ·
          refine ⟨14444448412350319700279771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38518529099600852534079389 14444448412350319700279771)
          ·
            refine ⟨21666672618525479550419657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14444448412350319700279771 21666672618525479550419657)
            ·
              refine ⟨16250004463894109662814743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21666672618525479550419657 16250004463894109662814743)
              ·
                refine ⟨24375006695841164494222115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16250004463894109662814743 24375006695841164494222115)
                ·
                  refine ⟨36562510043761746741333173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24375006695841164494222115 36562510043761746741333173)
                  ·
                    refine ⟨3427735316602663756999985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36562510043761746741333173 3427735316602663756999985)
                    ·
                      refine ⟨2570801487451997817749989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427735316602663756999985 2570801487451997817749989)
                      ·
                        rfl

theorem cell23_5006618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_5006618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006618 prefixEnd_5006618 := by exact prefixLift 5006618
  have htrace : WordTrace (prefixWord ++ tailWord_5006618) baseStart_5006618 baseEnd_5006618 := by
    simpa [prefixWord, tailWord_5006618, baseEnd_5006618] using wordTrace_append hprefix tailTrace_5006618
  have hstable : (prefixWord ++ tailWord_5006618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006618).length < 2 ^ (prefixWord ++ tailWord_5006618).sum := by decide
  have hdescent : baseEnd_5006618 < baseStart_5006618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006662 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_5006662 : Nat := 118140960795 + 5006662 * 2 ^ 59
def prefixEnd_5006662 : Nat := 4983230072969 + 3 ^ 40 * 5006662 * 2
def baseEnd_5006662 : Nat := 856941360200265215199929

theorem tailTrace_5006662 : CollatzResearch.WordTrace tailWord_5006662 prefixEnd_5006662 856941360200265215199929 := by
  unfold tailWord_5006662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5706498905866441207472695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121738643325150745759417493 5706498905866441207472695)
  ·
    refine ⟨8559748358799661811209043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5706498905866441207472695 8559748358799661811209043)
    ·
      refine ⟨12839622538199492716813565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8559748358799661811209043 12839622538199492716813565)
      ·
        refine ⟨4814858451824809768805087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12839622538199492716813565 4814858451824809768805087)
        ·
          refine ⟨7222287677737214653207631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814858451824809768805087 7222287677737214653207631)
          ·
            refine ⟨10833431516605821979811447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7222287677737214653207631 10833431516605821979811447)
            ·
              refine ⟨16250147274908732969717171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10833431516605821979811447 16250147274908732969717171)
              ·
                refine ⟨24375220912363099454575757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16250147274908732969717171 24375220912363099454575757)
                ·
                  refine ⟨9140707842136162295465909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24375220912363099454575757 9140707842136162295465909)
                  ·
                    refine ⟨856941360200265215199929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9140707842136162295465909 856941360200265215199929)
                    ·
                      rfl

theorem cell23_5006662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_5006662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006662 prefixEnd_5006662 := by exact prefixLift 5006662
  have htrace : WordTrace (prefixWord ++ tailWord_5006662) baseStart_5006662 baseEnd_5006662 := by
    simpa [prefixWord, tailWord_5006662, baseEnd_5006662] using wordTrace_append hprefix tailTrace_5006662
  have hstable : (prefixWord ++ tailWord_5006662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006662).length < 2 ^ (prefixWord ++ tailWord_5006662).sum := by decide
  have hdescent : baseEnd_5006662 < baseStart_5006662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006668 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_5006668 : Nat := 118140960795 + 5006668 * 2 ^ 59
def prefixEnd_5006668 : Nat := 4983230072969 + 3 ^ 40 * 5006668 * 2
def baseEnd_5006668 : Nat := 2570827161484722622124759

theorem tailTrace_5006668 : CollatzResearch.WordTrace tailWord_5006668 prefixEnd_5006668 2570827161484722622124759 := by
  unfold tailWord_5006668
  simp only [CollatzResearch.WordTrace]
  refine ⟨91304091912852190831922329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121738789217136254442563105 91304091912852190831922329)
  ·
    refine ⟨68478068934639143123941747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91304091912852190831922329 68478068934639143123941747)
    ·
      refine ⟨102717103401958714685912621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68478068934639143123941747 102717103401958714685912621)
      ·
        refine ⟨38518913775734518007217233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102717103401958714685912621 38518913775734518007217233)
        ·
          refine ⟨28889185331800888505412925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38518913775734518007217233 28889185331800888505412925)
          ·
            refine ⟨10833444499425333189529847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28889185331800888505412925 10833444499425333189529847)
            ·
              refine ⟨16250166749137999784294771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10833444499425333189529847 16250166749137999784294771)
              ·
                refine ⟨24375250123706999676442157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16250166749137999784294771 24375250123706999676442157)
                ·
                  refine ⟨9140718796390124878665809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24375250123706999676442157 9140718796390124878665809)
                  ·
                    refine ⟨6855539097292593658999357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9140718796390124878665809 6855539097292593658999357)
                    ·
                      refine ⟨2570827161484722622124759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6855539097292593658999357 2570827161484722622124759)
                      ·
                        rfl

theorem cell23_5006668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_5006668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006668 prefixEnd_5006668 := by exact prefixLift 5006668
  have htrace : WordTrace (prefixWord ++ tailWord_5006668) baseStart_5006668 baseEnd_5006668 := by
    simpa [prefixWord, tailWord_5006668, baseEnd_5006668] using wordTrace_append hprefix tailTrace_5006668
  have hstable : (prefixWord ++ tailWord_5006668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006668).length < 2 ^ (prefixWord ++ tailWord_5006668).sum := by decide
  have hdescent : baseEnd_5006668 < baseStart_5006668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006669 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5006669 : Nat := 118140960795 + 5006669 * 2 ^ 59
def prefixEnd_5006669 : Nat := 4983230072969 + 3 ^ 40 * 5006669 * 2
def baseEnd_5006669 : Nat := 2570827674965377118212255

theorem tailTrace_5006669 : CollatzResearch.WordTrace tailWord_5006669 prefixEnd_5006669 2570827674965377118212255 := by
  unfold tailWord_5006669
  simp only [CollatzResearch.WordTrace]
  refine ⟨182608220298700758834631061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121738813532467172556420707 182608220298700758834631061)
  ·
    refine ⟨8559760326501598070373331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182608220298700758834631061 8559760326501598070373331)
    ·
      refine ⟨12839640489752397105559997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8559760326501598070373331 12839640489752397105559997)
      ·
        refine ⟨4814865183657148914584999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12839640489752397105559997 4814865183657148914584999)
        ·
          refine ⟨7222297775485723371877499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814865183657148914584999 7222297775485723371877499)
          ·
            refine ⟨10833446663228585057816249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7222297775485723371877499 10833446663228585057816249)
            ·
              refine ⟨8125084997421438793362187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10833446663228585057816249 8125084997421438793362187)
              ·
                refine ⟨12187627496132158190043281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8125084997421438793362187 12187627496132158190043281)
                ·
                  refine ⟨9140720622099118642532461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12187627496132158190043281 9140720622099118642532461)
                  ·
                    refine ⟨3427770233287169490949673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9140720622099118642532461 3427770233287169490949673)
                    ·
                      refine ⟨2570827674965377118212255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427770233287169490949673 2570827674965377118212255)
                      ·
                        rfl

theorem cell23_5006669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5006669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006669 prefixEnd_5006669 := by exact prefixLift 5006669
  have htrace : WordTrace (prefixWord ++ tailWord_5006669) baseStart_5006669 baseEnd_5006669 := by
    simpa [prefixWord, tailWord_5006669, baseEnd_5006669] using wordTrace_append hprefix tailTrace_5006669
  have hstable : (prefixWord ++ tailWord_5006669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006669).length < 2 ^ (prefixWord ++ tailWord_5006669).sum := by decide
  have hdescent : baseEnd_5006669 < baseStart_5006669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006681 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 3]
def baseStart_5006681 : Nat := 118140960795 + 5006681 * 2 ^ 59
def prefixEnd_5006681 : Nat := 4983230072969 + 3 ^ 40 * 5006681 * 2
def baseEnd_5006681 : Nat := 2570833836733231071262199

theorem tailTrace_5006681 : CollatzResearch.WordTrace tailWord_5006681 prefixEnd_5006681 2570833836733231071262199 := by
  unfold tailWord_5006681
  simp only [CollatzResearch.WordTrace]
  refine ⟨182608657974657284884067897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121739105316438189922711931 182608657974657284884067897)
  ·
    refine ⟨136956493480992963663050923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182608657974657284884067897 136956493480992963663050923)
    ·
      refine ⟨205434740221489445494576385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136956493480992963663050923 205434740221489445494576385)
      ·
        refine ⟨154076055166117084120932289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205434740221489445494576385 154076055166117084120932289)
        ·
          refine ⟨115557041374587813090699217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154076055166117084120932289 115557041374587813090699217)
          ·
            refine ⟨86667781030940859818024413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115557041374587813090699217 86667781030940859818024413)
            ·
              refine ⟨32500417886602822431759155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86667781030940859818024413 32500417886602822431759155)
              ·
                refine ⟨48750626829904233647638733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32500417886602822431759155 48750626829904233647638733)
                ·
                  refine ⟨18281485061214087617864525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48750626829904233647638733 18281485061214087617864525)
                  ·
                    refine ⟨6855556897955282856699197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18281485061214087617864525 6855556897955282856699197)
                    ·
                      refine ⟨2570833836733231071262199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6855556897955282856699197 2570833836733231071262199)
                      ·
                        rfl

theorem cell23_5006681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_5006681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006681 prefixEnd_5006681 := by exact prefixLift 5006681
  have htrace : WordTrace (prefixWord ++ tailWord_5006681) baseStart_5006681 baseEnd_5006681 := by
    simpa [prefixWord, tailWord_5006681, baseEnd_5006681] using wordTrace_append hprefix tailTrace_5006681
  have hstable : (prefixWord ++ tailWord_5006681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006681).length < 2 ^ (prefixWord ++ tailWord_5006681).sum := by decide
  have hdescent : baseEnd_5006681 < baseStart_5006681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006701 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_5006701 : Nat := 118140960795 + 5006701 * 2 ^ 59
def prefixEnd_5006701 : Nat := 4983230072969 + 3 ^ 40 * 5006701 * 2
def baseEnd_5006701 : Nat := 856948035448773664337369

theorem tailTrace_5006701 : CollatzResearch.WordTrace tailWord_5006701 prefixEnd_5006701 856948035448773664337369 := by
  unfold tailWord_5006701
  simp only [CollatzResearch.WordTrace]
  refine ⟨182609387434584828299795957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121739591623056552199863971 182609387434584828299795957)
  ·
    refine ⟨17119630071992327653105871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182609387434584828299795957 17119630071992327653105871)
    ·
      refine ⟨25679445107988491479658807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17119630071992327653105871 25679445107988491479658807)
      ·
        refine ⟨38519167661982737219488211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25679445107988491479658807 38519167661982737219488211)
        ·
          refine ⟨57778751492974105829232317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38519167661982737219488211 57778751492974105829232317)
          ·
            refine ⟨21667031809865289685962119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57778751492974105829232317 21667031809865289685962119)
            ·
              refine ⟨32500547714797934528943179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21667031809865289685962119 32500547714797934528943179)
              ·
                refine ⟨48750821572196901793414769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32500547714797934528943179 48750821572196901793414769)
                ·
                  refine ⟨36563116179147676345061077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48750821572196901793414769 36563116179147676345061077)
                  ·
                    refine ⟨856948035448773664337369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36563116179147676345061077 856948035448773664337369)
                    ·
                      rfl

theorem cell23_5006701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_5006701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006701 prefixEnd_5006701 := by exact prefixLift 5006701
  have htrace : WordTrace (prefixWord ++ tailWord_5006701) baseStart_5006701 baseEnd_5006701 := by
    simpa [prefixWord, tailWord_5006701, baseEnd_5006701] using wordTrace_append hprefix tailTrace_5006701
  have hstable : (prefixWord ++ tailWord_5006701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006701).length < 2 ^ (prefixWord ++ tailWord_5006701).sum := by decide
  have hdescent : baseEnd_5006701 < baseStart_5006701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006741 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_5006741 : Nat := 118140960795 + 5006741 * 2 ^ 59
def prefixEnd_5006741 : Nat := 4983230072969 + 3 ^ 40 * 5006741 * 2
def baseEnd_5006741 : Nat := 2570864645572500836511923

theorem tailTrace_5006741 : CollatzResearch.WordTrace tailWord_5006741 prefixEnd_5006741 2570864645572500836511923 := by
  unfold tailWord_5006741
  simp only [CollatzResearch.WordTrace]
  refine ⟨182610846354439915131252077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121740564236293276754168051 182610846354439915131252077)
  ·
    refine ⟨68479067382914968174219529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182610846354439915131252077 68479067382914968174219529)
    ·
      refine ⟨51359300537186226130664647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68479067382914968174219529 51359300537186226130664647)
      ·
        refine ⟨77038950805779339195996971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51359300537186226130664647 77038950805779339195996971)
        ·
          refine ⟨115558426208669008793995457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77038950805779339195996971 115558426208669008793995457)
          ·
            refine ⟨86668819656501756595496593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115558426208669008793995457 86668819656501756595496593)
            ·
              refine ⟨65001614742376317446622445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86668819656501756595496593 65001614742376317446622445)
              ·
                refine ⟨24375605528391119042483417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65001614742376317446622445 24375605528391119042483417)
                ·
                  refine ⟨18281704146293339281862563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24375605528391119042483417 18281704146293339281862563)
                  ·
                    refine ⟨27422556219440008922793845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18281704146293339281862563 27422556219440008922793845)
                    ·
                      refine ⟨2570864645572500836511923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27422556219440008922793845 2570864645572500836511923)
                      ·
                        rfl

theorem cell23_5006741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_5006741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006741 prefixEnd_5006741 := by exact prefixLift 5006741
  have htrace : WordTrace (prefixWord ++ tailWord_5006741) baseStart_5006741 baseEnd_5006741 := by
    simpa [prefixWord, tailWord_5006741, baseEnd_5006741] using wordTrace_append hprefix tailTrace_5006741
  have hstable : (prefixWord ++ tailWord_5006741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006741).length < 2 ^ (prefixWord ++ tailWord_5006741).sum := by decide
  have hdescent : baseEnd_5006741 < baseStart_5006741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006755 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 4, 2, 2]
def baseStart_5006755 : Nat := 118140960795 + 5006755 * 2 ^ 59
def prefixEnd_5006755 : Nat := 4983230072969 + 3 ^ 40 * 5006755 * 2
def baseEnd_5006755 : Nat := 2570871834301663781736859

theorem tailTrace_5006755 : CollatzResearch.WordTrace tailWord_5006755 prefixEnd_5006755 2570871834301663781736859 := by
  unfold tailWord_5006755
  simp only [CollatzResearch.WordTrace]
  refine ⟨182611356976389195522261719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121740904650926130348174479 182611356976389195522261719)
  ·
    refine ⟨273917035464583793283392579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182611356976389195522261719 273917035464583793283392579)
    ·
      refine ⟨410875553196875689925088869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273917035464583793283392579 410875553196875689925088869)
      ·
        refine ⟨77039166224414191860954163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 410875553196875689925088869 77039166224414191860954163)
        ·
          refine ⟨115558749336621287791431245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77039166224414191860954163 115558749336621287791431245)
          ·
            refine ⟨43334531001232982921786717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115558749336621287791431245 43334531001232982921786717)
            ·
              refine ⟨16250449125462368595670019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43334531001232982921786717 16250449125462368595670019)
              ·
                refine ⟨24375673688193552893505029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16250449125462368595670019 24375673688193552893505029)
                ·
                  refine ⟨4570438816536291167532193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24375673688193552893505029 4570438816536291167532193)
                  ·
                    refine ⟨3427829112402218375649145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4570438816536291167532193 3427829112402218375649145)
                    ·
                      refine ⟨2570871834301663781736859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427829112402218375649145 2570871834301663781736859)
                      ·
                        rfl

theorem cell23_5006755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_5006755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006755 prefixEnd_5006755 := by exact prefixLift 5006755
  have htrace : WordTrace (prefixWord ++ tailWord_5006755) baseStart_5006755 baseEnd_5006755 := by
    simpa [prefixWord, tailWord_5006755, baseEnd_5006755] using wordTrace_append hprefix tailTrace_5006755
  have hstable : (prefixWord ++ tailWord_5006755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006755).length < 2 ^ (prefixWord ++ tailWord_5006755).sum := by decide
  have hdescent : baseEnd_5006755 < baseStart_5006755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006791 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 1, 7]
def baseStart_5006791 : Nat := 118140960795 + 5006791 * 2 ^ 59
def prefixEnd_5006791 : Nat := 4983230072969 + 3 ^ 40 * 5006791 * 2
def baseEnd_5006791 : Nat := 856963439868408546962231

theorem tailTrace_5006791 : CollatzResearch.WordTrace tailWord_5006791 prefixEnd_5006791 856963439868408546962231 := by
  unfold tailWord_5006791
  simp only [CollatzResearch.WordTrace]
  refine ⟨182612670004258773670572227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121741780002839182447048151 182612670004258773670572227)
  ·
    refine ⟨273919005006388160505858341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182612670004258773670572227 273919005006388160505858341)
    ·
      refine ⟨51359813438697780094848439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273919005006388160505858341 51359813438697780094848439)
      ·
        refine ⟨77039720158046670142272659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51359813438697780094848439 77039720158046670142272659)
        ·
          refine ⟨115559580237070005213408989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77039720158046670142272659 115559580237070005213408989)
          ·
            refine ⟨43334842588901251955028371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115559580237070005213408989 43334842588901251955028371)
            ·
              refine ⟨65002263883351877932542557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43334842588901251955028371 65002263883351877932542557)
              ·
                refine ⟨24375848956256954224703459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65002263883351877932542557 24375848956256954224703459)
                ·
                  refine ⟨36563773434385431337055189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24375848956256954224703459 36563773434385431337055189)
                  ·
                    refine ⟨856963439868408546962231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36563773434385431337055189 856963439868408546962231)
                    ·
                      rfl

theorem cell23_5006791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_5006791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006791 prefixEnd_5006791 := by exact prefixLift 5006791
  have htrace : WordTrace (prefixWord ++ tailWord_5006791) baseStart_5006791 baseEnd_5006791 := by
    simpa [prefixWord, tailWord_5006791, baseEnd_5006791] using wordTrace_append hprefix tailTrace_5006791
  have hstable : (prefixWord ++ tailWord_5006791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006791).length < 2 ^ (prefixWord ++ tailWord_5006791).sum := by decide
  have hdescent : baseEnd_5006791 < baseStart_5006791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006841 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 6]
def baseStart_5006841 : Nat := 118140960795 + 5006841 * 2 ^ 59
def prefixEnd_5006841 : Nat := 4983230072969 + 3 ^ 40 * 5006841 * 2
def baseEnd_5006841 : Nat := 2570915993637950445261463

theorem tailTrace_5006841 : CollatzResearch.WordTrace tailWord_5006841 prefixEnd_5006841 2570915993637950445261463 := by
  unfold tailWord_5006841
  simp only [CollatzResearch.WordTrace]
  refine ⟨182614493654077632209892377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121742995769385088139928251 182614493654077632209892377)
  ·
    refine ⟨136960870240558224157419283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182614493654077632209892377 136960870240558224157419283)
    ·
      refine ⟨205441305360837336236128925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136960870240558224157419283 205441305360837336236128925)
      ·
        refine ⟨77040489510314001088548347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205441305360837336236128925 77040489510314001088548347)
        ·
          refine ⟨115560734265471001632822521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77040489510314001088548347 115560734265471001632822521)
          ·
            refine ⟨86670550699103251224616891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115560734265471001632822521 86670550699103251224616891)
            ·
              refine ⟨130005826048654876836925337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86670550699103251224616891 130005826048654876836925337)
              ·
                refine ⟨97504369536491157627694003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130005826048654876836925337 97504369536491157627694003)
                ·
                  refine ⟨146256554304736736441541005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97504369536491157627694003 146256554304736736441541005)
                  ·
                    refine ⟨54846207864276276165577877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146256554304736736441541005 54846207864276276165577877)
                    ·
                      refine ⟨2570915993637950445261463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54846207864276276165577877 2570915993637950445261463)
                      ·
                        rfl

theorem cell23_5006841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_5006841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006841 prefixEnd_5006841 := by exact prefixLift 5006841
  have htrace : WordTrace (prefixWord ++ tailWord_5006841) baseStart_5006841 baseEnd_5006841 := by
    simpa [prefixWord, tailWord_5006841, baseEnd_5006841] using wordTrace_append hprefix tailTrace_5006841
  have hstable : (prefixWord ++ tailWord_5006841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006841).length < 2 ^ (prefixWord ++ tailWord_5006841).sum := by decide
  have hdescent : baseEnd_5006841 < baseStart_5006841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006845 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_5006845 : Nat := 118140960795 + 5006845 * 2 ^ 59
def prefixEnd_5006845 : Nat := 4983230072969 + 3 ^ 40 * 5006845 * 2
def baseEnd_5006845 : Nat := 2570918047560568429611445

theorem tailTrace_5006845 : CollatzResearch.WordTrace tailWord_5006845 prefixEnd_5006845 2570918047560568429611445 := by
  unfold tailWord_5006845
  simp only [CollatzResearch.WordTrace]
  refine ⟨182614639546063140893037989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121743093030708760595358659 182614639546063140893037989)
  ·
    refine ⟨34240244914886838917444623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182614639546063140893037989 34240244914886838917444623)
    ·
      refine ⟨51360367372330258376166935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34240244914886838917444623 51360367372330258376166935)
      ·
        refine ⟨77040551058495387564250403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51360367372330258376166935 77040551058495387564250403)
        ·
          refine ⟨115560826587743081346375605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77040551058495387564250403 115560826587743081346375605)
          ·
            refine ⟨10833827492600913876222713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115560826587743081346375605 10833827492600913876222713)
            ·
              refine ⟨8125370619450685407167035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10833827492600913876222713 8125370619450685407167035)
              ·
                refine ⟨12188055929176028110750553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8125370619450685407167035 12188055929176028110750553)
                ·
                  refine ⟨9141041946882021083062915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12188055929176028110750553 9141041946882021083062915)
                  ·
                    refine ⟨13711562920323031624594373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9141041946882021083062915 13711562920323031624594373)
                    ·
                      refine ⟨2570918047560568429611445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13711562920323031624594373 2570918047560568429611445)
                      ·
                        rfl

theorem cell23_5006845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_5006845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006845 prefixEnd_5006845 := by exact prefixLift 5006845
  have htrace : WordTrace (prefixWord ++ tailWord_5006845) baseStart_5006845 baseEnd_5006845 := by
    simpa [prefixWord, tailWord_5006845, baseEnd_5006845] using wordTrace_append hprefix tailTrace_5006845
  have hstable : (prefixWord ++ tailWord_5006845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006845).length < 2 ^ (prefixWord ++ tailWord_5006845).sum := by decide
  have hdescent : baseEnd_5006845 < baseStart_5006845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006851 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 8]
def baseStart_5006851 : Nat := 118140960795 + 5006851 * 2 ^ 59
def prefixEnd_5006851 : Nat := 4983230072969 + 3 ^ 40 * 5006851 * 2
def baseEnd_5006851 : Nat := 285657903160499489570713

theorem tailTrace_5006851 : CollatzResearch.WordTrace tailWord_5006851 prefixEnd_5006851 285657903160499489570713 := by
  unfold tailWord_5006851
  simp only [CollatzResearch.WordTrace]
  refine ⟨182614858384041403917756407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121743238922694269278504271 182614858384041403917756407)
  ·
    refine ⟨273922287576062105876634611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182614858384041403917756407 273922287576062105876634611)
    ·
      refine ⟨410883431364093158814951917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273922287576062105876634611 410883431364093158814951917)
      ·
        refine ⟨154081286761534934555606969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410883431364093158814951917 154081286761534934555606969)
        ·
          refine ⟨115560965071151200916705227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154081286761534934555606969 115560965071151200916705227)
          ·
            refine ⟨173341447606726801375057841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115560965071151200916705227 173341447606726801375057841)
            ·
              refine ⟨130006085705045101031293381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173341447606726801375057841 130006085705045101031293381)
              ·
                refine ⟨24376141069695956443367509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130006085705045101031293381 24376141069695956443367509)
                ·
                  refine ⟨285657903160499489570713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24376141069695956443367509 285657903160499489570713)
                  ·
                    rfl

theorem cell23_5006851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 8].length) (baseStart_5006851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006851 prefixEnd_5006851 := by exact prefixLift 5006851
  have htrace : WordTrace (prefixWord ++ tailWord_5006851) baseStart_5006851 baseEnd_5006851 := by
    simpa [prefixWord, tailWord_5006851, baseEnd_5006851] using wordTrace_append hprefix tailTrace_5006851
  have hstable : (prefixWord ++ tailWord_5006851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006851).length < 2 ^ (prefixWord ++ tailWord_5006851).sum := by decide
  have hdescent : baseEnd_5006851 < baseStart_5006851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006952 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5006952 : Nat := 118140960795 + 5006952 * 2 ^ 59
def prefixEnd_5006952 : Nat := 4983230072969 + 3 ^ 40 * 5006952 * 2
def baseEnd_5006952 : Nat := 2570972989990599510973453

theorem tailTrace_5006952 : CollatzResearch.WordTrace tailWord_5006952 prefixEnd_5006952 2570972989990599510973453 := by
  unfold tailWord_5006952
  simp only [CollatzResearch.WordTrace]
  refine ⟨91309271078337749083591555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121745694771116998778122073 91309271078337749083591555)
  ·
    refine ⟨136963906617506623625387333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91309271078337749083591555 136963906617506623625387333)
    ·
      refine ⟨25680732490782491929760125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136963906617506623625387333 25680732490782491929760125)
      ·
        refine ⟨9630274684043434473660047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25680732490782491929760125 9630274684043434473660047)
        ·
          refine ⟨14445412026065151710490071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9630274684043434473660047 14445412026065151710490071)
          ·
            refine ⟨21668118039097727565735107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14445412026065151710490071 21668118039097727565735107)
            ·
              refine ⟨32502177058646591348602661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21668118039097727565735107 32502177058646591348602661)
              ·
                refine ⟨6094158198496235877862999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32502177058646591348602661 6094158198496235877862999)
                ·
                  refine ⟨9141237297744353816794499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6094158198496235877862999 9141237297744353816794499)
                  ·
                    refine ⟨13711855946616530725191749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9141237297744353816794499 13711855946616530725191749)
                    ·
                      refine ⟨2570972989990599510973453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13711855946616530725191749 2570972989990599510973453)
                      ·
                        rfl

theorem cell23_5006952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5006952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006952 prefixEnd_5006952 := by exact prefixLift 5006952
  have htrace : WordTrace (prefixWord ++ tailWord_5006952) baseStart_5006952 baseEnd_5006952 := by
    simpa [prefixWord, tailWord_5006952, baseEnd_5006952] using wordTrace_append hprefix tailTrace_5006952
  have hstable : (prefixWord ++ tailWord_5006952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006952).length < 2 ^ (prefixWord ++ tailWord_5006952).sum := by decide
  have hdescent : baseEnd_5006952 < baseStart_5006952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006986 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_5006986 : Nat := 118140960795 + 5006986 * 2 ^ 59
def prefixEnd_5006986 : Nat := 4983230072969 + 3 ^ 40 * 5006986 * 2
def baseEnd_5006986 : Nat := 2570990448332852377948297

theorem tailTrace_5006986 : CollatzResearch.WordTrace tailWord_5006986 prefixEnd_5006986 2570990448332852377948297 := by
  unfold tailWord_5006986
  simp only [CollatzResearch.WordTrace]
  refine ⟨45654945559638080493480203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121746521492368214649280541 45654945559638080493480203)
  ·
    refine ⟨68482418339457120740220305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45654945559638080493480203 68482418339457120740220305)
    ·
      refine ⟨51361813754592840555165229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68482418339457120740220305 51361813754592840555165229)
      ·
        refine ⟨19260680157972315208186961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51361813754592840555165229 19260680157972315208186961)
        ·
          refine ⟨14445510118479236406140221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19260680157972315208186961 14445510118479236406140221)
          ·
            refine ⟨5417066294429713652302583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14445510118479236406140221 5417066294429713652302583)
            ·
              refine ⟨8125599441644570478453875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417066294429713652302583 8125599441644570478453875)
              ·
                refine ⟨12188399162466855717680813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8125599441644570478453875 12188399162466855717680813)
                ·
                  refine ⟨4570649685925070894130305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12188399162466855717680813 4570649685925070894130305)
                  ·
                    refine ⟨3427987264443803170597729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4570649685925070894130305 3427987264443803170597729)
                    ·
                      refine ⟨2570990448332852377948297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3427987264443803170597729 2570990448332852377948297)
                      ·
                        rfl

theorem cell23_5006986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_5006986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006986 prefixEnd_5006986 := by exact prefixLift 5006986
  have htrace : WordTrace (prefixWord ++ tailWord_5006986) baseStart_5006986 baseEnd_5006986 := by
    simpa [prefixWord, tailWord_5006986, baseEnd_5006986] using wordTrace_append hprefix tailTrace_5006986
  have hstable : (prefixWord ++ tailWord_5006986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006986).length < 2 ^ (prefixWord ++ tailWord_5006986).sum := by decide
  have hdescent : baseEnd_5006986 < baseStart_5006986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5006988 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_5006988 : Nat := 118140960795 + 5006988 * 2 ^ 59
def prefixEnd_5006988 : Nat := 4983230072969 + 3 ^ 40 * 5006988 * 2
def baseEnd_5006988 : Nat := 856997158431387123374429

theorem tailTrace_5006988 : CollatzResearch.WordTrace tailWord_5006988 prefixEnd_5006988 856997158431387123374429 := by
  unfold tailWord_5006988
  simp only [CollatzResearch.WordTrace]
  refine ⟨91309927592272538157746809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121746570123030050876995745 91309927592272538157746809)
  ·
    refine ⟨68482445694204403618310107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91309927592272538157746809 68482445694204403618310107)
    ·
      refine ⟨102723668541306605427465161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68482445694204403618310107 102723668541306605427465161)
      ·
        refine ⟨77042751405979954070598871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102723668541306605427465161 77042751405979954070598871)
        ·
          refine ⟨115564127108969931105898307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77042751405979954070598871 115564127108969931105898307)
          ·
            refine ⟨173346190663454896658847461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115564127108969931105898307 173346190663454896658847461)
            ·
              refine ⟨32502410749397793123533899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173346190663454896658847461 32502410749397793123533899)
              ·
                refine ⟨48753616124096689685300849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32502410749397793123533899 48753616124096689685300849)
                ·
                  refine ⟨36565212093072517263975637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48753616124096689685300849 36565212093072517263975637)
                  ·
                    refine ⟨856997158431387123374429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36565212093072517263975637 856997158431387123374429)
                    ·
                      rfl

theorem cell23_5006988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_5006988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5006988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5006988 prefixEnd_5006988 := by exact prefixLift 5006988
  have htrace : WordTrace (prefixWord ++ tailWord_5006988) baseStart_5006988 baseEnd_5006988 := by
    simpa [prefixWord, tailWord_5006988, baseEnd_5006988] using wordTrace_append hprefix tailTrace_5006988
  have hstable : (prefixWord ++ tailWord_5006988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5006988).length < 2 ^ (prefixWord ++ tailWord_5006988).sum := by decide
  have hdescent : baseEnd_5006988 < baseStart_5006988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5006988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007006 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_5007006 : Nat := 118140960795 + 5007006 * 2 ^ 59
def prefixEnd_5007006 : Nat := 4983230072969 + 3 ^ 40 * 5007006 * 2
def baseEnd_5007006 : Nat := 2571000717945942299698205

theorem tailTrace_5007006 : CollatzResearch.WordTrace tailWord_5007006 prefixEnd_5007006 2571000717945942299698205 := by
  unfold tailWord_5007006
  simp only [CollatzResearch.WordTrace]
  refine ⟨22827563962309983173706109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121747007798986576926432581 22827563962309983173706109)
  ·
    refine ⟨8560336485866243690139791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22827563962309983173706109 8560336485866243690139791)
    ·
      refine ⟨12840504728799365535209687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8560336485866243690139791 12840504728799365535209687)
      ·
        refine ⟨19260757093199048302814531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12840504728799365535209687 19260757093199048302814531)
        ·
          refine ⟨28891135639798572454221797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19260757093199048302814531 28891135639798572454221797)
          ·
            refine ⟨5417087932462232335166587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28891135639798572454221797 5417087932462232335166587)
            ·
              refine ⟨8125631898693348502749881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417087932462232335166587 8125631898693348502749881)
              ·
                refine ⟨6094223924020011377062411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8125631898693348502749881 6094223924020011377062411)
                ·
                  refine ⟨9141335886030017065593617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6094223924020011377062411 9141335886030017065593617)
                  ·
                    refine ⟨6856001914522512799195213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9141335886030017065593617 6856001914522512799195213)
                    ·
                      refine ⟨2571000717945942299698205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6856001914522512799195213 2571000717945942299698205)
                      ·
                        rfl

theorem cell23_5007006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_5007006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007006 prefixEnd_5007006 := by exact prefixLift 5007006
  have htrace : WordTrace (prefixWord ++ tailWord_5007006) baseStart_5007006 baseEnd_5007006 := by
    simpa [prefixWord, tailWord_5007006, baseEnd_5007006] using wordTrace_append hprefix tailTrace_5007006
  have hstable : (prefixWord ++ tailWord_5007006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007006).length < 2 ^ (prefixWord ++ tailWord_5007006).sum := by decide
  have hdescent : baseEnd_5007006 < baseStart_5007006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007016 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5007016 : Nat := 118140960795 + 5007016 * 2 ^ 59
def prefixEnd_5007016 : Nat := 4983230072969 + 3 ^ 40 * 5007016 * 2
def baseEnd_5007016 : Nat := 2571005852752487260573159

theorem tailTrace_5007016 : CollatzResearch.WordTrace tailWord_5007016 prefixEnd_5007016 2571005852752487260573159 := by
  unfold tailWord_5007016
  simp only [CollatzResearch.WordTrace]
  refine ⟨91310438214221818548756451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121747250952295758065008601 91310438214221818548756451)
  ·
    refine ⟨136965657321332727823134677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91310438214221818548756451 136965657321332727823134677)
    ·
      refine ⟨3210132593468735808354719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 136965657321332727823134677 3210132593468735808354719)
      ·
        refine ⟨4815198890203103712532079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210132593468735808354719 4815198890203103712532079)
        ·
          refine ⟨7222798335304655568798119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815198890203103712532079 7222798335304655568798119)
          ·
            refine ⟨10834197502956983353197179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7222798335304655568798119 10834197502956983353197179)
            ·
              refine ⟨16251296254435475029795769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834197502956983353197179 16251296254435475029795769)
              ·
                refine ⟨12188472190826606272346827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16251296254435475029795769 12188472190826606272346827)
                ·
                  refine ⟨18282708286239909408520241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12188472190826606272346827 18282708286239909408520241)
                  ·
                    refine ⟨13712031214679932056390181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18282708286239909408520241 13712031214679932056390181)
                    ·
                      refine ⟨2571005852752487260573159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13712031214679932056390181 2571005852752487260573159)
                      ·
                        rfl

theorem cell23_5007016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5007016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007016 prefixEnd_5007016 := by exact prefixLift 5007016
  have htrace : WordTrace (prefixWord ++ tailWord_5007016) baseStart_5007016 baseEnd_5007016 := by
    simpa [prefixWord, tailWord_5007016, baseEnd_5007016] using wordTrace_append hprefix tailTrace_5007016
  have hstable : (prefixWord ++ tailWord_5007016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007016).length < 2 ^ (prefixWord ++ tailWord_5007016).sum := by decide
  have hdescent : baseEnd_5007016 < baseStart_5007016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007052 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_5007052 : Nat := 118140960795 + 5007052 * 2 ^ 59
def prefixEnd_5007052 : Nat := 4983230072969 + 3 ^ 40 * 5007052 * 2
def baseEnd_5007052 : Nat := 857008112685349706574331

theorem tailTrace_5007052 : CollatzResearch.WordTrace tailWord_5007052 prefixEnd_5007052 857008112685349706574331 := by
  unfold tailWord_5007052
  simp only [CollatzResearch.WordTrace]
  refine ⟨91311094728156607622911705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121748126304208810163882273 91311094728156607622911705)
  ·
    refine ⟨68483321046117455717183779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91311094728156607622911705 68483321046117455717183779)
    ·
      refine ⟨102724981569176183575775669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68483321046117455717183779 102724981569176183575775669)
      ·
        refine ⟨9630467022110267210228969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102724981569176183575775669 9630467022110267210228969)
        ·
          refine ⟨7222850266582700407671727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9630467022110267210228969 7222850266582700407671727)
          ·
            refine ⟨10834275399874050611507591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7222850266582700407671727 10834275399874050611507591)
            ·
              refine ⟨16251413099811075917261387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834275399874050611507591 16251413099811075917261387)
              ·
                refine ⟨24377119649716613875892081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16251413099811075917261387 24377119649716613875892081)
                ·
                  refine ⟨18282839737287460406919061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24377119649716613875892081 18282839737287460406919061)
                  ·
                    refine ⟨857008112685349706574331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18282839737287460406919061 857008112685349706574331)
                    ·
                      rfl

theorem cell23_5007052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_5007052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007052 prefixEnd_5007052 := by exact prefixLift 5007052
  have htrace : WordTrace (prefixWord ++ tailWord_5007052) baseStart_5007052 baseEnd_5007052 := by
    simpa [prefixWord, tailWord_5007052, baseEnd_5007052] using wordTrace_append hprefix tailTrace_5007052
  have hstable : (prefixWord ++ tailWord_5007052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007052).length < 2 ^ (prefixWord ++ tailWord_5007052).sum := by decide
  have hdescent : baseEnd_5007052 < baseStart_5007052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007065 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 7]
def baseStart_5007065 : Nat := 118140960795 + 5007065 * 2 ^ 59
def prefixEnd_5007065 : Nat := 4983230072969 + 3 ^ 40 * 5007065 * 2
def baseEnd_5007065 : Nat := 285670112589395285428937

theorem tailTrace_5007065 : CollatzResearch.WordTrace tailWord_5007065 prefixEnd_5007065 285670112589395285428937 := by
  unfold tailWord_5007065
  simp only [CollatzResearch.WordTrace]
  refine ⟨182622663605266118466046649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121748442403510745644031099 182622663605266118466046649)
  ·
    refine ⟨136966997703949588849534987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182622663605266118466046649 136966997703949588849534987)
    ·
      refine ⟨205450496555924383274302481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136966997703949588849534987 205450496555924383274302481)
      ·
        refine ⟨154087872416943287455726861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205450496555924383274302481 154087872416943287455726861)
        ·
          refine ⟨57782952156353732795897573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154087872416943287455726861 57782952156353732795897573)
          ·
            refine ⟨10834303529316324899230795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57782952156353732795897573 10834303529316324899230795)
            ·
              refine ⟨16251455293974487348846193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834303529316324899230795 16251455293974487348846193)
              ·
                refine ⟨12188591470480865511634645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16251455293974487348846193 12188591470480865511634645)
                ·
                  refine ⟨285670112589395285428937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12188591470480865511634645 285670112589395285428937)
                  ·
                    rfl

theorem cell23_5007065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 7].length) (baseStart_5007065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007065 prefixEnd_5007065 := by exact prefixLift 5007065
  have htrace : WordTrace (prefixWord ++ tailWord_5007065) baseStart_5007065 baseEnd_5007065 := by
    simpa [prefixWord, tailWord_5007065, baseEnd_5007065] using wordTrace_append hprefix tailTrace_5007065
  have hstable : (prefixWord ++ tailWord_5007065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007065).length < 2 ^ (prefixWord ++ tailWord_5007065).sum := by decide
  have hdescent : baseEnd_5007065 < baseStart_5007065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007082 : List Nat := [3, 1, 3, 1, 1, 1, 3, 5, 5]
def baseStart_5007082 : Nat := 118140960795 + 5007082 * 2 ^ 59
def prefixEnd_5007082 : Nat := 4983230072969 + 3 ^ 40 * 5007082 * 2
def baseEnd_5007082 : Nat := 285671082497298222483095

theorem tailTrace_5007082 : CollatzResearch.WordTrace tailWord_5007082 prefixEnd_5007082 285671082497298222483095 := by
  unfold tailWord_5007082
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655820911551132592353875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121748855764136353579610333 45655820911551132592353875)
  ·
    refine ⟨68483731367326698888530813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45655820911551132592353875 68483731367326698888530813)
    ·
      refine ⟨25681399262747512083199055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68483731367326698888530813 25681399262747512083199055)
      ·
        refine ⟨38522098894121268124798583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25681399262747512083199055 38522098894121268124798583)
        ·
          refine ⟨57783148341181902187197875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38522098894121268124798583 57783148341181902187197875)
          ·
            refine ⟨86674722511772853280796813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57783148341181902187197875 86674722511772853280796813)
            ·
              refine ⟨32503020941914819980298805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86674722511772853280796813 32503020941914819980298805)
              ·
                refine ⟨3047158213304514373153013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32503020941914819980298805 3047158213304514373153013)
                ·
                  refine ⟨285671082497298222483095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3047158213304514373153013 285671082497298222483095)
                  ·
                    rfl

theorem cell23_5007082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_5007082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007082 prefixEnd_5007082 := by exact prefixLift 5007082
  have htrace : WordTrace (prefixWord ++ tailWord_5007082) baseStart_5007082 baseEnd_5007082 := by
    simpa [prefixWord, tailWord_5007082, baseEnd_5007082] using wordTrace_append hprefix tailTrace_5007082
  have hstable : (prefixWord ++ tailWord_5007082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007082).length < 2 ^ (prefixWord ++ tailWord_5007082).sum := by decide
  have hdescent : baseEnd_5007082 < baseStart_5007082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007095 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 2, 5]
def baseStart_5007095 : Nat := 118140960795 + 5007095 * 2 ^ 59
def prefixEnd_5007095 : Nat := 4983230072969 + 3 ^ 40 * 5007095 * 2
def baseEnd_5007095 : Nat := 857015472574730817161765

theorem tailTrace_5007095 : CollatzResearch.WordTrace tailWord_5007095 prefixEnd_5007095 857015472574730817161765 := by
  unfold tailWord_5007095
  simp only [CollatzResearch.WordTrace]
  refine ⟨182623757795157433589638739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121749171863438289059759159 182623757795157433589638739)
  ·
    refine ⟨273935636692736150384458109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182623757795157433589638739 273935636692736150384458109)
    ·
      refine ⟨102725863759776056394171791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273935636692736150384458109 102725863759776056394171791)
      ·
        refine ⟨154088795639664084591257687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102725863759776056394171791 154088795639664084591257687)
        ·
          refine ⟨231133193459496126886886531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154088795639664084591257687 231133193459496126886886531)
          ·
            refine ⟨346699790189244190330329797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231133193459496126886886531 346699790189244190330329797)
            ·
              refine ⟨65006210660483285686936837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 346699790189244190330329797 65006210660483285686936837)
              ·
                refine ⟨12188664498840616066300657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65006210660483285686936837 12188664498840616066300657)
                ·
                  refine ⟨9141498374130462049725493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12188664498840616066300657 9141498374130462049725493)
                  ·
                    refine ⟨857015472574730817161765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9141498374130462049725493 857015472574730817161765)
                    ·
                      rfl

theorem cell23_5007095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_5007095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007095 prefixEnd_5007095 := by exact prefixLift 5007095
  have htrace : WordTrace (prefixWord ++ tailWord_5007095) baseStart_5007095 baseEnd_5007095 := by
    simpa [prefixWord, tailWord_5007095, baseEnd_5007095] using wordTrace_append hprefix tailTrace_5007095
  have hstable : (prefixWord ++ tailWord_5007095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007095).length < 2 ^ (prefixWord ++ tailWord_5007095).sum := by decide
  have hdescent : baseEnd_5007095 < baseStart_5007095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
