import V185TrunkScan22Chunk184

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1650078 : List Nat := [4, 3, 1, 2, 3, 9]
def baseStart_1650078 : Nat := 118140960795 + 1650078 * 2 ^ 59
def prefixEnd_1650078 : Nat := 4983230072969 + 3 ^ 40 * 1650078 * 2
def baseEnd_1650078 : Nat := 6973523715306175275197

theorem tailTrace_1650078 : CollatzResearch.WordTrace tailWord_1650078 prefixEnd_1650078 6973523715306175275197 := by
  unfold tailWord_1650078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522911114507086466424861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40122192610704461154265925 7522911114507086466424861)
  ·
    refine ⟨2821091667940157424909323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7522911114507086466424861 2821091667940157424909323)
    ·
      refine ⟨4231637501910236137363985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821091667940157424909323 4231637501910236137363985)
      ·
        refine ⟨3173728126432677103022989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4231637501910236137363985 3173728126432677103022989)
        ·
          refine ⟨1190148047412253913633621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3173728126432677103022989 1190148047412253913633621)
          ·
            refine ⟨6973523715306175275197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1190148047412253913633621 6973523715306175275197)
            ·
              rfl

theorem cell22_1650078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 9].length) (baseStart_1650078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650078 prefixEnd_1650078 := by exact prefixLift 1650078
  have htrace : WordTrace (prefixWord ++ tailWord_1650078) baseStart_1650078 baseEnd_1650078 := by
    simpa [prefixWord, tailWord_1650078, baseEnd_1650078] using wordTrace_append hprefix tailTrace_1650078
  have hstable : (prefixWord ++ tailWord_1650078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650078).length < 2 ^ (prefixWord ++ tailWord_1650078).sum := by decide
  have hdescent : baseEnd_1650078 < baseStart_1650078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650104 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_1650104 : Nat := 118140960795 + 1650104 * 2 ^ 59
def prefixEnd_1650104 : Nat := 4983230072969 + 3 ^ 40 * 1650104 * 2
def baseEnd_1650104 : Nat := 564864321271144796140877

theorem tailTrace_1650104 : CollatzResearch.WordTrace tailWord_1650104 prefixEnd_1650104 564864321271144796140877 := by
  unfold tailWord_1650104
  simp only [CollatzResearch.WordTrace]
  refine ⟨30092118606981249085922683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40122824809308332114563577 30092118606981249085922683)
  ·
    refine ⟨45138177910471873628884025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30092118606981249085922683 45138177910471873628884025)
    ·
      refine ⟨33853633432853905221663019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45138177910471873628884025 33853633432853905221663019)
      ·
        refine ⟨50780450149280857832494529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33853633432853905221663019 50780450149280857832494529)
        ·
          refine ⟨38085337611960643374370897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50780450149280857832494529 38085337611960643374370897)
          ·
            refine ⟨28564003208970482530778173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38085337611960643374370897 28564003208970482530778173)
            ·
              refine ⟨10711501203363930949041815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28564003208970482530778173 10711501203363930949041815)
              ·
                refine ⟨16067251805045896423562723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10711501203363930949041815 16067251805045896423562723)
                ·
                  refine ⟨24100877707568844635344085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16067251805045896423562723 24100877707568844635344085)
                  ·
                    refine ⟨564864321271144796140877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24100877707568844635344085 564864321271144796140877)
                    ·
                      rfl

theorem cell22_1650104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_1650104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650104 prefixEnd_1650104 := by exact prefixLift 1650104
  have htrace : WordTrace (prefixWord ++ tailWord_1650104) baseStart_1650104 baseEnd_1650104 := by
    simpa [prefixWord, tailWord_1650104, baseEnd_1650104] using wordTrace_append hprefix tailTrace_1650104
  have hstable : (prefixWord ++ tailWord_1650104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650104).length < 2 ^ (prefixWord ++ tailWord_1650104).sum := by decide
  have hdescent : baseEnd_1650104 < baseStart_1650104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650151 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 6]
def baseStart_1650151 : Nat := 118140960795 + 1650151 * 2 ^ 59
def prefixEnd_1650151 : Nat := 4983230072969 + 3 ^ 40 * 1650151 * 2
def baseEnd_1650151 : Nat := 188293470110550780071911

theorem tailTrace_1650151 : CollatzResearch.WordTrace tailWord_1650151 prefixEnd_1650151 188293470110550780071911 := by
  unfold tailWord_1650151
  simp only [CollatzResearch.WordTrace]
  refine ⟨60185951444792225198806307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40123967629861483465870871 60185951444792225198806307)
  ·
    refine ⟨90278927167188337798209461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60185951444792225198806307 90278927167188337798209461)
    ·
      refine ⟨8463649421923906668582137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90278927167188337798209461 8463649421923906668582137)
      ·
        refine ⟨6347737066442930001436603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8463649421923906668582137 6347737066442930001436603)
        ·
          refine ⟨9521605599664395002154905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347737066442930001436603 9521605599664395002154905)
          ·
            refine ⟨7141204199748296251616179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9521605599664395002154905 7141204199748296251616179)
            ·
              refine ⟨10711806299622444377424269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7141204199748296251616179 10711806299622444377424269)
              ·
                refine ⟨4016927362358416641534101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10711806299622444377424269 4016927362358416641534101)
                ·
                  refine ⟨188293470110550780071911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4016927362358416641534101 188293470110550780071911)
                  ·
                    rfl

theorem cell22_1650151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 6].length) (baseStart_1650151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650151 prefixEnd_1650151 := by exact prefixLift 1650151
  have htrace : WordTrace (prefixWord ++ tailWord_1650151) baseStart_1650151 baseEnd_1650151 := by
    simpa [prefixWord, tailWord_1650151, baseEnd_1650151] using wordTrace_append hprefix tailTrace_1650151
  have hstable : (prefixWord ++ tailWord_1650151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650151).length < 2 ^ (prefixWord ++ tailWord_1650151).sum := by decide
  have hdescent : baseEnd_1650151 < baseStart_1650151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650181 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_1650181 : Nat := 118140960795 + 1650181 * 2 ^ 59
def prefixEnd_1650181 : Nat := 4983230072969 + 3 ^ 40 * 1650181 * 2
def baseEnd_1650181 : Nat := 564890679944742261965641

theorem tailTrace_1650181 : CollatzResearch.WordTrace tailWord_1650181 prefixEnd_1650181 564890679944742261965641 := by
  unfold tailWord_1650181
  simp only [CollatzResearch.WordTrace]
  refine ⟨60187045634683540322398397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40124697089789026881598931 60187045634683540322398397)
  ·
    refine ⟨22570142113006327620899399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60187045634683540322398397 22570142113006327620899399)
    ·
      refine ⟨33855213169509491431349099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22570142113006327620899399 33855213169509491431349099)
      ·
        refine ⟨50782819754264237147023649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33855213169509491431349099 50782819754264237147023649)
        ·
          refine ⟨38087114815698177860267737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50782819754264237147023649 38087114815698177860267737)
          ·
            refine ⟨28565336111773633395200803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38087114815698177860267737 28565336111773633395200803)
            ·
              refine ⟨42848004167660450092801205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28565336111773633395200803 42848004167660450092801205)
              ·
                refine ⟨4017000390718167196200113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42848004167660450092801205 4017000390718167196200113)
                ·
                  refine ⟨3012750293038625397150085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4017000390718167196200113 3012750293038625397150085)
                  ·
                    refine ⟨564890679944742261965641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012750293038625397150085 564890679944742261965641)
                    ·
                      rfl

theorem cell22_1650181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_1650181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650181 prefixEnd_1650181 := by exact prefixLift 1650181
  have htrace : WordTrace (prefixWord ++ tailWord_1650181) baseStart_1650181 baseEnd_1650181 := by
    simpa [prefixWord, tailWord_1650181, baseEnd_1650181] using wordTrace_append hprefix tailTrace_1650181
  have hstable : (prefixWord ++ tailWord_1650181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650181).length < 2 ^ (prefixWord ++ tailWord_1650181).sum := by decide
  have hdescent : baseEnd_1650181 < baseStart_1650181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650183 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 4, 3]
def baseStart_1650183 : Nat := 118140960795 + 1650183 * 2 ^ 59
def prefixEnd_1650183 : Nat := 4983230072969 + 3 ^ 40 * 1650183 * 2
def baseEnd_1650183 : Nat := 564891364585614923415635

theorem tailTrace_1650183 : CollatzResearch.WordTrace tailWord_1650183 prefixEnd_1650183 564891364585614923415635 := by
  unfold tailWord_1650183
  simp only [CollatzResearch.WordTrace]
  refine ⟨60187118580676294663971203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40124745720450863109314135 60187118580676294663971203)
  ·
    refine ⟨90280677871014441995956805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60187118580676294663971203 90280677871014441995956805)
    ·
      refine ⟨16927627100815207874241901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90280677871014441995956805 16927627100815207874241901)
      ·
        refine ⟨6347860162805702952840713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16927627100815207874241901 6347860162805702952840713)
        ·
          refine ⟨4760895122104277214630535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6347860162805702952840713 4760895122104277214630535)
          ·
            refine ⟨7141342683156415821945803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760895122104277214630535 7141342683156415821945803)
            ·
              refine ⟨10712014024734623732918705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7141342683156415821945803 10712014024734623732918705)
              ·
                refine ⟨8034010518550967799689029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10712014024734623732918705 8034010518550967799689029)
                ·
                  refine ⟨1506376972228306462441693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8034010518550967799689029 1506376972228306462441693)
                  ·
                    refine ⟨564891364585614923415635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506376972228306462441693 564891364585614923415635)
                    ·
                      rfl

theorem cell22_1650183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_1650183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650183 prefixEnd_1650183 := by exact prefixLift 1650183
  have htrace : WordTrace (prefixWord ++ tailWord_1650183) baseStart_1650183 baseEnd_1650183 := by
    simpa [prefixWord, tailWord_1650183, baseEnd_1650183] using wordTrace_append hprefix tailTrace_1650183
  have hstable : (prefixWord ++ tailWord_1650183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650183).length < 2 ^ (prefixWord ++ tailWord_1650183).sum := by decide
  have hdescent : baseEnd_1650183 < baseStart_1650183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650245 : List Nat := [1, 3, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_1650245 : Nat := 118140960795 + 1650245 * 2 ^ 59
def prefixEnd_1650245 : Nat := 4983230072969 + 3 ^ 40 * 1650245 * 2
def baseEnd_1650245 : Nat := 564912588452667428365445

theorem tailTrace_1650245 : CollatzResearch.WordTrace tailWord_1650245 prefixEnd_1650245 564912588452667428365445 := by
  unfold tailWord_1650245
  simp only [CollatzResearch.WordTrace]
  refine ⟨60189379906451679252728189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40126253270967786168485459 60189379906451679252728189)
  ·
    refine ⟨22571017464919379719773071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60189379906451679252728189 22571017464919379719773071)
    ·
      refine ⟨33856526197379069579659607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22571017464919379719773071 33856526197379069579659607)
      ·
        refine ⟨50784789296068604369489411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33856526197379069579659607 50784789296068604369489411)
        ·
          refine ⟨76177183944102906554234117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50784789296068604369489411 76177183944102906554234117)
          ·
            refine ⟨14283221989519294978918897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76177183944102906554234117 14283221989519294978918897)
            ·
              refine ⟨10712416492139471234189173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14283221989519294978918897 10712416492139471234189173)
              ·
                refine ⟨1004289046138075428205235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10712416492139471234189173 1004289046138075428205235)
                ·
                  refine ⟨1506433569207113142307853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004289046138075428205235 1506433569207113142307853)
                  ·
                    refine ⟨564912588452667428365445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506433569207113142307853 564912588452667428365445)
                    ·
                      rfl

theorem cell22_1650245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_1650245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650245 prefixEnd_1650245 := by exact prefixLift 1650245
  have htrace : WordTrace (prefixWord ++ tailWord_1650245) baseStart_1650245 baseEnd_1650245 := by
    simpa [prefixWord, tailWord_1650245, baseEnd_1650245] using wordTrace_append hprefix tailTrace_1650245
  have hstable : (prefixWord ++ tailWord_1650245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650245).length < 2 ^ (prefixWord ++ tailWord_1650245).sum := by decide
  have hdescent : baseEnd_1650245 < baseStart_1650245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650256 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_1650256 : Nat := 118140960795 + 1650256 * 2 ^ 59
def prefixEnd_1650256 : Nat := 4983230072969 + 3 ^ 40 * 1650256 * 2
def baseEnd_1650256 : Nat := 564916353977467066340411

theorem tailTrace_1650256 : CollatzResearch.WordTrace tailWord_1650256 prefixEnd_1650256 564916353977467066340411 := by
  unfold tailWord_1650256
  simp only [CollatzResearch.WordTrace]
  refine ⟨30094890554705914065689311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40126520739607885420919081 30094890554705914065689311)
  ·
    refine ⟨45142335832058871098533967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30094890554705914065689311 45142335832058871098533967)
    ·
      refine ⟨67713503748088306647800951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45142335832058871098533967 67713503748088306647800951)
      ·
        refine ⟨101570255622132459971701427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67713503748088306647800951 101570255622132459971701427)
        ·
          refine ⟨152355383433198689957552141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101570255622132459971701427 152355383433198689957552141)
          ·
            refine ⟨57133268787449508734082053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152355383433198689957552141 57133268787449508734082053)
            ·
              refine ⟨10712487897646782887640385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57133268787449508734082053 10712487897646782887640385)
              ·
                refine ⟨8034365923235087165730289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10712487897646782887640385 8034365923235087165730289)
                ·
                  refine ⟨6025774442426315374297717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8034365923235087165730289 6025774442426315374297717)
                  ·
                    refine ⟨564916353977467066340411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6025774442426315374297717 564916353977467066340411)
                    ·
                      rfl

theorem cell22_1650256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_1650256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650256 prefixEnd_1650256 := by exact prefixLift 1650256
  have htrace : WordTrace (prefixWord ++ tailWord_1650256) baseStart_1650256 baseEnd_1650256 := by
    simpa [prefixWord, tailWord_1650256, baseEnd_1650256] using wordTrace_append hprefix tailTrace_1650256
  have hstable : (prefixWord ++ tailWord_1650256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650256).length < 2 ^ (prefixWord ++ tailWord_1650256).sum := by decide
  have hdescent : baseEnd_1650256 < baseStart_1650256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650258 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_1650258 : Nat := 118140960795 + 1650258 * 2 ^ 59
def prefixEnd_1650258 : Nat := 4983230072969 + 3 ^ 40 * 1650258 * 2
def baseEnd_1650258 : Nat := 188305679539446575930135

theorem tailTrace_1650258 : CollatzResearch.WordTrace tailWord_1650258 prefixEnd_1650258 188305679539446575930135 := by
  unfold tailWord_1650258
  simp only [CollatzResearch.WordTrace]
  refine ⟨15047463513851145618237857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40126569370269721648634285 15047463513851145618237857)
  ·
    refine ⟨11285597635388359213678393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15047463513851145618237857 11285597635388359213678393)
    ·
      refine ⟨8464198226541269410258795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11285597635388359213678393 8464198226541269410258795)
      ·
        refine ⟨12696297339811904115388193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8464198226541269410258795 12696297339811904115388193)
        ·
          refine ⟨9522223004858928086541145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12696297339811904115388193 9522223004858928086541145)
          ·
            refine ⟨7141667253644196064905859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9522223004858928086541145 7141667253644196064905859)
            ·
              refine ⟨10712500880466294097358789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7141667253644196064905859 10712500880466294097358789)
              ·
                refine ⟨2008593915087430143254773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10712500880466294097358789 2008593915087430143254773)
                ·
                  refine ⟨188305679539446575930135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2008593915087430143254773 188305679539446575930135)
                  ·
                    rfl

theorem cell22_1650258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_1650258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650258 prefixEnd_1650258 := by exact prefixLift 1650258
  have htrace : WordTrace (prefixWord ++ tailWord_1650258) baseStart_1650258 baseEnd_1650258 := by
    simpa [prefixWord, tailWord_1650258, baseEnd_1650258] using wordTrace_append hprefix tailTrace_1650258
  have hstable : (prefixWord ++ tailWord_1650258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650258).length < 2 ^ (prefixWord ++ tailWord_1650258).sum := by decide
  have hdescent : baseEnd_1650258 < baseStart_1650258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650288 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_1650288 : Nat := 118140960795 + 1650288 * 2 ^ 59
def prefixEnd_1650288 : Nat := 4983230072969 + 3 ^ 40 * 1650288 * 2
def baseEnd_1650288 : Nat := 564927308231429649540313

theorem tailTrace_1650288 : CollatzResearch.WordTrace tailWord_1650288 prefixEnd_1650288 564927308231429649540313 := by
  unfold tailWord_1650288
  simp only [CollatzResearch.WordTrace]
  refine ⟨30095474122647948798271759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40127298830197265064362345 30095474122647948798271759)
  ·
    refine ⟨45143211183971923197407639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30095474122647948798271759 45143211183971923197407639)
    ·
      refine ⟨67714816775957884796111459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45143211183971923197407639 67714816775957884796111459)
      ·
        refine ⟨101572225163936827194167189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67714816775957884796111459 101572225163936827194167189)
        ·
          refine ⟨4761198054559538774726587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101572225163936827194167189 4761198054559538774726587)
          ·
            refine ⟨7141797081839308162089881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761198054559538774726587 7141797081839308162089881)
            ·
              refine ⟨5356347811379481121567411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7141797081839308162089881 5356347811379481121567411)
              ·
                refine ⟨8034521717069221682351117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356347811379481121567411 8034521717069221682351117)
                ·
                  refine ⟨3012945643900958130881669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8034521717069221682351117 3012945643900958130881669)
                  ·
                    refine ⟨564927308231429649540313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012945643900958130881669 564927308231429649540313)
                    ·
                      rfl

theorem cell22_1650288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_1650288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650288 prefixEnd_1650288 := by exact prefixLift 1650288
  have htrace : WordTrace (prefixWord ++ tailWord_1650288) baseStart_1650288 baseEnd_1650288 := by
    simpa [prefixWord, tailWord_1650288, baseEnd_1650288] using wordTrace_append hprefix tailTrace_1650288
  have hstable : (prefixWord ++ tailWord_1650288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650288).length < 2 ^ (prefixWord ++ tailWord_1650288).sum := by decide
  have hdescent : baseEnd_1650288 < baseStart_1650288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650305 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1650305 : Nat := 118140960795 + 1650305 * 2 ^ 59
def prefixEnd_1650305 : Nat := 4983230072969 + 3 ^ 40 * 1650305 * 2
def baseEnd_1650305 : Nat := 564933127678847271865261

theorem tailTrace_1650305 : CollatzResearch.WordTrace tailWord_1650305 prefixEnd_1650305 564933127678847271865261 := by
  unfold tailWord_1650305
  simp only [CollatzResearch.WordTrace]
  refine ⟨60191568286234309499912369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40127712190822872999941579 60191568286234309499912369)
  ·
    refine ⟨45143676214675732124934277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60191568286234309499912369 45143676214675732124934277)
    ·
      refine ⟨8464439290251699773425177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45143676214675732124934277 8464439290251699773425177)
      ·
        refine ⟨6348329467688774830068883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8464439290251699773425177 6348329467688774830068883)
        ·
          refine ⟨9522494201533162245103325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6348329467688774830068883 9522494201533162245103325)
          ·
            refine ⟨3570935325574935841913747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9522494201533162245103325 3570935325574935841913747)
            ·
              refine ⟨5356402988362403762870621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570935325574935841913747 5356402988362403762870621)
              ·
                refine ⟨2008651120635901411076483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5356402988362403762870621 2008651120635901411076483)
                ·
                  refine ⟨3012976680953852116614725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008651120635901411076483 3012976680953852116614725)
                  ·
                    refine ⟨564933127678847271865261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3012976680953852116614725 564933127678847271865261)
                    ·
                      rfl

theorem cell22_1650305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1650305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650305 prefixEnd_1650305 := by exact prefixLift 1650305
  have htrace : WordTrace (prefixWord ++ tailWord_1650305) baseStart_1650305 baseEnd_1650305 := by
    simpa [prefixWord, tailWord_1650305, baseEnd_1650305] using wordTrace_append hprefix tailTrace_1650305
  have hstable : (prefixWord ++ tailWord_1650305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650305).length < 2 ^ (prefixWord ++ tailWord_1650305).sum := by decide
  have hdescent : baseEnd_1650305 < baseStart_1650305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650363 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 5, 3]
def baseStart_1650363 : Nat := 118140960795 + 1650363 * 2 ^ 59
def prefixEnd_1650363 : Nat := 4983230072969 + 3 ^ 40 * 1650363 * 2
def baseEnd_1650363 : Nat := 564952982264154453915083

theorem tailTrace_1650363 : CollatzResearch.WordTrace tailWord_1650363 prefixEnd_1650363 564952982264154453915083 := by
  unfold tailWord_1650363
  simp only [CollatzResearch.WordTrace]
  refine ⟨60193683720024185405523743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40129122480016123603682495 60193683720024185405523743)
  ·
    refine ⟨90290525580036278108285615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60193683720024185405523743 90290525580036278108285615)
    ·
      refine ⟨135435788370054417162428423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90290525580036278108285615 135435788370054417162428423)
      ·
        refine ⟨203153682555081625743642635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135435788370054417162428423 203153682555081625743642635)
        ·
          refine ⟨304730523832622438615463953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203153682555081625743642635 304730523832622438615463953)
          ·
            refine ⟨228547892874466828961597965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304730523832622438615463953 228547892874466828961597965)
            ·
              refine ⟨85705459827925060860599237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228547892874466828961597965 85705459827925060860599237)
              ·
                refine ⟨16069773717735948911362357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85705459827925060860599237 16069773717735948911362357)
                ·
                  refine ⟨1506541286037745210440221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16069773717735948911362357 1506541286037745210440221)
                  ·
                    refine ⟨564952982264154453915083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506541286037745210440221 564952982264154453915083)
                    ·
                      rfl

theorem cell22_1650363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 3].length) (baseStart_1650363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650363 prefixEnd_1650363 := by exact prefixLift 1650363
  have htrace : WordTrace (prefixWord ++ tailWord_1650363) baseStart_1650363 baseEnd_1650363 := by
    simpa [prefixWord, tailWord_1650363, baseEnd_1650363] using wordTrace_append hprefix tailTrace_1650363
  have hstable : (prefixWord ++ tailWord_1650363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650363).length < 2 ^ (prefixWord ++ tailWord_1650363).sum := by decide
  have hdescent : baseEnd_1650363 < baseStart_1650363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650455 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 6]
def baseStart_1650455 : Nat := 118140960795 + 1650455 * 2 ^ 59
def prefixEnd_1650455 : Nat := 4983230072969 + 3 ^ 40 * 1650455 * 2
def baseEnd_1650455 : Nat := 188328158581432293538267

theorem tailTrace_1650455 : CollatzResearch.WordTrace tailWord_1650455 prefixEnd_1650455 188328158581432293538267 := by
  unfold tailWord_1650455
  simp only [CollatzResearch.WordTrace]
  refine ⟨60197039235690885117872819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40131359490460590078581879 60197039235690885117872819)
  ·
    refine ⟨90295558853536327676809229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60197039235690885117872819 90295558853536327676809229)
    ·
      refine ⟨33860834570076122878803461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90295558853536327676809229 33860834570076122878803461)
      ·
        refine ⟨6348906481889273039775649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33860834570076122878803461 6348906481889273039775649)
        ·
          refine ⟨4761679861416954779831737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6348906481889273039775649 4761679861416954779831737)
          ·
            refine ⟨3571259896062716084873803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4761679861416954779831737 3571259896062716084873803)
            ·
              refine ⟨5356889844094074127310705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571259896062716084873803 5356889844094074127310705)
              ·
                refine ⟨4017667383070555595483029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356889844094074127310705 4017667383070555595483029)
                ·
                  refine ⟨188328158581432293538267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4017667383070555595483029 188328158581432293538267)
                  ·
                    rfl

theorem cell22_1650455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 6].length) (baseStart_1650455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650455 prefixEnd_1650455 := by exact prefixLift 1650455
  have htrace : WordTrace (prefixWord ++ tailWord_1650455) baseStart_1650455 baseEnd_1650455 := by
    simpa [prefixWord, tailWord_1650455, baseEnd_1650455] using wordTrace_append hprefix tailTrace_1650455
  have hstable : (prefixWord ++ tailWord_1650455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650455).length < 2 ^ (prefixWord ++ tailWord_1650455).sum := by decide
  have hdescent : baseEnd_1650455 < baseStart_1650455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650472 : List Nat := [2, 1, 5, 1, 1, 2, 1, 5, 4]
def baseStart_1650472 : Nat := 118140960795 + 1650472 * 2 ^ 59
def prefixEnd_1650472 : Nat := 4983230072969 + 3 ^ 40 * 1650472 * 2
def baseEnd_1650472 : Nat := 188330098397238167646583

theorem tailTrace_1650472 : CollatzResearch.WordTrace tailWord_1650472 prefixEnd_1650472 188330098397238167646583 := by
  unfold tailWord_1650472
  simp only [CollatzResearch.WordTrace]
  refine ⟨30098829638314648510620835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40131772851086198014161113 30098829638314648510620835)
  ·
    refine ⟨45148244457471972765931253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30098829638314648510620835 45148244457471972765931253)
    ·
      refine ⟨4232647917887997446806055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45148244457471972765931253 4232647917887997446806055)
      ·
        refine ⟨6348971876831996170209083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4232647917887997446806055 6348971876831996170209083)
        ·
          refine ⟨9523457815247994255313625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6348971876831996170209083 9523457815247994255313625)
          ·
            refine ⟨7142593361435995691485219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9523457815247994255313625 7142593361435995691485219)
            ·
              refine ⟨10713890042153993537227829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7142593361435995691485219 10713890042153993537227829)
              ·
                refine ⟨1004427191451936894115109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10713890042153993537227829 1004427191451936894115109)
                ·
                  refine ⟨188330098397238167646583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004427191451936894115109 188330098397238167646583)
                  ·
                    rfl

theorem cell22_1650472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 4].length) (baseStart_1650472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650472 prefixEnd_1650472 := by exact prefixLift 1650472
  have htrace : WordTrace (prefixWord ++ tailWord_1650472) baseStart_1650472 baseEnd_1650472 := by
    simpa [prefixWord, tailWord_1650472, baseEnd_1650472] using wordTrace_append hprefix tailTrace_1650472
  have hstable : (prefixWord ++ tailWord_1650472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650472).length < 2 ^ (prefixWord ++ tailWord_1650472).sum := by decide
  have hdescent : baseEnd_1650472 < baseStart_1650472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650504 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 2, 3]
def baseStart_1650504 : Nat := 118140960795 + 1650504 * 2 ^ 59
def prefixEnd_1650504 : Nat := 4983230072969 + 3 ^ 40 * 1650504 * 2
def baseEnd_1650504 : Nat := 565001249445677086139651

theorem tailTrace_1650504 : CollatzResearch.WordTrace tailWord_1650504 prefixEnd_1650504 565001249445677086139651 := by
  unfold tailWord_1650504
  simp only [CollatzResearch.WordTrace]
  refine ⟨30099413206256683243203283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40132550941675577657604377 30099413206256683243203283)
  ·
    refine ⟨45149119809385024864804925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30099413206256683243203283 45149119809385024864804925)
    ·
      refine ⟨16930919928519384324301847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45149119809385024864804925 16930919928519384324301847)
      ·
        refine ⟨25396379892779076486452771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16930919928519384324301847 25396379892779076486452771)
        ·
          refine ⟨38094569839168614729679157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25396379892779076486452771 38094569839168614729679157)
          ·
            refine ⟨3571365922422057630907421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38094569839168614729679157 3571365922422057630907421)
            ·
              refine ⟨1339262220908271611590283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3571365922422057630907421 1339262220908271611590283)
              ·
                refine ⟨2008893331362407417385425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339262220908271611590283 2008893331362407417385425)
                ·
                  refine ⟨1506669998521805563039069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2008893331362407417385425 1506669998521805563039069)
                  ·
                    refine ⟨565001249445677086139651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506669998521805563039069 565001249445677086139651)
                    ·
                      rfl

theorem cell22_1650504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_1650504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650504 prefixEnd_1650504 := by exact prefixLift 1650504
  have htrace : WordTrace (prefixWord ++ tailWord_1650504) baseStart_1650504 baseEnd_1650504 := by
    simpa [prefixWord, tailWord_1650504, baseEnd_1650504] using wordTrace_append hprefix tailTrace_1650504
  have hstable : (prefixWord ++ tailWord_1650504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650504).length < 2 ^ (prefixWord ++ tailWord_1650504).sum := by decide
  have hdescent : baseEnd_1650504 < baseStart_1650504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650517 : List Nat := [1, 3, 2, 2, 2, 4, 2, 6]
def baseStart_1650517 : Nat := 118140960795 + 1650517 * 2 ^ 59
def prefixEnd_1650517 : Nat := 4983230072969 + 3 ^ 40 * 1650517 * 2
def baseEnd_1650517 : Nat := 62778411067927709507179

theorem tailTrace_1650517 : CollatzResearch.WordTrace tailWord_1650517 prefixEnd_1650517 62778411067927709507179 := by
  unfold tailWord_1650517
  simp only [CollatzResearch.WordTrace]
  refine ⟨60199300561466269706629805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40132867040977513137753203 60199300561466269706629805)
  ·
    refine ⟨22574737710549851139986177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60199300561466269706629805 22574737710549851139986177)
    ·
      refine ⟨16931053282912388354989633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22574737710549851139986177 16931053282912388354989633)
      ·
        refine ⟨12698289962184291266242225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16931053282912388354989633 12698289962184291266242225)
        ·
          refine ⟨9523717471638218449681669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12698289962184291266242225 9523717471638218449681669)
          ·
            refine ⟨1785697025932165959315313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9523717471638218449681669 1785697025932165959315313)
            ·
              refine ⟨1339272769449124469486485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785697025932165959315313 1339272769449124469486485)
              ·
                refine ⟨62778411067927709507179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1339272769449124469486485 62778411067927709507179)
                ·
                  rfl

theorem cell22_1650517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 6].length) (baseStart_1650517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650517 prefixEnd_1650517 := by exact prefixLift 1650517
  have htrace : WordTrace (prefixWord ++ tailWord_1650517) baseStart_1650517 baseEnd_1650517 := by
    simpa [prefixWord, tailWord_1650517, baseEnd_1650517] using wordTrace_append hprefix tailTrace_1650517
  have hstable : (prefixWord ++ tailWord_1650517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650517).length < 2 ^ (prefixWord ++ tailWord_1650517).sum := by decide
  have hdescent : baseEnd_1650517 < baseStart_1650517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650545 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 5]
def baseStart_1650545 : Nat := 118140960795 + 1650545 * 2 ^ 59
def prefixEnd_1650545 : Nat := 4983230072969 + 3 ^ 40 * 1650545 * 2
def baseEnd_1650545 : Nat := 188338428194522215288175

theorem tailTrace_1650545 : CollatzResearch.WordTrace tailWord_1650545 prefixEnd_1650545 188338428194522215288175 := by
  unfold tailWord_1650545
  simp only [CollatzResearch.WordTrace]
  refine ⟨60200321805364830488649089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40133547870243220325766059 60200321805364830488649089)
  ·
    refine ⟨45150241354023622866486817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60200321805364830488649089 45150241354023622866486817)
    ·
      refine ⟨33862681015517717149865113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45150241354023622866486817 33862681015517717149865113)
      ·
        refine ⟨25397010761638287862398835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33862681015517717149865113 25397010761638287862398835)
        ·
          refine ⟨38095516142457431793598253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25397010761638287862398835 38095516142457431793598253)
          ·
            refine ⟨14285818553421536922599345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38095516142457431793598253 14285818553421536922599345)
            ·
              refine ⟨10714363915066152691949509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14285818553421536922599345 10714363915066152691949509)
              ·
                refine ⟨2008943234074903629740533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10714363915066152691949509 2008943234074903629740533)
                ·
                  refine ⟨188338428194522215288175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2008943234074903629740533 188338428194522215288175)
                  ·
                    rfl

theorem cell22_1650545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_1650545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650545 prefixEnd_1650545 := by exact prefixLift 1650545
  have htrace : WordTrace (prefixWord ++ tailWord_1650545) baseStart_1650545 baseEnd_1650545 := by
    simpa [prefixWord, tailWord_1650545, baseEnd_1650545] using wordTrace_append hprefix tailTrace_1650545
  have hstable : (prefixWord ++ tailWord_1650545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650545).length < 2 ^ (prefixWord ++ tailWord_1650545).sum := by decide
  have hdescent : baseEnd_1650545 < baseStart_1650545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650607 : List Nat := [1, 1, 2, 1, 2, 2, 5, 4, 4]
def baseStart_1650607 : Nat := 118140960795 + 1650607 * 2 ^ 59
def prefixEnd_1650607 : Nat := 4983230072969 + 3 ^ 40 * 1650607 * 2
def baseEnd_1650607 : Nat := 188345502816873050271445

theorem tailTrace_1650607 : CollatzResearch.WordTrace tailWord_1650607 prefixEnd_1650607 188345502816873050271445 := by
  unfold tailWord_1650607
  simp only [CollatzResearch.WordTrace]
  refine ⟨60202583131140215077406075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40135055420760143384937383 60202583131140215077406075)
  ·
    refine ⟨90303874696710322616109113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60202583131140215077406075 90303874696710322616109113)
    ·
      refine ⟨67727906022532741962081835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90303874696710322616109113 67727906022532741962081835)
      ·
        refine ⟨101591859033799112943122753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67727906022532741962081835 101591859033799112943122753)
        ·
          refine ⟨76193894275349334707342065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101591859033799112943122753 76193894275349334707342065)
          ·
            refine ⟨57145420706512001030506549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76193894275349334707342065 57145420706512001030506549)
            ·
              refine ⟨5357383191235500096609989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57145420706512001030506549 5357383191235500096609989)
              ·
                refine ⟨1004509348356656268114373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5357383191235500096609989 1004509348356656268114373)
                ·
                  refine ⟨188345502816873050271445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004509348356656268114373 188345502816873050271445)
                  ·
                    rfl

theorem cell22_1650607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 4].length) (baseStart_1650607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650607 prefixEnd_1650607 := by exact prefixLift 1650607
  have htrace : WordTrace (prefixWord ++ tailWord_1650607) baseStart_1650607 baseEnd_1650607 := by
    simpa [prefixWord, tailWord_1650607, baseEnd_1650607] using wordTrace_append hprefix tailTrace_1650607
  have hstable : (prefixWord ++ tailWord_1650607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650607).length < 2 ^ (prefixWord ++ tailWord_1650607).sum := by decide
  have hdescent : baseEnd_1650607 < baseStart_1650607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650622 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1650622 : Nat := 118140960795 + 1650622 * 2 ^ 59
def prefixEnd_1650622 : Nat := 4983230072969 + 3 ^ 40 * 1650622 * 2
def baseEnd_1650622 : Nat := 565041643257164111689289

theorem tailTrace_1650622 : CollatzResearch.WordTrace tailWord_1650622 prefixEnd_1650622 565041643257164111689289 := by
  unfold tailWord_1650622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525391278260734079900265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40135420150723915092801413 7525391278260734079900265)
  ·
    refine ⟨5644043458695550559925199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7525391278260734079900265 5644043458695550559925199)
    ·
      refine ⟨8466065188043325839887799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5644043458695550559925199 8466065188043325839887799)
      ·
        refine ⟨12699097782064988759831699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8466065188043325839887799 12699097782064988759831699)
        ·
          refine ⟨19048646673097483139747549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12699097782064988759831699 19048646673097483139747549)
          ·
            refine ⟨7143242502411556177405331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19048646673097483139747549 7143242502411556177405331)
            ·
              refine ⟨10714863753617334266107997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7143242502411556177405331 10714863753617334266107997)
              ·
                refine ⟨4018073907606500349790499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10714863753617334266107997 4018073907606500349790499)
                ·
                  refine ⟨6027110861409750524685749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018073907606500349790499 6027110861409750524685749)
                  ·
                    refine ⟨565041643257164111689289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6027110861409750524685749 565041643257164111689289)
                    ·
                      rfl

theorem cell22_1650622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1650622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650622 prefixEnd_1650622 := by exact prefixLift 1650622
  have htrace : WordTrace (prefixWord ++ tailWord_1650622) baseStart_1650622 baseEnd_1650622 := by
    simpa [prefixWord, tailWord_1650622, baseEnd_1650622] using wordTrace_append hprefix tailTrace_1650622
  have hstable : (prefixWord ++ tailWord_1650622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650622).length < 2 ^ (prefixWord ++ tailWord_1650622).sum := by decide
  have hdescent : baseEnd_1650622 < baseStart_1650622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650686 : List Nat := [4, 2, 2, 2, 1, 3, 2, 6]
def baseStart_1650686 : Nat := 118140960795 + 1650686 * 2 ^ 59
def prefixEnd_1650686 : Nat := 4983230072969 + 3 ^ 40 * 1650686 * 2
def baseEnd_1650686 : Nat := 62784839085009919787677

theorem tailTrace_1650686 : CollatzResearch.WordTrace tailWord_1650686 prefixEnd_1650686 62784839085009919787677 := by
  unfold tailWord_1650686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525683062231751446191489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40136976331902674379687941 7525683062231751446191489)
  ·
    refine ⟨5644262296673813584643617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7525683062231751446191489 5644262296673813584643617)
    ·
      refine ⟨4233196722505360188482713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5644262296673813584643617 4233196722505360188482713)
      ·
        refine ⟨3174897541879020141362035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4233196722505360188482713 3174897541879020141362035)
        ·
          refine ⟨4762346312818530212043053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174897541879020141362035 4762346312818530212043053)
          ·
            refine ⟨1785879867306948829516145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4762346312818530212043053 1785879867306948829516145)
            ·
              refine ⟨1339409900480211622137109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785879867306948829516145 1339409900480211622137109)
              ·
                refine ⟨62784839085009919787677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1339409900480211622137109 62784839085009919787677)
                ·
                  rfl

theorem cell22_1650686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_1650686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650686 prefixEnd_1650686 := by exact prefixLift 1650686
  have htrace : WordTrace (prefixWord ++ tailWord_1650686) baseStart_1650686 baseEnd_1650686 := by
    simpa [prefixWord, tailWord_1650686, baseEnd_1650686] using wordTrace_append hprefix tailTrace_1650686
  have hstable : (prefixWord ++ tailWord_1650686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650686).length < 2 ^ (prefixWord ++ tailWord_1650686).sum := by decide
  have hdescent : baseEnd_1650686 < baseStart_1650686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650744 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_1650744 : Nat := 118140960795 + 1650744 * 2 ^ 59
def prefixEnd_1650744 : Nat := 4983230072969 + 3 ^ 40 * 1650744 * 2
def baseEnd_1650744 : Nat := 565083406350396460138915

theorem tailTrace_1650744 : CollatzResearch.WordTrace tailWord_1650744 prefixEnd_1650744 565083406350396460138915 := by
  unfold tailWord_1650744
  simp only [CollatzResearch.WordTrace]
  refine ⟨30103789965821943737571643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40138386621095924983428857 30103789965821943737571643)
  ·
    refine ⟨45155684948732915606357465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30103789965821943737571643 45155684948732915606357465)
    ·
      refine ⟨33866763711549686704768099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45155684948732915606357465 33866763711549686704768099)
      ·
        refine ⟨50800145567324530057152149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33866763711549686704768099 50800145567324530057152149)
        ·
          refine ⟨2381256823468337346429007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50800145567324530057152149 2381256823468337346429007)
          ·
            refine ⟨3571885235202506019643511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381256823468337346429007 3571885235202506019643511)
            ·
              refine ⟨5357827852803759029465267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571885235202506019643511 5357827852803759029465267)
              ·
                refine ⟨8036741779205638544197901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357827852803759029465267 8036741779205638544197901)
                ·
                  refine ⟨3013778167202114454074213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8036741779205638544197901 3013778167202114454074213)
                  ·
                    refine ⟨565083406350396460138915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3013778167202114454074213 565083406350396460138915)
                    ·
                      rfl

theorem cell22_1650744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_1650744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650744 prefixEnd_1650744 := by exact prefixLift 1650744
  have htrace : WordTrace (prefixWord ++ tailWord_1650744) baseStart_1650744 baseEnd_1650744 := by
    simpa [prefixWord, tailWord_1650744, baseEnd_1650744] using wordTrace_append hprefix tailTrace_1650744
  have hstable : (prefixWord ++ tailWord_1650744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650744).length < 2 ^ (prefixWord ++ tailWord_1650744).sum := by decide
  have hdescent : baseEnd_1650744 < baseStart_1650744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650759 : List Nat := [1, 1, 4, 1, 3, 1, 2, 5, 4]
def baseStart_1650759 : Nat := 118140960795 + 1650759 * 2 ^ 59
def prefixEnd_1650759 : Nat := 4983230072969 + 3 ^ 40 * 1650759 * 2
def baseEnd_1650759 : Nat := 188362847052313807004623

theorem tailTrace_1650759 : CollatzResearch.WordTrace tailWord_1650759 prefixEnd_1650759 188362847052313807004623 := by
  unfold tailWord_1650759
  simp only [CollatzResearch.WordTrace]
  refine ⟨60208127026589545036939331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40138751351059696691292887 60208127026589545036939331)
  ·
    refine ⟨90312190539884317555408997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60208127026589545036939331 90312190539884317555408997)
    ·
      refine ⟨16933535726228309541639187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90312190539884317555408997 16933535726228309541639187)
      ·
        refine ⟨25400303589342464312458781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16933535726228309541639187 25400303589342464312458781)
        ·
          refine ⟨9525113846003424117172043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25400303589342464312458781 9525113846003424117172043)
          ·
            refine ⟨14287670769005136175758065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9525113846003424117172043 14287670769005136175758065)
            ·
              refine ⟨10715753076753852131818549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14287670769005136175758065 10715753076753852131818549)
              ·
                refine ⟨1004601850945673637357989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10715753076753852131818549 1004601850945673637357989)
                ·
                  refine ⟨188362847052313807004623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004601850945673637357989 188362847052313807004623)
                  ·
                    rfl

theorem cell22_1650759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 4].length) (baseStart_1650759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650759 prefixEnd_1650759 := by exact prefixLift 1650759
  have htrace : WordTrace (prefixWord ++ tailWord_1650759) baseStart_1650759 baseEnd_1650759 := by
    simpa [prefixWord, tailWord_1650759, baseEnd_1650759] using wordTrace_append hprefix tailTrace_1650759
  have hstable : (prefixWord ++ tailWord_1650759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650759).length < 2 ^ (prefixWord ++ tailWord_1650759).sum := by decide
  have hdescent : baseEnd_1650759 < baseStart_1650759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650772 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1650772 : Nat := 118140960795 + 1650772 * 2 ^ 59
def prefixEnd_1650772 : Nat := 4983230072969 + 3 ^ 40 * 1650772 * 2
def baseEnd_1650772 : Nat := 565092991322613720438829

theorem tailTrace_1650772 : CollatzResearch.WordTrace tailWord_1650772 prefixEnd_1650772 565092991322613720438829 := by
  unfold tailWord_1650772
  simp only [CollatzResearch.WordTrace]
  refine ⟨30104300587771224128581285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40139067450361632171441713 30104300587771224128581285)
  ·
    refine ⟨5644556360207104524108991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30104300587771224128581285 5644556360207104524108991)
    ·
      refine ⟨8466834540310656786163487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5644556360207104524108991 8466834540310656786163487)
      ·
        refine ⟨12700251810465985179245231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8466834540310656786163487 12700251810465985179245231)
        ·
          refine ⟨19050377715698977768867847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12700251810465985179245231 19050377715698977768867847)
          ·
            refine ⟨28575566573548466653301771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19050377715698977768867847 28575566573548466653301771)
            ·
              refine ⟨42863349860322699979952657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28575566573548466653301771 42863349860322699979952657)
              ·
                refine ⟨32147512395242024984964493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42863349860322699979952657 32147512395242024984964493)
                ·
                  refine ⟨12055317148215759369361685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32147512395242024984964493 12055317148215759369361685)
                  ·
                    refine ⟨565092991322613720438829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12055317148215759369361685 565092991322613720438829)
                    ·
                      rfl

theorem cell22_1650772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1650772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650772 prefixEnd_1650772 := by exact prefixLift 1650772
  have htrace : WordTrace (prefixWord ++ tailWord_1650772) baseStart_1650772 baseEnd_1650772 := by
    simpa [prefixWord, tailWord_1650772, baseEnd_1650772] using wordTrace_append hprefix tailTrace_1650772
  have hstable : (prefixWord ++ tailWord_1650772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650772).length < 2 ^ (prefixWord ++ tailWord_1650772).sum := by decide
  have hdescent : baseEnd_1650772 < baseStart_1650772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650776 : List Nat := [2, 1, 2, 2, 1, 4, 4, 2, 4]
def baseStart_1650776 : Nat := 118140960795 + 1650776 * 2 ^ 59
def prefixEnd_1650776 : Nat := 4983230072969 + 3 ^ 40 * 1650776 * 2
def baseEnd_1650776 : Nat := 188364786868119681112939

theorem tailTrace_1650776 : CollatzResearch.WordTrace tailWord_1650776 prefixEnd_1650776 188364786868119681112939 := by
  unfold tailWord_1650776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30104373533763978470154091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40139164711685304626872121 30104373533763978470154091)
  ·
    refine ⟨45156560300645967705231137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30104373533763978470154091 45156560300645967705231137)
    ·
      refine ⟨33867420225484475778923353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45156560300645967705231137 33867420225484475778923353)
      ·
        refine ⟨25400565169113356834192515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33867420225484475778923353 25400565169113356834192515)
        ·
          refine ⟨38100847753670035251288773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25400565169113356834192515 38100847753670035251288773)
          ·
            refine ⟨7143908953813131609616645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38100847753670035251288773 7143908953813131609616645)
            ·
              refine ⟨1339482928839962176803121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7143908953813131609616645 1339482928839962176803121)
              ·
                refine ⟨1004612196629971632602341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339482928839962176803121 1004612196629971632602341)
                ·
                  refine ⟨188364786868119681112939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004612196629971632602341 188364786868119681112939)
                  ·
                    rfl

theorem cell22_1650776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 4].length) (baseStart_1650776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650776 prefixEnd_1650776 := by exact prefixLift 1650776
  have htrace : WordTrace (prefixWord ++ tailWord_1650776) baseStart_1650776 baseEnd_1650776 := by
    simpa [prefixWord, tailWord_1650776, baseEnd_1650776] using wordTrace_append hprefix tailTrace_1650776
  have hstable : (prefixWord ++ tailWord_1650776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650776).length < 2 ^ (prefixWord ++ tailWord_1650776).sum := by decide
  have hdescent : baseEnd_1650776 < baseStart_1650776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650787 : List Nat := [1, 1, 1, 5, 1, 1, 5, 7]
def baseStart_1650787 : Nat := 118140960795 + 1650787 * 2 ^ 59
def prefixEnd_1650787 : Nat := 4983230072969 + 3 ^ 40 * 1650787 * 2
def baseEnd_1650787 : Nat := 62788680681017631257087

theorem tailTrace_1650787 : CollatzResearch.WordTrace tailWord_1650787 prefixEnd_1650787 62788680681017631257087 := by
  unfold tailWord_1650787
  simp only [CollatzResearch.WordTrace]
  refine ⟨60209148270488105818958615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40139432180325403879305743 60209148270488105818958615)
  ·
    refine ⟨90313722405732158728437923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60209148270488105818958615 90313722405732158728437923)
    ·
      refine ⟨135470583608598238092656885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90313722405732158728437923 135470583608598238092656885)
      ·
        refine ⟨12700367213306084821186583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135470583608598238092656885 12700367213306084821186583)
        ·
          refine ⟨19050550819959127231779875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12700367213306084821186583 19050550819959127231779875)
          ·
            refine ⟨28575826229938690847669813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19050550819959127231779875 28575826229938690847669813)
            ·
              refine ⟨2678983709056752266969045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28575826229938690847669813 2678983709056752266969045)
              ·
                refine ⟨62788680681017631257087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2678983709056752266969045 62788680681017631257087)
                ·
                  rfl

theorem cell22_1650787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 7].length) (baseStart_1650787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650787 prefixEnd_1650787 := by exact prefixLift 1650787
  have htrace : WordTrace (prefixWord ++ tailWord_1650787) baseStart_1650787 baseEnd_1650787 := by
    simpa [prefixWord, tailWord_1650787, baseEnd_1650787] using wordTrace_append hprefix tailTrace_1650787
  have hstable : (prefixWord ++ tailWord_1650787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650787).length < 2 ^ (prefixWord ++ tailWord_1650787).sum := by decide
  have hdescent : baseEnd_1650787 < baseStart_1650787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650806 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_1650806 : Nat := 118140960795 + 1650806 * 2 ^ 59
def prefixEnd_1650806 : Nat := 4983230072969 + 3 ^ 40 * 1650806 * 2
def baseEnd_1650806 : Nat := 565104630217448965088725

theorem tailTrace_1650806 : CollatzResearch.WordTrace tailWord_1650806 prefixEnd_1650806 565104630217448965088725 := by
  unfold tailWord_1650806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763115078588704503993767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40139894171612848042600181 3763115078588704503993767)
  ·
    refine ⟨5644672617883056755990651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3763115078588704503993767 5644672617883056755990651)
    ·
      refine ⟨8467008926824585133985977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5644672617883056755990651 8467008926824585133985977)
      ·
        refine ⟨6350256695118438850489483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8467008926824585133985977 6350256695118438850489483)
        ·
          refine ⟨9525385042677658275734225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6350256695118438850489483 9525385042677658275734225)
          ·
            refine ⟨7144038782008243706800669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9525385042677658275734225 7144038782008243706800669)
            ·
              refine ⟨2679014543253091390050251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7144038782008243706800669 2679014543253091390050251)
              ·
                refine ⟨4018521814879637085075377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679014543253091390050251 4018521814879637085075377)
                ·
                  refine ⟨3013891361159727813806533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4018521814879637085075377 3013891361159727813806533)
                  ·
                    refine ⟨565104630217448965088725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3013891361159727813806533 565104630217448965088725)
                    ·
                      rfl

theorem cell22_1650806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_1650806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650806 prefixEnd_1650806 := by exact prefixLift 1650806
  have htrace : WordTrace (prefixWord ++ tailWord_1650806) baseStart_1650806 baseEnd_1650806 := by
    simpa [prefixWord, tailWord_1650806, baseEnd_1650806] using wordTrace_append hprefix tailTrace_1650806
  have hstable : (prefixWord ++ tailWord_1650806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650806).length < 2 ^ (prefixWord ++ tailWord_1650806).sum := by decide
  have hdescent : baseEnd_1650806 < baseStart_1650806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650832 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 7]
def baseStart_1650832 : Nat := 118140960795 + 1650832 * 2 ^ 59
def prefixEnd_1650832 : Nat := 4983230072969 + 3 ^ 40 * 1650832 * 2
def baseEnd_1650832 : Nat := 188371176849597854646215

theorem tailTrace_1650832 : CollatzResearch.WordTrace tailWord_1650832 prefixEnd_1650832 188371176849597854646215 := by
  unfold tailWord_1650832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30105394777662539252173375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40140526370216719002897833 30105394777662539252173375)
  ·
    refine ⟨45158092166493808878260063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30105394777662539252173375 45158092166493808878260063)
    ·
      refine ⟨67737138249740713317390095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45158092166493808878260063 67737138249740713317390095)
      ·
        refine ⟨101605707374611069976085143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67737138249740713317390095 101605707374611069976085143)
        ·
          refine ⟨152408561061916604964127715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101605707374611069976085143 152408561061916604964127715)
          ·
            refine ⟨228612841592874907446191573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152408561061916604964127715 228612841592874907446191573)
            ·
              refine ⟨5358113474833005643270115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 228612841592874907446191573 5358113474833005643270115)
              ·
                refine ⟨8037170212249508464905173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5358113474833005643270115 8037170212249508464905173)
                ·
                  refine ⟨188371176849597854646215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8037170212249508464905173 188371176849597854646215)
                  ·
                    rfl

theorem cell22_1650832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_1650832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650832 prefixEnd_1650832 := by exact prefixLift 1650832
  have htrace : WordTrace (prefixWord ++ tailWord_1650832) baseStart_1650832 baseEnd_1650832 := by
    simpa [prefixWord, tailWord_1650832, baseEnd_1650832] using wordTrace_append hprefix tailTrace_1650832
  have hstable : (prefixWord ++ tailWord_1650832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650832).length < 2 ^ (prefixWord ++ tailWord_1650832).sum := by decide
  have hdescent : baseEnd_1650832 < baseStart_1650832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650973 : List Nat := [1, 4, 2, 3, 2, 1, 3, 6]
def baseStart_1650973 : Nat := 118140960795 + 1650973 * 2 ^ 59
def prefixEnd_1650973 : Nat := 4983230072969 + 3 ^ 40 * 1650973 * 2
def baseEnd_1650973 : Nat := 62795755303368466240357

theorem tailTrace_1650973 : CollatzResearch.WordTrace tailWord_1650973 prefixEnd_1650973 62795755303368466240357 := by
  unfold tailWord_1650973
  simp only [CollatzResearch.WordTrace]
  refine ⟨60215932247814259585229573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40143954831876173056819715 60215932247814259585229573)
  ·
    refine ⟨11290487296465173672230545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60215932247814259585229573 11290487296465173672230545)
    ·
      refine ⟨8467865472348880254172909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11290487296465173672230545 8467865472348880254172909)
      ·
        refine ⟨3175449552130830095314841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8467865472348880254172909 3175449552130830095314841)
        ·
          refine ⟨2381587164098122571486131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175449552130830095314841 2381587164098122571486131)
          ·
            refine ⟨3572380746147183857229197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381587164098122571486131 3572380746147183857229197)
            ·
              refine ⟨1339642779805193946460949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3572380746147183857229197 1339642779805193946460949)
              ·
                refine ⟨62795755303368466240357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1339642779805193946460949 62795755303368466240357)
                ·
                  rfl

theorem cell22_1650973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 6].length) (baseStart_1650973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650973 prefixEnd_1650973 := by exact prefixLift 1650973
  have htrace : WordTrace (prefixWord ++ tailWord_1650973) baseStart_1650973 baseEnd_1650973 := by
    simpa [prefixWord, tailWord_1650973, baseEnd_1650973] using wordTrace_append hprefix tailTrace_1650973
  have hstable : (prefixWord ++ tailWord_1650973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650973).length < 2 ^ (prefixWord ++ tailWord_1650973).sum := by decide
  have hdescent : baseEnd_1650973 < baseStart_1650973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650988 : List Nat := [2, 2, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_1650988 : Nat := 118140960795 + 1650988 * 2 ^ 59
def prefixEnd_1650988 : Nat := 4983230072969 + 3 ^ 40 * 1650988 * 2
def baseEnd_1650988 : Nat := 565166932536861157038167

theorem tailTrace_1650988 : CollatzResearch.WordTrace tailWord_1650988 prefixEnd_1650988 565166932536861157038167 := by
  unfold tailWord_1650988
  simp only [CollatzResearch.WordTrace]
  refine ⟨30108239671379958573512809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40144319561839944764683745 30108239671379958573512809)
  ·
    refine ⟨22581179753534968930134607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30108239671379958573512809 22581179753534968930134607)
    ·
      refine ⟨33871769630302453395201911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22581179753534968930134607 33871769630302453395201911)
      ·
        refine ⟨50807654445453680092802867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33871769630302453395201911 50807654445453680092802867)
        ·
          refine ⟨76211481668180520139204301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50807654445453680092802867 76211481668180520139204301)
          ·
            refine ⟨28579305625567695052201613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76211481668180520139204301 28579305625567695052201613)
            ·
              refine ⟨10717239609587885644575605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28579305625567695052201613 10717239609587885644575605)
              ·
                refine ⟨1004741213398864279178963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10717239609587885644575605 1004741213398864279178963)
                ·
                  refine ⟨1507111820098296418768445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004741213398864279178963 1507111820098296418768445)
                  ·
                    refine ⟨565166932536861157038167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1507111820098296418768445 565166932536861157038167)
                    ·
                      rfl

theorem cell22_1650988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_1650988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1650988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1650988 prefixEnd_1650988 := by exact prefixLift 1650988
  have htrace : WordTrace (prefixWord ++ tailWord_1650988) baseStart_1650988 baseEnd_1650988 := by
    simpa [prefixWord, tailWord_1650988, baseEnd_1650988] using wordTrace_append hprefix tailTrace_1650988
  have hstable : (prefixWord ++ tailWord_1650988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650988).length < 2 ^ (prefixWord ++ tailWord_1650988).sum := by decide
  have hdescent : baseEnd_1650988 < baseStart_1650988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651001 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 7]
def baseStart_1651001 : Nat := 118140960795 + 1651001 * 2 ^ 59
def prefixEnd_1651001 : Nat := 4983230072969 + 3 ^ 40 * 1651001 * 2
def baseEnd_1651001 : Nat := 188390460900844485487709

theorem tailTrace_1651001 : CollatzResearch.WordTrace tailWord_1651001 prefixEnd_1651001 188390460900844485487709 := by
  unfold tailWord_1651001
  simp only [CollatzResearch.WordTrace]
  refine ⟨60216953491712820367248857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40144635661141880244832571 60216953491712820367248857)
  ·
    refine ⟨45162715118784615275436643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60216953491712820367248857 45162715118784615275436643)
    ·
      refine ⟨67744072678176922913154965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45162715118784615275436643 67744072678176922913154965)
      ·
        refine ⟨3175503406789543261554139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67744072678176922913154965 3175503406789543261554139)
        ·
          refine ⟨4763255110184314892331209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175503406789543261554139 4763255110184314892331209)
          ·
            refine ⟨3572441332638236169248407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4763255110184314892331209 3572441332638236169248407)
            ·
              refine ⟨5358661998957354253872611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572441332638236169248407 5358661998957354253872611)
              ·
                refine ⟨8037992998436031380808917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5358661998957354253872611 8037992998436031380808917)
                ·
                  refine ⟨188390460900844485487709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8037992998436031380808917 188390460900844485487709)
                  ·
                    rfl

theorem cell22_1651001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_1651001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651001 prefixEnd_1651001 := by exact prefixLift 1651001
  have htrace : WordTrace (prefixWord ++ tailWord_1651001) baseStart_1651001 baseEnd_1651001 := by
    simpa [prefixWord, tailWord_1651001, baseEnd_1651001] using wordTrace_append hprefix tailTrace_1651001
  have hstable : (prefixWord ++ tailWord_1651001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651001).length < 2 ^ (prefixWord ++ tailWord_1651001).sum := by decide
  have hdescent : baseEnd_1651001 < baseStart_1651001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651048 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1651048 : Nat := 118140960795 + 1651048 * 2 ^ 59
def prefixEnd_1651048 : Nat := 4983230072969 + 3 ^ 40 * 1651048 * 2
def baseEnd_1651048 : Nat := 565187471763041000537983

theorem tailTrace_1651048 : CollatzResearch.WordTrace tailWord_1651048 prefixEnd_1651048 565187471763041000537983 := by
  unfold tailWord_1651048
  simp only [CollatzResearch.WordTrace]
  refine ⟨30109333861271273697104899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40145778481695031596139865 30109333861271273697104899)
  ·
    refine ⟨45164000791906910545657349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30109333861271273697104899 45164000791906910545657349)
    ·
      refine ⟨8468250148482545727310753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45164000791906910545657349 8468250148482545727310753)
      ·
        refine ⟨6351187611361909295483065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8468250148482545727310753 6351187611361909295483065)
        ·
          refine ⟨4763390708521431971612299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6351187611361909295483065 4763390708521431971612299)
          ·
            refine ⟨7145086062782147957418449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763390708521431971612299 7145086062782147957418449)
            ·
              refine ⟨5358814547086610968063837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7145086062782147957418449 5358814547086610968063837)
              ·
                refine ⟨2009555455157479113023939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5358814547086610968063837 2009555455157479113023939)
                ·
                  refine ⟨3014333182736218669535909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009555455157479113023939 3014333182736218669535909)
                  ·
                    refine ⟨565187471763041000537983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014333182736218669535909 565187471763041000537983)
                    ·
                      rfl

theorem cell22_1651048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1651048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651048 prefixEnd_1651048 := by exact prefixLift 1651048
  have htrace : WordTrace (prefixWord ++ tailWord_1651048) baseStart_1651048 baseEnd_1651048 := by
    simpa [prefixWord, tailWord_1651048, baseEnd_1651048] using wordTrace_append hprefix tailTrace_1651048
  have hstable : (prefixWord ++ tailWord_1651048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651048).length < 2 ^ (prefixWord ++ tailWord_1651048).sum := by decide
  have hdescent : baseEnd_1651048 < baseStart_1651048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651076 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1651076 : Nat := 118140960795 + 1651076 * 2 ^ 59
def prefixEnd_1651076 : Nat := 4983230072969 + 3 ^ 40 * 1651076 * 2
def baseEnd_1651076 : Nat := 565197056735258260837897

theorem tailTrace_1651076 : CollatzResearch.WordTrace tailWord_1651076 prefixEnd_1651076 565197056735258260837897 := by
  unfold tailWord_1651076
  simp only [CollatzResearch.WordTrace]
  refine ⟨30109844483220554088114541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40146459310960738784152721 30109844483220554088114541)
  ·
    refine ⟨11291191681207707783042953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30109844483220554088114541 11291191681207707783042953)
    ·
      refine ⟨8468393760905780837282215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11291191681207707783042953 8468393760905780837282215)
      ·
        refine ⟨12702590641358671255923323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8468393760905780837282215 12702590641358671255923323)
        ·
          refine ⟨19053885962038006883884985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12702590641358671255923323 19053885962038006883884985)
          ·
            refine ⟨14290414471528505162913739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19053885962038006883884985 14290414471528505162913739)
            ·
              refine ⟨21435621707292757744370609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14290414471528505162913739 21435621707292757744370609)
              ·
                refine ⟨16076716280469568308277957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21435621707292757744370609 16076716280469568308277957)
                ·
                  refine ⟨3014384302588044057802117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16076716280469568308277957 3014384302588044057802117)
                  ·
                    refine ⟨565197056735258260837897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014384302588044057802117 565197056735258260837897)
                    ·
                      rfl

theorem cell22_1651076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1651076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651076 prefixEnd_1651076 := by exact prefixLift 1651076
  have htrace : WordTrace (prefixWord ++ tailWord_1651076) baseStart_1651076 baseEnd_1651076 := by
    simpa [prefixWord, tailWord_1651076, baseEnd_1651076] using wordTrace_append hprefix tailTrace_1651076
  have hstable : (prefixWord ++ tailWord_1651076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651076).length < 2 ^ (prefixWord ++ tailWord_1651076).sum := by decide
  have hdescent : baseEnd_1651076 < baseStart_1651076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651082 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_1651082 : Nat := 118140960795 + 1651082 * 2 ^ 59
def prefixEnd_1651082 : Nat := 4983230072969 + 3 ^ 40 * 1651082 * 2
def baseEnd_1651082 : Nat := 565199110657876245187879

theorem tailTrace_1651082 : CollatzResearch.WordTrace tailWord_1651082 prefixEnd_1651082 565199110657876245187879 := by
  unfold tailWord_1651082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15054976951104842800236875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40146605202946247467298333 15054976951104842800236875)
  ·
    refine ⟨22582465426657264200355313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15054976951104842800236875 22582465426657264200355313)
    ·
      refine ⟨16936849069992948150266485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22582465426657264200355313 16936849069992948150266485)
      ·
        refine ⟨1587829600311838889087483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16936849069992948150266485 1587829600311838889087483)
        ·
          refine ⟨2381744400467758333631225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587829600311838889087483 2381744400467758333631225)
          ·
            refine ⟨1786308300350818750223419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2381744400467758333631225 1786308300350818750223419)
            ·
              refine ⟨2679462450526228125335129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786308300350818750223419 2679462450526228125335129)
              ·
                refine ⟨2009596837894671094001347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679462450526228125335129 2009596837894671094001347)
                ·
                  refine ⟨3014395256842006641002021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009596837894671094001347 3014395256842006641002021)
                  ·
                    refine ⟨565199110657876245187879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014395256842006641002021 565199110657876245187879)
                    ·
                      rfl

theorem cell22_1651082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_1651082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651082 prefixEnd_1651082 := by exact prefixLift 1651082
  have htrace : WordTrace (prefixWord ++ tailWord_1651082) baseStart_1651082 baseEnd_1651082 := by
    simpa [prefixWord, tailWord_1651082, baseEnd_1651082] using wordTrace_append hprefix tailTrace_1651082
  have hstable : (prefixWord ++ tailWord_1651082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651082).length < 2 ^ (prefixWord ++ tailWord_1651082).sum := by decide
  have hdescent : baseEnd_1651082 < baseStart_1651082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651112 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1651112 : Nat := 118140960795 + 1651112 * 2 ^ 59
def prefixEnd_1651112 : Nat := 4983230072969 + 3 ^ 40 * 1651112 * 2
def baseEnd_1651112 : Nat := 565209380270966166937787

theorem tailTrace_1651112 : CollatzResearch.WordTrace tailWord_1651112 prefixEnd_1651112 565209380270966166937787 := by
  unfold tailWord_1651112
  simp only [CollatzResearch.WordTrace]
  refine ⟨30110500997155343162269795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40147334662873790883026393 30110500997155343162269795)
  ·
    refine ⟨45165751495733014743404693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30110500997155343162269795 45165751495733014743404693)
    ·
      refine ⟨2117144601362485066097095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45165751495733014743404693 2117144601362485066097095)
      ·
        refine ⟨3175716902043727599145643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2117144601362485066097095 3175716902043727599145643)
        ·
          refine ⟨4763575353065591398718465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175716902043727599145643 4763575353065591398718465)
          ·
            refine ⟨3572681514799193549038849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4763575353065591398718465 3572681514799193549038849)
            ·
              refine ⟨2679511136099395161779137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572681514799193549038849 2679511136099395161779137)
              ·
                refine ⟨2009633352074546371334353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679511136099395161779137 2009633352074546371334353)
                ·
                  refine ⟨1507225014055909778500765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2009633352074546371334353 1507225014055909778500765)
                  ·
                    refine ⟨565209380270966166937787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1507225014055909778500765 565209380270966166937787)
                    ·
                      rfl

theorem cell22_1651112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1651112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651112 prefixEnd_1651112 := by exact prefixLift 1651112
  have htrace : WordTrace (prefixWord ++ tailWord_1651112) baseStart_1651112 baseEnd_1651112 := by
    simpa [prefixWord, tailWord_1651112, baseEnd_1651112] using wordTrace_append hprefix tailTrace_1651112
  have hstable : (prefixWord ++ tailWord_1651112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651112).length < 2 ^ (prefixWord ++ tailWord_1651112).sum := by decide
  have hdescent : baseEnd_1651112 < baseStart_1651112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651114 : List Nat := [3, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_1651114 : Nat := 118140960795 + 1651114 * 2 ^ 59
def prefixEnd_1651114 : Nat := 4983230072969 + 3 ^ 40 * 1651114 * 2
def baseEnd_1651114 : Nat := 188403354970612942795927

theorem tailTrace_1651114 : CollatzResearch.WordTrace tailWord_1651114 prefixEnd_1651114 188403354970612942795927 := by
  unfold tailWord_1651114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055268735075860166528099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40147383293535627110741597 15055268735075860166528099)
  ·
    refine ⟨22582903102613790249792149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15055268735075860166528099 22582903102613790249792149)
    ·
      refine ⟨1058573582935021417959007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22582903102613790249792149 1058573582935021417959007)
      ·
        refine ⟨1587860374402532126938511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058573582935021417959007 1587860374402532126938511)
        ·
          refine ⟨2381790561603798190407767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587860374402532126938511 2381790561603798190407767)
          ·
            refine ⟨3572685842405697285611651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381790561603798190407767 3572685842405697285611651)
            ·
              refine ⟨5359028763608545928417477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572685842405697285611651 5359028763608545928417477)
              ·
                refine ⟨1004817893176602361578277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5359028763608545928417477 1004817893176602361578277)
                ·
                  refine ⟨188403354970612942795927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004817893176602361578277 188403354970612942795927)
                  ·
                    rfl

theorem cell22_1651114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_1651114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651114 prefixEnd_1651114 := by exact prefixLift 1651114
  have htrace : WordTrace (prefixWord ++ tailWord_1651114) baseStart_1651114 baseEnd_1651114 := by
    simpa [prefixWord, tailWord_1651114, baseEnd_1651114] using wordTrace_append hprefix tailTrace_1651114
  have hstable : (prefixWord ++ tailWord_1651114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651114).length < 2 ^ (prefixWord ++ tailWord_1651114).sum := by decide
  have hdescent : baseEnd_1651114 < baseStart_1651114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651121 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_1651121 : Nat := 118140960795 + 1651121 * 2 ^ 59
def prefixEnd_1651121 : Nat := 4983230072969 + 3 ^ 40 * 1651121 * 2
def baseEnd_1651121 : Nat := 565212461154893143462759

theorem tailTrace_1651121 : CollatzResearch.WordTrace tailWord_1651121 prefixEnd_1651121 565212461154893143462759 := by
  unfold tailWord_1651121
  simp only [CollatzResearch.WordTrace]
  refine ⟨60221330251278080861617217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40147553500852053907744811 60221330251278080861617217)
  ·
    refine ⟨45165997688458560646212913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60221330251278080861617217 45165997688458560646212913)
    ·
      refine ⟨33874498266343920484659685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45165997688458560646212913 33874498266343920484659685)
      ·
        refine ⟨6351468424939485090873691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33874498266343920484659685 6351468424939485090873691)
        ·
          refine ⟨9527202637409227636310537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6351468424939485090873691 9527202637409227636310537)
          ·
            refine ⟨7145401978056920727232903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9527202637409227636310537 7145401978056920727232903)
            ·
              refine ⟨10718102967085381090849355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145401978056920727232903 10718102967085381090849355)
              ·
                refine ⟨16077154450628071636274033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10718102967085381090849355 16077154450628071636274033)
                ·
                  refine ⟨12057865837971053727205525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16077154450628071636274033 12057865837971053727205525)
                  ·
                    refine ⟨565212461154893143462759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12057865837971053727205525 565212461154893143462759)
                    ·
                      rfl

theorem cell22_1651121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_1651121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651121 prefixEnd_1651121 := by exact prefixLift 1651121
  have htrace : WordTrace (prefixWord ++ tailWord_1651121) baseStart_1651121 baseEnd_1651121 := by
    simpa [prefixWord, tailWord_1651121, baseEnd_1651121] using wordTrace_append hprefix tailTrace_1651121
  have hstable : (prefixWord ++ tailWord_1651121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651121).length < 2 ^ (prefixWord ++ tailWord_1651121).sum := by decide
  have hdescent : baseEnd_1651121 < baseStart_1651121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651125 : List Nat := [1, 3, 3, 2, 4, 1, 1, 7]
def baseStart_1651125 : Nat := 118140960795 + 1651125 * 2 ^ 59
def prefixEnd_1651125 : Nat := 4983230072969 + 3 ^ 40 * 1651125 * 2
def baseEnd_1651125 : Nat := 62801536715182051818083

theorem tailTrace_1651125 : CollatzResearch.WordTrace tailWord_1651125 prefixEnd_1651125 62801536715182051818083 := by
  unfold tailWord_1651125
  simp only [CollatzResearch.WordTrace]
  refine ⟨60221476143263589544762829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40147650762175726363175219 60221476143263589544762829)
  ·
    refine ⟨22583053553723846079286061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60221476143263589544762829 22583053553723846079286061)
    ·
      refine ⟨8468645082646442279732273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22583053553723846079286061 8468645082646442279732273)
      ·
        refine ⟨6351483811984831709799205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8468645082646442279732273 6351483811984831709799205)
        ·
          refine ⟨1190903214747155945587351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6351483811984831709799205 1190903214747155945587351)
          ·
            refine ⟨1786354822120733918381027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190903214747155945587351 1786354822120733918381027)
            ·
              refine ⟨2679532233181100877571541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786354822120733918381027 2679532233181100877571541)
              ·
                refine ⟨62801536715182051818083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2679532233181100877571541 62801536715182051818083)
                ·
                  rfl

theorem cell22_1651125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 7].length) (baseStart_1651125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651125 prefixEnd_1651125 := by exact prefixLift 1651125
  have htrace : WordTrace (prefixWord ++ tailWord_1651125) baseStart_1651125 baseEnd_1651125 := by
    simpa [prefixWord, tailWord_1651125, baseEnd_1651125] using wordTrace_append hprefix tailTrace_1651125
  have hstable : (prefixWord ++ tailWord_1651125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651125).length < 2 ^ (prefixWord ++ tailWord_1651125).sum := by decide
  have hdescent : baseEnd_1651125 < baseStart_1651125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651157 : List Nat := [1, 3, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_1651157 : Nat := 118140960795 + 1651157 * 2 ^ 59
def prefixEnd_1651157 : Nat := 4983230072969 + 3 ^ 40 * 1651157 * 2
def baseEnd_1651157 : Nat := 565224784690601049562649

theorem tailTrace_1651157 : CollatzResearch.WordTrace tailWord_1651157 prefixEnd_1651157 565224784690601049562649 := by
  unfold tailWord_1651157
  simp only [CollatzResearch.WordTrace]
  refine ⟨60222643279147659009927725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40148428852765106006618483 60222643279147659009927725)
  ·
    refine ⟨22583491229680372128722897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60222643279147659009927725 22583491229680372128722897)
    ·
      refine ⟨16937618422260279096542173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22583491229680372128722897 16937618422260279096542173)
      ·
        refine ⟨6351606908347604661203315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16937618422260279096542173 6351606908347604661203315)
        ·
          refine ⟨9527410362521406991804973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6351606908347604661203315 9527410362521406991804973)
          ·
            refine ⟨3572778885945527621926865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9527410362521406991804973 3572778885945527621926865)
            ·
              refine ⟨2679584164459145716445149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572778885945527621926865 2679584164459145716445149)
              ·
                refine ⟨1004844061672179643666931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2679584164459145716445149 1004844061672179643666931)
                ·
                  refine ⟨1507266092508269465500397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004844061672179643666931 1507266092508269465500397)
                  ·
                    refine ⟨565224784690601049562649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1507266092508269465500397 565224784690601049562649)
                    ·
                      rfl

theorem cell22_1651157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_1651157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651157 prefixEnd_1651157 := by exact prefixLift 1651157
  have htrace : WordTrace (prefixWord ++ tailWord_1651157) baseStart_1651157 baseEnd_1651157 := by
    simpa [prefixWord, tailWord_1651157, baseEnd_1651157] using wordTrace_append hprefix tailTrace_1651157
  have hstable : (prefixWord ++ tailWord_1651157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651157).length < 2 ^ (prefixWord ++ tailWord_1651157).sum := by decide
  have hdescent : baseEnd_1651157 < baseStart_1651157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651226 : List Nat := [3, 1, 1, 3, 1, 1, 12]
def baseStart_1651226 : Nat := 118140960795 + 1651226 * 2 ^ 59
def prefixEnd_1651226 : Nat := 4983230072969 + 3 ^ 40 * 1651226 * 2
def baseEnd_1651226 : Nat := 20935126103729921095831

theorem tailTrace_1651226 : CollatzResearch.WordTrace tailWord_1651226 prefixEnd_1651226 20935126103729921095831 := by
  unfold tailWord_1651226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15056289978974420948547383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40150106610598455862793021 15056289978974420948547383)
  ·
    refine ⟨22584434968461631422821075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15056289978974420948547383 22584434968461631422821075)
    ·
      refine ⟨33876652452692447134231613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22584434968461631422821075 33876652452692447134231613)
      ·
        refine ⟨12703744669759667675336855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33876652452692447134231613 12703744669759667675336855)
        ·
          refine ⟨19055617004639501513005283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12703744669759667675336855 19055617004639501513005283)
          ·
            refine ⟨28583425506959252269507925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19055617004639501513005283 28583425506959252269507925)
            ·
              refine ⟨20935126103729921095831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 28583425506959252269507925 20935126103729921095831)
              ·
                rfl

theorem cell22_1651226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 12].length) (baseStart_1651226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651226 prefixEnd_1651226 := by exact prefixLift 1651226
  have htrace : WordTrace (prefixWord ++ tailWord_1651226) baseStart_1651226 baseEnd_1651226 := by
    simpa [prefixWord, tailWord_1651226, baseEnd_1651226] using wordTrace_append hprefix tailTrace_1651226
  have hstable : (prefixWord ++ tailWord_1651226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651226).length < 2 ^ (prefixWord ++ tailWord_1651226).sum := by decide
  have hdescent : baseEnd_1651226 < baseStart_1651226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651228 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1651228 : Nat := 118140960795 + 1651228 * 2 ^ 59
def prefixEnd_1651228 : Nat := 4983230072969 + 3 ^ 40 * 1651228 * 2
def baseEnd_1651228 : Nat := 565249089441580531037431

theorem tailTrace_1651228 : CollatzResearch.WordTrace tailWord_1651228 prefixEnd_1651228 565249089441580531037431 := by
  unfold tailWord_1651228
  simp only [CollatzResearch.WordTrace]
  refine ⟨30112616430945219067881169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40150155241260292090508225 30112616430945219067881169)
  ·
    refine ⟨22584462323208914300910877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30112616430945219067881169 22584462323208914300910877)
    ·
      refine ⟨8469173371203342862841579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22584462323208914300910877 8469173371203342862841579)
      ·
        refine ⟨12703760056805014294262369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8469173371203342862841579 12703760056805014294262369)
        ·
          refine ⟨9527820042603760720696777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12703760056805014294262369 9527820042603760720696777)
          ·
            refine ⟨7145865031952820540522583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9527820042603760720696777 7145865031952820540522583)
            ·
              refine ⟨10718797547929230810783875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145865031952820540522583 10718797547929230810783875)
              ·
                refine ⟨16078196321893846216175813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10718797547929230810783875 16078196321893846216175813)
                ·
                  refine ⟨3014661810355096165532965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16078196321893846216175813 3014661810355096165532965)
                  ·
                    refine ⟨565249089441580531037431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014661810355096165532965 565249089441580531037431)
                    ·
                      rfl

theorem cell22_1651228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1651228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651228 prefixEnd_1651228 := by exact prefixLift 1651228
  have htrace : WordTrace (prefixWord ++ tailWord_1651228) baseStart_1651228 baseEnd_1651228 := by
    simpa [prefixWord, tailWord_1651228, baseEnd_1651228] using wordTrace_append hprefix tailTrace_1651228
  have hstable : (prefixWord ++ tailWord_1651228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651228).length < 2 ^ (prefixWord ++ tailWord_1651228).sum := by decide
  have hdescent : baseEnd_1651228 < baseStart_1651228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651232 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 6]
def baseStart_1651232 : Nat := 118140960795 + 1651232 * 2 ^ 59
def prefixEnd_1651232 : Nat := 4983230072969 + 3 ^ 40 * 1651232 * 2
def baseEnd_1651232 : Nat := 188416819574441951312473

theorem tailTrace_1651232 : CollatzResearch.WordTrace tailWord_1651232 prefixEnd_1651232 188416819574441951312473 := by
  unfold tailWord_1651232
  simp only [CollatzResearch.WordTrace]
  refine ⟨30112689376937973409453975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40150252502583964545938633 30112689376937973409453975)
  ·
    refine ⟨45169034065406960114180963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30112689376937973409453975 45169034065406960114180963)
    ·
      refine ⟨67753551098110440171271445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45169034065406960114180963 67753551098110440171271445)
      ·
        refine ⟨3175947707723926883028349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67753551098110440171271445 3175947707723926883028349)
        ·
          refine ⟨1190980390396472581135631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3175947707723926883028349 1190980390396472581135631)
          ·
            refine ⟨1786470585594708871703447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190980390396472581135631 1786470585594708871703447)
            ·
              refine ⟨2679705878392063307555171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786470585594708871703447 2679705878392063307555171)
              ·
                refine ⟨4019558817588094961332757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679705878392063307555171 4019558817588094961332757)
                ·
                  refine ⟨188416819574441951312473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4019558817588094961332757 188416819574441951312473)
                  ·
                    rfl

theorem cell22_1651232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_1651232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651232 prefixEnd_1651232 := by exact prefixLift 1651232
  have htrace : WordTrace (prefixWord ++ tailWord_1651232) baseStart_1651232 baseEnd_1651232 := by
    simpa [prefixWord, tailWord_1651232, baseEnd_1651232] using wordTrace_append hprefix tailTrace_1651232
  have hstable : (prefixWord ++ tailWord_1651232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651232).length < 2 ^ (prefixWord ++ tailWord_1651232).sum := by decide
  have hdescent : baseEnd_1651232 < baseStart_1651232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651288 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 5]
def baseStart_1651288 : Nat := 118140960795 + 1651288 * 2 ^ 59
def prefixEnd_1651288 : Nat := 4983230072969 + 3 ^ 40 * 1651288 * 2
def baseEnd_1651288 : Nat := 188423209555920124845749

theorem tailTrace_1651288 : CollatzResearch.WordTrace tailWord_1651288 prefixEnd_1651288 188423209555920124845749 := by
  unfold tailWord_1651288
  simp only [CollatzResearch.WordTrace]
  refine ⟨30113710620836534191473259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40151614161115378921964345 30113710620836534191473259)
  ·
    refine ⟨45170565931254801287209889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30113710620836534191473259 45170565931254801287209889)
    ·
      refine ⟨33877924448441100965407417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45170565931254801287209889 33877924448441100965407417)
      ·
        refine ⟨25408443336330825724055563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33877924448441100965407417 25408443336330825724055563)
        ·
          refine ⟨38112665004496238586083345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25408443336330825724055563 38112665004496238586083345)
          ·
            refine ⟨28584498753372178939562509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38112665004496238586083345 28584498753372178939562509)
            ·
              refine ⟨10719187032514567102335941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28584498753372178939562509 10719187032514567102335941)
              ·
                refine ⟨2009847568596481331687989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10719187032514567102335941 2009847568596481331687989)
                ·
                  refine ⟨188423209555920124845749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2009847568596481331687989 188423209555920124845749)
                  ·
                    rfl

theorem cell22_1651288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_1651288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651288 prefixEnd_1651288 := by exact prefixLift 1651288
  have htrace : WordTrace (prefixWord ++ tailWord_1651288) baseStart_1651288 baseEnd_1651288 := by
    simpa [prefixWord, tailWord_1651288, baseEnd_1651288] using wordTrace_append hprefix tailTrace_1651288
  have hstable : (prefixWord ++ tailWord_1651288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651288).length < 2 ^ (prefixWord ++ tailWord_1651288).sum := by decide
  have hdescent : baseEnd_1651288 < baseStart_1651288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651335 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1651335 : Nat := 118140960795 + 1651335 * 2 ^ 59
def prefixEnd_1651335 : Nat := 4983230072969 + 3 ^ 40 * 1651335 * 2
def baseEnd_1651335 : Nat := 565285717728267918612103

theorem tailTrace_1651335 : CollatzResearch.WordTrace tailWord_1651335 prefixEnd_1651335 565285717728267918612103 := by
  unfold tailWord_1651335
  simp only [CollatzResearch.WordTrace]
  refine ⟨60229135472502795409907459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40152756981668530273271639 60229135472502795409907459)
  ·
    refine ⟨90343703208754193114861189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60229135472502795409907459 90343703208754193114861189)
    ·
      refine ⟨16939444351641411209036473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90343703208754193114861189 16939444351641411209036473)
      ·
        refine ⟨12704583263731058406777355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16939444351641411209036473 12704583263731058406777355)
        ·
          refine ⟨19056874895596587610166033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12704583263731058406777355 19056874895596587610166033)
          ·
            refine ⟨14292656171697440707624525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19056874895596587610166033 14292656171697440707624525)
            ·
              refine ⟨5359746064386540265359197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14292656171697440707624525 5359746064386540265359197)
              ·
                refine ⟨2009904774144952599509699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5359746064386540265359197 2009904774144952599509699)
                ·
                  refine ⟨3014857161217428899264549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009904774144952599509699 3014857161217428899264549)
                  ·
                    refine ⟨565285717728267918612103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014857161217428899264549 565285717728267918612103)
                    ·
                      rfl

theorem cell22_1651335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1651335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651335 prefixEnd_1651335 := by exact prefixLift 1651335
  have htrace : WordTrace (prefixWord ++ tailWord_1651335) baseStart_1651335 baseEnd_1651335 := by
    simpa [prefixWord, tailWord_1651335, baseEnd_1651335] using wordTrace_append hprefix tailTrace_1651335
  have hstable : (prefixWord ++ tailWord_1651335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651335).length < 2 ^ (prefixWord ++ tailWord_1651335).sum := by decide
  have hdescent : baseEnd_1651335 < baseStart_1651335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651363 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 6, 4]
def baseStart_1651363 : Nat := 118140960795 + 1651363 * 2 ^ 59
def prefixEnd_1651363 : Nat := 4983230072969 + 3 ^ 40 * 1651363 * 2
def baseEnd_1651363 : Nat := 565295302700485178912017

theorem tailTrace_1651363 : CollatzResearch.WordTrace tailWord_1651363 prefixEnd_1651363 565295302700485178912017 := by
  unfold tailWord_1651363
  simp only [CollatzResearch.WordTrace]
  refine ⟨60230156716401356191926743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40153437810934237461284495 60230156716401356191926743)
  ·
    refine ⟨90345235074602034287890115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60230156716401356191926743 90345235074602034287890115)
    ·
      refine ⟨135517852611903051431835173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90345235074602034287890115 135517852611903051431835173)
      ·
        refine ⟨25409597364731822143469095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135517852611903051431835173 25409597364731822143469095)
        ·
          refine ⟨38114396047097733215203643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25409597364731822143469095 38114396047097733215203643)
          ·
            refine ⟨57171594070646599822805465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38114396047097733215203643 57171594070646599822805465)
            ·
              refine ⟨42878695552984949867104099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57171594070646599822805465 42878695552984949867104099)
              ·
                refine ⟨64318043329477424800656149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42878695552984949867104099 64318043329477424800656149)
                ·
                  refine ⟨3014908281069254287530757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64318043329477424800656149 3014908281069254287530757)
                  ·
                    refine ⟨565295302700485178912017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014908281069254287530757 565295302700485178912017)
                    ·
                      rfl

theorem cell22_1651363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 4].length) (baseStart_1651363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651363 prefixEnd_1651363 := by exact prefixLift 1651363
  have htrace : WordTrace (prefixWord ++ tailWord_1651363) baseStart_1651363 baseEnd_1651363 := by
    simpa [prefixWord, tailWord_1651363, baseEnd_1651363] using wordTrace_append hprefix tailTrace_1651363
  have hstable : (prefixWord ++ tailWord_1651363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651363).length < 2 ^ (prefixWord ++ tailWord_1651363).sum := by decide
  have hdescent : baseEnd_1651363 < baseStart_1651363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651412 : List Nat := [2, 4, 1, 3, 2, 1, 2, 7]
def baseStart_1651412 : Nat := 118140960795 + 1651412 * 2 ^ 59
def prefixEnd_1651412 : Nat := 4983230072969 + 3 ^ 40 * 1651412 * 2
def baseEnd_1651412 : Nat := 62812452933540598270763

theorem tailTrace_1651412 : CollatzResearch.WordTrace tailWord_1651412 prefixEnd_1651412 62812452933540598270763 := by
  unfold tailWord_1651412
  simp only [CollatzResearch.WordTrace]
  refine ⟨30115971946611918780230245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40154629262149225040306993 30115971946611918780230245)
  ·
    refine ⟨5646744739989734771293171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30115971946611918780230245 5646744739989734771293171)
    ·
      refine ⟨8470117109984602156939757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5646744739989734771293171 8470117109984602156939757)
      ·
        refine ⟨3176293916244225808852409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8470117109984602156939757 3176293916244225808852409)
        ·
          refine ⟨2382220437183169356639307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3176293916244225808852409 2382220437183169356639307)
          ·
            refine ⟨3573330655774754034958961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382220437183169356639307 3573330655774754034958961)
            ·
              refine ⟨2679997991831065526219221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3573330655774754034958961 2679997991831065526219221)
              ·
                refine ⟨62812452933540598270763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2679997991831065526219221 62812452933540598270763)
                ·
                  rfl

theorem cell22_1651412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 7].length) (baseStart_1651412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651412 prefixEnd_1651412 := by exact prefixLift 1651412
  have htrace : WordTrace (prefixWord ++ tailWord_1651412) baseStart_1651412 baseEnd_1651412 := by
    simpa [prefixWord, tailWord_1651412, baseEnd_1651412] using wordTrace_append hprefix tailTrace_1651412
  have hstable : (prefixWord ++ tailWord_1651412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651412).length < 2 ^ (prefixWord ++ tailWord_1651412).sum := by decide
  have hdescent : baseEnd_1651412 < baseStart_1651412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651500 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_1651500 : Nat := 118140960795 + 1651500 * 2 ^ 59
def prefixEnd_1651500 : Nat := 4983230072969 + 3 ^ 40 * 1651500 * 2
def baseEnd_1651500 : Nat := 565342200600262488236597

theorem tailTrace_1651500 : CollatzResearch.WordTrace tailWord_1651500 prefixEnd_1651500 565342200600262488236597 := by
  unfold tailWord_1651500
  simp only [CollatzResearch.WordTrace]
  refine ⟨30117576758452514294831977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40156769011270019059775969 30117576758452514294831977)
  ·
    refine ⟨22588182568839385721123983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30117576758452514294831977 22588182568839385721123983)
    ·
      refine ⟨33882273853259078581685975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22588182568839385721123983 33882273853259078581685975)
      ·
        refine ⟨50823410779888617872528963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33882273853259078581685975 50823410779888617872528963)
        ·
          refine ⟨76235116169832926808793445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50823410779888617872528963 76235116169832926808793445)
          ·
            refine ⟨14294084281843673776648771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76235116169832926808793445 14294084281843673776648771)
            ·
              refine ⟨21441126422765510664973157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14294084281843673776648771 21441126422765510664973157)
              ·
                refine ⟨4020211204268533249682467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21441126422765510664973157 4020211204268533249682467)
                ·
                  refine ⟨6030316806402799874523701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020211204268533249682467 6030316806402799874523701)
                  ·
                    refine ⟨565342200600262488236597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6030316806402799874523701 565342200600262488236597)
                    ·
                      rfl

theorem cell22_1651500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_1651500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651500 prefixEnd_1651500 := by exact prefixLift 1651500
  have htrace : WordTrace (prefixWord ++ tailWord_1651500) baseStart_1651500 baseEnd_1651500 := by
    simpa [prefixWord, tailWord_1651500, baseEnd_1651500] using wordTrace_append hprefix tailTrace_1651500
  have hstable : (prefixWord ++ tailWord_1651500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651500).length < 2 ^ (prefixWord ++ tailWord_1651500).sum := by decide
  have hdescent : baseEnd_1651500 < baseStart_1651500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651579 : List Nat := [1, 1, 1, 1, 1, 5, 2, 6, 1, 3]
def baseStart_1651579 : Nat := 118140960795 + 1651579 * 2 ^ 59
def prefixEnd_1651579 : Nat := 4983230072969 + 3 ^ 40 * 1651579 * 2
def baseEnd_1651579 : Nat := 565369243914732615511355

theorem tailTrace_1651579 : CollatzResearch.WordTrace tailWord_1651579 prefixEnd_1651579 565369243914732615511355 := by
  unfold tailWord_1651579
  simp only [CollatzResearch.WordTrace]
  refine ⟨60238034883618825081789791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40158689922412550054526527 60238034883618825081789791)
  ·
    refine ⟨90357052325428237622684687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60238034883618825081789791 90357052325428237622684687)
    ·
      refine ⟨135535578488142356434027031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90357052325428237622684687 135535578488142356434027031)
      ·
        refine ⟨203303367732213534651040547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135535578488142356434027031 203303367732213534651040547)
        ·
          refine ⟨304955051598320301976560821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203303367732213534651040547 304955051598320301976560821)
          ·
            refine ⟨28589536087342528310302577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 304955051598320301976560821 28589536087342528310302577)
            ·
              refine ⟨21442152065506896232726933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28589536087342528310302577 21442152065506896232726933)
              ·
                refine ⟨1005100878070635760909075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21442152065506896232726933 1005100878070635760909075)
                ·
                  refine ⟨1507651317105953641363613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005100878070635760909075 1507651317105953641363613)
                  ·
                    refine ⟨565369243914732615511355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1507651317105953641363613 565369243914732615511355)
                    ·
                      rfl

theorem cell22_1651579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 3].length) (baseStart_1651579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651579 prefixEnd_1651579 := by exact prefixLift 1651579
  have htrace : WordTrace (prefixWord ++ tailWord_1651579) baseStart_1651579 baseEnd_1651579 := by
    simpa [prefixWord, tailWord_1651579, baseEnd_1651579] using wordTrace_append hprefix tailTrace_1651579
  have hstable : (prefixWord ++ tailWord_1651579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651579).length < 2 ^ (prefixWord ++ tailWord_1651579).sum := by decide
  have hdescent : baseEnd_1651579 < baseStart_1651579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651637 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 6]
def baseStart_1651637 : Nat := 118140960795 + 1651637 * 2 ^ 59
def prefixEnd_1651637 : Nat := 4983230072969 + 3 ^ 40 * 1651637 * 2
def baseEnd_1651637 : Nat := 188463032833346599187059

theorem tailTrace_1651637 : CollatzResearch.WordTrace tailWord_1651637 prefixEnd_1651637 188463032833346599187059 := by
  unfold tailWord_1651637
  simp only [CollatzResearch.WordTrace]
  refine ⟨60240150317408700987401165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40160100211605800658267443 60240150317408700987401165)
  ·
    refine ⟨22590056369028262870275437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60240150317408700987401165 22590056369028262870275437)
    ·
      refine ⟨8471271138385598576353289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22590056369028262870275437 8471271138385598576353289)
      ·
        refine ⟨6353453353789198932264967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8471271138385598576353289 6353453353789198932264967)
        ·
          refine ⟨9530180030683798398397451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6353453353789198932264967 9530180030683798398397451)
          ·
            refine ⟨14295270046025697597596177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9530180030683798398397451 14295270046025697597596177)
            ·
              refine ⟨10721452534519273198197133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14295270046025697597596177 10721452534519273198197133)
              ·
                refine ⟨4020544700444727449323925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10721452534519273198197133 4020544700444727449323925)
                ·
                  refine ⟨188463032833346599187059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4020544700444727449323925 188463032833346599187059)
                  ·
                    rfl

theorem cell22_1651637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_1651637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651637 prefixEnd_1651637 := by exact prefixLift 1651637
  have htrace : WordTrace (prefixWord ++ tailWord_1651637) baseStart_1651637 baseEnd_1651637 := by
    simpa [prefixWord, tailWord_1651637, baseEnd_1651637] using wordTrace_append hprefix tailTrace_1651637
  have hstable : (prefixWord ++ tailWord_1651637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651637).length < 2 ^ (prefixWord ++ tailWord_1651637).sum := by decide
  have hdescent : baseEnd_1651637 < baseStart_1651637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651748 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_1651748 : Nat := 118140960795 + 1651748 * 2 ^ 59
def prefixEnd_1651748 : Nat := 4983230072969 + 3 ^ 40 * 1651748 * 2
def baseEnd_1651748 : Nat := 565427096068472508035837

theorem tailTrace_1651748 : CollatzResearch.WordTrace tailWord_1651748 prefixEnd_1651748 565427096068472508035837 := by
  unfold tailWord_1651748
  simp only [CollatzResearch.WordTrace]
  refine ⟨30122099410003283472345949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40162799213337711296461265 30122099410003283472345949)
  ·
    refine ⟨11295787278751231302129731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30122099410003283472345949 11295787278751231302129731)
    ·
      refine ⟨16943680918126846953194597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11295787278751231302129731 16943680918126846953194597)
      ·
        refine ⟨3176940172148783803723987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16943680918126846953194597 3176940172148783803723987)
        ·
          refine ⟨4765410258223175705585981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3176940172148783803723987 4765410258223175705585981)
          ·
            refine ⟨1787028846833690889594743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4765410258223175705585981 1787028846833690889594743)
            ·
              refine ⟨2680543270250536334392115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787028846833690889594743 2680543270250536334392115)
              ·
                refine ⟨4020814905375804501588173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680543270250536334392115 4020814905375804501588173)
                ·
                  refine ⟨1507805589515926688095565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4020814905375804501588173 1507805589515926688095565)
                  ·
                    refine ⟨565427096068472508035837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1507805589515926688095565 565427096068472508035837)
                    ·
                      rfl

theorem cell22_1651748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_1651748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651748 prefixEnd_1651748 := by exact prefixLift 1651748
  have htrace : WordTrace (prefixWord ++ tailWord_1651748) baseStart_1651748 baseEnd_1651748 := by
    simpa [prefixWord, tailWord_1651748, baseEnd_1651748] using wordTrace_append hprefix tailTrace_1651748
  have hstable : (prefixWord ++ tailWord_1651748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651748).length < 2 ^ (prefixWord ++ tailWord_1651748).sum := by decide
  have hdescent : baseEnd_1651748 < baseStart_1651748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651804 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1651804 : Nat := 118140960795 + 1651804 * 2 ^ 59
def prefixEnd_1651804 : Nat := 4983230072969 + 3 ^ 40 * 1651804 * 2
def baseEnd_1651804 : Nat := 565446266012907028635665

theorem tailTrace_1651804 : CollatzResearch.WordTrace tailWord_1651804 prefixEnd_1651804 565446266012907028635665 := by
  unfold tailWord_1651804
  simp only [CollatzResearch.WordTrace]
  refine ⟨30123120653901844254365233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40164160871869125672486977 30123120653901844254365233)
  ·
    refine ⟨22592340490426383190773925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30123120653901844254365233 22592340490426383190773925)
    ·
      refine ⟨4236063841954946848270111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22592340490426383190773925 4236063841954946848270111)
      ·
        refine ⟨6354095762932420272405167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236063841954946848270111 6354095762932420272405167)
        ·
          refine ⟨9531143644398630408607751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354095762932420272405167 9531143644398630408607751)
          ·
            refine ⟨14296715466597945612911627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9531143644398630408607751 14296715466597945612911627)
            ·
              refine ⟨21445073199896918419367441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14296715466597945612911627 21445073199896918419367441)
              ·
                refine ⟨16083804899922688814525581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21445073199896918419367441 16083804899922688814525581)
                ·
                  refine ⟨6031426837471008305447093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16083804899922688814525581 6031426837471008305447093)
                  ·
                    refine ⟨565446266012907028635665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6031426837471008305447093 565446266012907028635665)
                    ·
                      rfl

theorem cell22_1651804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1651804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651804 prefixEnd_1651804 := by exact prefixLift 1651804
  have htrace : WordTrace (prefixWord ++ tailWord_1651804) baseStart_1651804 baseEnd_1651804 := by
    simpa [prefixWord, tailWord_1651804, baseEnd_1651804] using wordTrace_append hprefix tailTrace_1651804
  have hstable : (prefixWord ++ tailWord_1651804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651804).length < 2 ^ (prefixWord ++ tailWord_1651804).sum := by decide
  have hdescent : baseEnd_1651804 < baseStart_1651804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651821 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1651821 : Nat := 118140960795 + 1651821 * 2 ^ 59
def prefixEnd_1651821 : Nat := 4983230072969 + 3 ^ 40 * 1651821 * 2
def baseEnd_1651821 : Nat := 565452085460324650960613

theorem tailTrace_1651821 : CollatzResearch.WordTrace tailWord_1651821 prefixEnd_1651821 565452085460324650960613 := by
  unfold tailWord_1651821
  simp only [CollatzResearch.WordTrace]
  refine ⟨60246861348742100412099317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40164574232494733608066211 60246861348742100412099317)
  ·
    refine ⟨5648143251444571913634311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60246861348742100412099317 5648143251444571913634311)
    ·
      refine ⟨8472214877166857870451467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5648143251444571913634311 8472214877166857870451467)
      ·
        refine ⟨12708322315750286805677201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8472214877166857870451467 12708322315750286805677201)
        ·
          refine ⟨9531241736812715104257901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12708322315750286805677201 9531241736812715104257901)
          ·
            refine ⟨3574215651304768164096713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9531241736812715104257901 3574215651304768164096713)
            ·
              refine ⟨2680661738478576123072535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3574215651304768164096713 2680661738478576123072535)
              ·
                refine ⟨4020992607717864184608803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680661738478576123072535 4020992607717864184608803)
                ·
                  refine ⟨6031488911576796276913205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020992607717864184608803 6031488911576796276913205)
                  ·
                    refine ⟨565452085460324650960613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6031488911576796276913205 565452085460324650960613)
                    ·
                      rfl

theorem cell22_1651821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1651821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651821 prefixEnd_1651821 := by exact prefixLift 1651821
  have htrace : WordTrace (prefixWord ++ tailWord_1651821) baseStart_1651821 baseEnd_1651821 := by
    simpa [prefixWord, tailWord_1651821, baseEnd_1651821] using wordTrace_append hprefix tailTrace_1651821
  have hstable : (prefixWord ++ tailWord_1651821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651821).length < 2 ^ (prefixWord ++ tailWord_1651821).sum := by decide
  have hdescent : baseEnd_1651821 < baseStart_1651821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651885 : List Nat := [1, 5, 2, 1, 4, 1, 2, 6]
def baseStart_1651885 : Nat := 118140960795 + 1651885 * 2 ^ 59
def prefixEnd_1651885 : Nat := 4983230072969 + 3 ^ 40 * 1651885 * 2
def baseEnd_1651885 : Nat := 62830443774249979706713

theorem tailTrace_1651885 : CollatzResearch.WordTrace tailWord_1651885 prefixEnd_1651885 62830443774249979706713 := by
  unfold tailWord_1651885
  simp only [CollatzResearch.WordTrace]
  refine ⟨60249195620510239342429109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40166130413673492894952739 60249195620510239342429109)
  ·
    refine ⟨5648362089422834938352729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60249195620510239342429109 5648362089422834938352729)
    ·
      refine ⟨4236271567067126203764547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5648362089422834938352729 4236271567067126203764547)
      ·
        refine ⟨6354407350600689305646821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236271567067126203764547 6354407350600689305646821)
        ·
          refine ⟨1191451378237629244808779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6354407350600689305646821 1191451378237629244808779)
          ·
            refine ⟨1787177067356443867213169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191451378237629244808779 1787177067356443867213169)
            ·
              refine ⟨1340382800517332900409877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1787177067356443867213169 1340382800517332900409877)
              ·
                refine ⟨62830443774249979706713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1340382800517332900409877 62830443774249979706713)
                ·
                  rfl

theorem cell22_1651885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 6].length) (baseStart_1651885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651885 prefixEnd_1651885 := by exact prefixLift 1651885
  have htrace : WordTrace (prefixWord ++ tailWord_1651885) baseStart_1651885 baseEnd_1651885 := by
    simpa [prefixWord, tailWord_1651885, baseEnd_1651885] using wordTrace_append hprefix tailTrace_1651885
  have hstable : (prefixWord ++ tailWord_1651885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651885).length < 2 ^ (prefixWord ++ tailWord_1651885).sum := by decide
  have hdescent : baseEnd_1651885 < baseStart_1651885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651900 : List Nat := [2, 2, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_1651900 : Nat := 118140960795 + 1651900 * 2 ^ 59
def prefixEnd_1651900 : Nat := 4983230072969 + 3 ^ 40 * 1651900 * 2
def baseEnd_1651900 : Nat := 565479128774794778235371

theorem tailTrace_1651900 : CollatzResearch.WordTrace tailWord_1651900 prefixEnd_1651900 565479128774794778235371 := by
  unfold tailWord_1651900
  simp only [CollatzResearch.WordTrace]
  refine ⟨30124871357727948452112577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40166495143637264602816769 30124871357727948452112577)
  ·
    refine ⟨22593653518295961339084433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30124871357727948452112577 22593653518295961339084433)
    ·
      refine ⟨16945240138721971004313325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22593653518295961339084433 16945240138721971004313325)
      ·
        refine ⟨6354465052020739126617497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16945240138721971004313325 6354465052020739126617497)
        ·
          refine ⟨4765848789015554344963123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6354465052020739126617497 4765848789015554344963123)
          ·
            refine ⟨7148773183523331517444685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765848789015554344963123 7148773183523331517444685)
            ·
              refine ⟨2680789943821249319041757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7148773183523331517444685 2680789943821249319041757)
              ·
                refine ⟨1005296228932968494640659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2680789943821249319041757 1005296228932968494640659)
                ·
                  refine ⟨1507944343399452741960989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005296228932968494640659 1507944343399452741960989)
                  ·
                    refine ⟨565479128774794778235371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1507944343399452741960989 565479128774794778235371)
                    ·
                      rfl

theorem cell22_1651900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_1651900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651900 prefixEnd_1651900 := by exact prefixLift 1651900
  have htrace : WordTrace (prefixWord ++ tailWord_1651900) baseStart_1651900 baseEnd_1651900 := by
    simpa [prefixWord, tailWord_1651900, baseEnd_1651900] using wordTrace_append hprefix tailTrace_1651900
  have hstable : (prefixWord ++ tailWord_1651900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651900).length < 2 ^ (prefixWord ++ tailWord_1651900).sum := by decide
  have hdescent : baseEnd_1651900 < baseStart_1651900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651909 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_1651909 : Nat := 118140960795 + 1651909 * 2 ^ 59
def prefixEnd_1651909 : Nat := 4983230072969 + 3 ^ 40 * 1651909 * 2
def baseEnd_1651909 : Nat := 565482209658721754760343

theorem tailTrace_1651909 : CollatzResearch.WordTrace tailWord_1651909 prefixEnd_1651909 565482209658721754760343 := by
  unfold tailWord_1651909
  simp only [CollatzResearch.WordTrace]
  refine ⟨60250070972423291441302781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40166713981615527627535187 60250070972423291441302781)
  ·
    refine ⟨22593776614658734290488543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60250070972423291441302781 22593776614658734290488543)
    ·
      refine ⟨33890664921988101435732815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22593776614658734290488543 33890664921988101435732815)
      ·
        refine ⟨50835997382982152153599223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33890664921988101435732815 50835997382982152153599223)
        ·
          refine ⟨76253996074473228230398835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50835997382982152153599223 76253996074473228230398835)
          ·
            refine ⟨114380994111709842345598253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76253996074473228230398835 114380994111709842345598253)
            ·
              refine ⟨42892872791891190879599345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114380994111709842345598253 42892872791891190879599345)
              ·
                refine ⟨32169654593918393159699509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42892872791891190879599345 32169654593918393159699509)
                ·
                  refine ⟨3015905118179849358721829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32169654593918393159699509 3015905118179849358721829)
                  ·
                    refine ⟨565482209658721754760343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3015905118179849358721829 565482209658721754760343)
                    ·
                      rfl

theorem cell22_1651909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_1651909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651909 prefixEnd_1651909 := by exact prefixLift 1651909
  have htrace : WordTrace (prefixWord ++ tailWord_1651909) baseStart_1651909 baseEnd_1651909 := by
    simpa [prefixWord, tailWord_1651909, baseEnd_1651909] using wordTrace_append hprefix tailTrace_1651909
  have hstable : (prefixWord ++ tailWord_1651909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651909).length < 2 ^ (prefixWord ++ tailWord_1651909).sum := by decide
  have hdescent : baseEnd_1651909 < baseStart_1651909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651943 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1651943 : Nat := 118140960795 + 1651943 * 2 ^ 59
def prefixEnd_1651943 : Nat := 4983230072969 + 3 ^ 40 * 1651943 * 2
def baseEnd_1651943 : Nat := 565493848553556999410239

theorem tailTrace_1651943 : CollatzResearch.WordTrace tailWord_1651943 prefixEnd_1651943 565493848553556999410239 := by
  unfold tailWord_1651943
  simp only [CollatzResearch.WordTrace]
  refine ⟨60251311054300115248040483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40167540702866743498693655 60251311054300115248040483)
  ·
    refine ⟨90376966581450172872060725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60251311054300115248040483 90376966581450172872060725)
    ·
      refine ⟨8472840617010953706755693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90376966581450172872060725 8472840617010953706755693)
      ·
        refine ⟨3177315231379107640033385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8472840617010953706755693 3177315231379107640033385)
        ·
          refine ⟨2382986423534330730025039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3177315231379107640033385 2382986423534330730025039)
          ·
            refine ⟨3574479635301496095037559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382986423534330730025039 3574479635301496095037559)
            ·
              refine ⟨5361719452952244142556339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574479635301496095037559 5361719452952244142556339)
              ·
                refine ⟨8042579179428366213834509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361719452952244142556339 8042579179428366213834509)
                ·
                  refine ⟨3015967192285637330187941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8042579179428366213834509 3015967192285637330187941)
                  ·
                    refine ⟨565493848553556999410239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3015967192285637330187941 565493848553556999410239)
                    ·
                      rfl

theorem cell22_1651943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1651943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651943 prefixEnd_1651943 := by exact prefixLift 1651943
  have htrace : WordTrace (prefixWord ++ tailWord_1651943) baseStart_1651943 baseEnd_1651943 := by
    simpa [prefixWord, tailWord_1651943, baseEnd_1651943] using wordTrace_append hprefix tailTrace_1651943
  have hstable : (prefixWord ++ tailWord_1651943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651943).length < 2 ^ (prefixWord ++ tailWord_1651943).sum := by decide
  have hdescent : baseEnd_1651943 < baseStart_1651943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651958 : List Nat := [5, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1651958 : Nat := 118140960795 + 1651958 * 2 ^ 59
def prefixEnd_1651958 : Nat := 4983230072969 + 3 ^ 40 * 1651958 * 2
def baseEnd_1651958 : Nat := 188499661120033986761731

theorem tailTrace_1651958 : CollatzResearch.WordTrace tailWord_1651958 prefixEnd_1651958 188499661120033986761731 := by
  unfold tailWord_1651958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765741134327860800614783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40167905432830515206557685 3765741134327860800614783)
  ·
    refine ⟨5648611701491791200922175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3765741134327860800614783 5648611701491791200922175)
    ·
      refine ⟨8472917552237686801383263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5648611701491791200922175 8472917552237686801383263)
      ·
        refine ⟨12709376328356530202074895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8472917552237686801383263 12709376328356530202074895)
        ·
          refine ⟨19064064492534795303112343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12709376328356530202074895 19064064492534795303112343)
          ·
            refine ⟨28596096738802192954668515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19064064492534795303112343 28596096738802192954668515)
            ·
              refine ⟨42894145108203289432002773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28596096738802192954668515 42894145108203289432002773)
              ·
                refine ⟨1005331525973514596062565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42894145108203289432002773 1005331525973514596062565)
                ·
                  refine ⟨188499661120033986761731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1005331525973514596062565 188499661120033986761731)
                  ·
                    rfl

theorem cell22_1651958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1651958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651958 prefixEnd_1651958 := by exact prefixLift 1651958
  have htrace : WordTrace (prefixWord ++ tailWord_1651958) baseStart_1651958 baseEnd_1651958 := by
    simpa [prefixWord, tailWord_1651958, baseEnd_1651958] using wordTrace_append hprefix tailTrace_1651958
  have hstable : (prefixWord ++ tailWord_1651958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651958).length < 2 ^ (prefixWord ++ tailWord_1651958).sum := by decide
  have hdescent : baseEnd_1651958 < baseStart_1651958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651969 : List Nat := [1, 2, 4, 1, 1, 13]
def baseStart_1651969 : Nat := 118140960795 + 1651969 * 2 ^ 59
def prefixEnd_1651969 : Nat := 4983230072969 + 3 ^ 40 * 1651969 * 2
def baseEnd_1651969 : Nat := 6981515418332118497039

theorem tailTrace_1651969 : CollatzResearch.WordTrace tailWord_1651969 prefixEnd_1651969 6981515418332118497039 := by
  unfold tailWord_1651969
  simp only [CollatzResearch.WordTrace]
  refine ⟨60252259352205921688486961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40168172901470614458991307 60252259352205921688486961)
  ·
    refine ⟨45189194514154441266365221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60252259352205921688486961 45189194514154441266365221)
    ·
      refine ⟨8472973971403957737443479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45189194514154441266365221 8472973971403957737443479)
      ·
        refine ⟨12709460957105936606165219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8472973971403957737443479 12709460957105936606165219)
        ·
          refine ⟨19064191435658904909247829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12709460957105936606165219 19064191435658904909247829)
          ·
            refine ⟨6981515418332118497039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 19064191435658904909247829 6981515418332118497039)
            ·
              rfl

theorem cell22_1651969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 13].length) (baseStart_1651969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651969 prefixEnd_1651969 := by exact prefixLift 1651969
  have htrace : WordTrace (prefixWord ++ tailWord_1651969) baseStart_1651969 baseEnd_1651969 := by
    simpa [prefixWord, tailWord_1651969, baseEnd_1651969] using wordTrace_append hprefix tailTrace_1651969
  have hstable : (prefixWord ++ tailWord_1651969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651969).length < 2 ^ (prefixWord ++ tailWord_1651969).sum := by decide
  have hdescent : baseEnd_1651969 < baseStart_1651969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651971 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 2, 4]
def baseStart_1651971 : Nat := 118140960795 + 1651971 * 2 ^ 59
def prefixEnd_1651971 : Nat := 4983230072969 + 3 ^ 40 * 1651971 * 2
def baseEnd_1651971 : Nat := 565503433525774259710153

theorem tailTrace_1651971 : CollatzResearch.WordTrace tailWord_1651971 prefixEnd_1651971 565503433525774259710153 := by
  unfold tailWord_1651971
  simp only [CollatzResearch.WordTrace]
  refine ⟨60252332298198676030059767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40168221532132450686706511 60252332298198676030059767)
  ·
    refine ⟨90378498447298014045089651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60252332298198676030059767 90378498447298014045089651)
    ·
      refine ⟨135567747670947021067634477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90378498447298014045089651 135567747670947021067634477)
      ·
        refine ⟨50837905376605132900362929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135567747670947021067634477 50837905376605132900362929)
        ·
          refine ⟨38128429032453849675272197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50837905376605132900362929 38128429032453849675272197)
          ·
            refine ⟨7149080443585096814113537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38128429032453849675272197 7149080443585096814113537)
            ·
              refine ⟨5361810332688822610585153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7149080443585096814113537 5361810332688822610585153)
              ·
                refine ⟨4021357749516616957938865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5361810332688822610585153 4021357749516616957938865)
                ·
                  refine ⟨3016018312137462718454149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4021357749516616957938865 3016018312137462718454149)
                  ·
                    refine ⟨565503433525774259710153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3016018312137462718454149 565503433525774259710153)
                    ·
                      rfl

theorem cell22_1651971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 4].length) (baseStart_1651971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651971 prefixEnd_1651971 := by exact prefixLift 1651971
  have htrace : WordTrace (prefixWord ++ tailWord_1651971) baseStart_1651971 baseEnd_1651971 := by
    simpa [prefixWord, tailWord_1651971, baseEnd_1651971] using wordTrace_append hprefix tailTrace_1651971
  have hstable : (prefixWord ++ tailWord_1651971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651971).length < 2 ^ (prefixWord ++ tailWord_1651971).sum := by decide
  have hdescent : baseEnd_1651971 < baseStart_1651971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651973 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_1651973 : Nat := 118140960795 + 1651973 * 2 ^ 59
def prefixEnd_1651973 : Nat := 4983230072969 + 3 ^ 40 * 1651973 * 2
def baseEnd_1651973 : Nat := 565504118166646921160147

theorem tailTrace_1651973 : CollatzResearch.WordTrace tailWord_1651973 prefixEnd_1651973 565504118166646921160147 := by
  unfold tailWord_1651973
  simp only [CollatzResearch.WordTrace]
  refine ⟨60252405244191430371632573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40168270162794286914421715 60252405244191430371632573)
  ·
    refine ⟨22594651966571786389362215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60252405244191430371632573 22594651966571786389362215)
    ·
      refine ⟨33891977949857679584043323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22594651966571786389362215 33891977949857679584043323)
      ·
        refine ⟨50837966924786519376064985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33891977949857679584043323 50837966924786519376064985)
        ·
          refine ⟨38128475193589889532048739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50837966924786519376064985 38128475193589889532048739)
          ·
            refine ⟨57192712790384834298073109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38128475193589889532048739 57192712790384834298073109)
            ·
              refine ⟨2680908412049289107722177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57192712790384834298073109 2680908412049289107722177)
              ·
                refine ⟨2010681309036966830791633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680908412049289107722177 2010681309036966830791633)
                ·
                  refine ⟨1508010981777725123093725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010681309036966830791633 1508010981777725123093725)
                  ·
                    refine ⟨565504118166646921160147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508010981777725123093725 565504118166646921160147)
                    ·
                      rfl

theorem cell22_1651973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_1651973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1651973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1651973 prefixEnd_1651973 := by exact prefixLift 1651973
  have htrace : WordTrace (prefixWord ++ tailWord_1651973) baseStart_1651973 baseEnd_1651973 := by
    simpa [prefixWord, tailWord_1651973, baseEnd_1651973] using wordTrace_append hprefix tailTrace_1651973
  have hstable : (prefixWord ++ tailWord_1651973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651973).length < 2 ^ (prefixWord ++ tailWord_1651973).sum := by decide
  have hdescent : baseEnd_1651973 < baseStart_1651973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652031 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 7]
def baseStart_1652031 : Nat := 118140960795 + 1652031 * 2 ^ 59
def prefixEnd_1652031 : Nat := 4983230072969 + 3 ^ 40 * 1652031 * 2
def baseEnd_1652031 : Nat := 188507990917318034403323

theorem tailTrace_1652031 : CollatzResearch.WordTrace tailWord_1652031 prefixEnd_1652031 188507990917318034403323 := by
  unfold tailWord_1652031
  simp only [CollatzResearch.WordTrace]
  refine ⟨60254520677981306277243947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40169680451987537518162631 60254520677981306277243947)
  ·
    refine ⟨90381781016971959415865921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60254520677981306277243947 90381781016971959415865921)
    ·
      refine ⟨67786335762728969561899441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90381781016971959415865921 67786335762728969561899441)
      ·
        refine ⟨50839751822046727171424581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67786335762728969561899441 50839751822046727171424581)
        ·
          refine ⟨9532453466633761344642109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50839751822046727171424581 9532453466633761344642109)
          ·
            refine ⟨3574670049987660504240791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9532453466633761344642109 3574670049987660504240791)
            ·
              refine ⟨5362005074981490756361187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574670049987660504240791 5362005074981490756361187)
              ·
                refine ⟨8043007612472236134541781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362005074981490756361187 8043007612472236134541781)
                ·
                  refine ⟨188507990917318034403323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8043007612472236134541781 188507990917318034403323)
                  ·
                    rfl

theorem cell22_1652031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 7].length) (baseStart_1652031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652031 prefixEnd_1652031 := by exact prefixLift 1652031
  have htrace : WordTrace (prefixWord ++ tailWord_1652031) baseStart_1652031 baseEnd_1652031 := by
    simpa [prefixWord, tailWord_1652031, baseEnd_1652031] using wordTrace_append hprefix tailTrace_1652031
  have hstable : (prefixWord ++ tailWord_1652031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652031).length < 2 ^ (prefixWord ++ tailWord_1652031).sum := by decide
  have hdescent : baseEnd_1652031 < baseStart_1652031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652046 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1652046 : Nat := 118140960795 + 1652046 * 2 ^ 59
def prefixEnd_1652046 : Nat := 4983230072969 + 3 ^ 40 * 1652046 * 2
def baseEnd_1652046 : Nat := 565529107558499064084923

theorem tailTrace_1652046 : CollatzResearch.WordTrace tailWord_1652046 prefixEnd_1652046 565529107558499064084923 := by
  unfold tailWord_1652046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7531883471615870479879999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40170045181951309226026661 7531883471615870479879999)
  ·
    refine ⟨11297825207423805719819999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7531883471615870479879999 11297825207423805719819999)
    ·
      refine ⟨16946737811135708579729999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11297825207423805719819999 16946737811135708579729999)
      ·
        refine ⟨25420106716703562869594999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16946737811135708579729999 25420106716703562869594999)
        ·
          refine ⟨38130160075055344304392499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25420106716703562869594999 38130160075055344304392499)
          ·
            refine ⟨57195240112583016456588749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38130160075055344304392499 57195240112583016456588749)
            ·
              refine ⟨21448215042218631171220781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57195240112583016456588749 21448215042218631171220781)
              ·
                refine ⟨8043080640831986689207793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21448215042218631171220781 8043080640831986689207793)
                ·
                  refine ⟨6032310480623990016905845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8043080640831986689207793 6032310480623990016905845)
                  ·
                    refine ⟨565529107558499064084923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6032310480623990016905845 565529107558499064084923)
                    ·
                      rfl

theorem cell22_1652046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1652046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652046 prefixEnd_1652046 := by exact prefixLift 1652046
  have htrace : WordTrace (prefixWord ++ tailWord_1652046) baseStart_1652046 baseEnd_1652046 := by
    simpa [prefixWord, tailWord_1652046, baseEnd_1652046] using wordTrace_append hprefix tailTrace_1652046
  have hstable : (prefixWord ++ tailWord_1652046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652046).length < 2 ^ (prefixWord ++ tailWord_1652046).sum := by decide
  have hdescent : baseEnd_1652046 < baseStart_1652046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652048 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 5]
def baseStart_1652048 : Nat := 118140960795 + 1652048 * 2 ^ 59
def prefixEnd_1652048 : Nat := 4983230072969 + 3 ^ 40 * 1652048 * 2
def baseEnd_1652048 : Nat := 188509930733123908511639

theorem tailTrace_1652048 : CollatzResearch.WordTrace tailWord_1652048 prefixEnd_1652048 188509930733123908511639 := by
  unfold tailWord_1652048
  simp only [CollatzResearch.WordTrace]
  refine ⟨30127570359459859090306399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40170093812613145453741865 30127570359459859090306399)
  ·
    refine ⟨45191355539189788635459599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30127570359459859090306399 45191355539189788635459599)
    ·
      refine ⟨67787033308784682953189399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45191355539189788635459599 67787033308784682953189399)
      ·
        refine ⟨101680549963177024429784099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67787033308784682953189399 101680549963177024429784099)
        ·
          refine ⟨152520824944765536644676149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101680549963177024429784099 152520824944765536644676149)
          ·
            refine ⟨14298827338571769060438389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152520824944765536644676149 14298827338571769060438389)
            ·
              refine ⟨1340515062991103349416099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14298827338571769060438389 1340515062991103349416099)
              ·
                refine ⟨2010772594486655024124149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340515062991103349416099 2010772594486655024124149)
                ·
                  refine ⟨188509930733123908511639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2010772594486655024124149 188509930733123908511639)
                  ·
                    rfl

theorem cell22_1652048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_1652048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652048 prefixEnd_1652048 := by exact prefixLift 1652048
  have htrace : WordTrace (prefixWord ++ tailWord_1652048) baseStart_1652048 baseEnd_1652048 := by
    simpa [prefixWord, tailWord_1652048, baseEnd_1652048] using wordTrace_append hprefix tailTrace_1652048
  have hstable : (prefixWord ++ tailWord_1652048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652048).length < 2 ^ (prefixWord ++ tailWord_1652048).sum := by decide
  have hdescent : baseEnd_1652048 < baseStart_1652048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652121 : List Nat := [1, 2, 1, 2, 1, 5, 2, 8]
def baseStart_1652121 : Nat := 118140960795 + 1652121 * 2 ^ 59
def prefixEnd_1652121 : Nat := 4983230072969 + 3 ^ 40 * 1652121 * 2
def baseEnd_1652121 : Nat := 62839420176802652051077

theorem tailTrace_1652121 : CollatzResearch.WordTrace tailWord_1652121 prefixEnd_1652121 62839420176802652051077 := by
  unfold tailWord_1652121
  simp only [CollatzResearch.WordTrace]
  refine ⟨60257803247655251648020217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40171868831770167765346811 60257803247655251648020217)
  ·
    refine ⟨45193352435741438736015163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60257803247655251648020217 45193352435741438736015163)
    ·
      refine ⟨67790028653612158104022745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45193352435741438736015163 67790028653612158104022745)
      ·
        refine ⟨50842521490209118578017059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67790028653612158104022745 50842521490209118578017059)
        ·
          refine ⟨76263782235313677867025589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50842521490209118578017059 76263782235313677867025589)
          ·
            refine ⟨7149729584560657300033649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76263782235313677867025589 7149729584560657300033649)
            ·
              refine ⟨5362297188420492975025237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7149729584560657300033649 5362297188420492975025237)
              ·
                refine ⟨62839420176802652051077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5362297188420492975025237 62839420176802652051077)
                ·
                  rfl

theorem cell22_1652121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 8].length) (baseStart_1652121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652121 prefixEnd_1652121 := by exact prefixLift 1652121
  have htrace : WordTrace (prefixWord ++ tailWord_1652121) baseStart_1652121 baseEnd_1652121 := by
    simpa [prefixWord, tailWord_1652121, baseEnd_1652121] using wordTrace_append hprefix tailTrace_1652121
  have hstable : (prefixWord ++ tailWord_1652121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652121).length < 2 ^ (prefixWord ++ tailWord_1652121).sum := by decide
  have hdescent : baseEnd_1652121 < baseStart_1652121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652138 : List Nat := [3, 1, 6, 12]
def baseStart_1652138 : Nat := 118140960795 + 1652138 * 2 ^ 59
def prefixEnd_1652138 : Nat := 4983230072969 + 3 ^ 40 * 1652138 * 2
def baseEnd_1652138 : Nat := 775803293605818231529

theorem tailTrace_1652138 : CollatzResearch.WordTrace tailWord_1652138 prefixEnd_1652138 775803293605818231529 := by
  unfold tailWord_1652138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15064605822148415887847267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40172282192395775700926045 15064605822148415887847267)
  ·
    refine ⟨22596908733222623831770901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15064605822148415887847267 22596908733222623831770901)
    ·
      refine ⟨1059230096869810492114261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22596908733222623831770901 1059230096869810492114261)
      ·
        refine ⟨775803293605818231529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1059230096869810492114261 775803293605818231529)
        ·
          rfl

theorem cell22_1652138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 12].length) (baseStart_1652138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652138 prefixEnd_1652138 := by exact prefixLift 1652138
  have htrace : WordTrace (prefixWord ++ tailWord_1652138) baseStart_1652138 baseEnd_1652138 := by
    simpa [prefixWord, tailWord_1652138, baseEnd_1652138] using wordTrace_append hprefix tailTrace_1652138
  have hstable : (prefixWord ++ tailWord_1652138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652138).length < 2 ^ (prefixWord ++ tailWord_1652138).sum := by decide
  have hdescent : baseEnd_1652138 < baseStart_1652138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652151 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1652151 : Nat := 118140960795 + 1652151 * 2 ^ 59
def prefixEnd_1652151 : Nat := 4983230072969 + 3 ^ 40 * 1652151 * 2
def baseEnd_1652151 : Nat := 565565051204313790209601

theorem tailTrace_1652151 : CollatzResearch.WordTrace tailWord_1652151 prefixEnd_1652151 565565051204313790209601 := by
  unfold tailWord_1652151
  simp only [CollatzResearch.WordTrace]
  refine ⟨60258897437546566771612307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40172598291697711181074871 60258897437546566771612307)
  ·
    refine ⟨90388346156319850157418461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60258897437546566771612307 90388346156319850157418461)
    ·
      refine ⟨33895629808619943809031923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90388346156319850157418461 33895629808619943809031923)
      ·
        refine ⟨50843444712929915713547885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33895629808619943809031923 50843444712929915713547885)
        ·
          refine ⟨19066291767348718392580457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50843444712929915713547885 19066291767348718392580457)
          ·
            refine ⟨14299718825511538794435343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19066291767348718392580457 14299718825511538794435343)
            ·
              refine ⟨21449578238267308191653015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14299718825511538794435343 21449578238267308191653015)
              ·
                refine ⟨32174367357400962287479523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21449578238267308191653015 32174367357400962287479523)
                ·
                  refine ⟨48261551036101443431219285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32174367357400962287479523 48261551036101443431219285)
                  ·
                    refine ⟨565565051204313790209601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48261551036101443431219285 565565051204313790209601)
                    ·
                      rfl

theorem cell22_1652151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1652151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652151 prefixEnd_1652151 := by exact prefixLift 1652151
  have htrace : WordTrace (prefixWord ++ tailWord_1652151) baseStart_1652151 baseEnd_1652151 := by
    simpa [prefixWord, tailWord_1652151, baseEnd_1652151] using wordTrace_append hprefix tailTrace_1652151
  have hstable : (prefixWord ++ tailWord_1652151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652151).length < 2 ^ (prefixWord ++ tailWord_1652151).sum := by decide
  have hdescent : baseEnd_1652151 < baseStart_1652151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652170 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_1652170 : Nat := 118140960795 + 1652170 * 2 ^ 59
def prefixEnd_1652170 : Nat := 4983230072969 + 3 ^ 40 * 1652170 * 2
def baseEnd_1652170 : Nat := 565571555292604073984543

theorem tailTrace_1652170 : CollatzResearch.WordTrace tailWord_1652170 prefixEnd_1652170 565571555292604073984543 := by
  unfold tailWord_1652170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15064897606119433254138491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40173060282985155344369309 15064897606119433254138491)
  ·
    refine ⟨22597346409179149881207737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15064897606119433254138491 22597346409179149881207737)
    ·
      refine ⟨16948009806884362410905803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22597346409179149881207737 16948009806884362410905803)
      ·
        refine ⟨25422014710326543616358705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16948009806884362410905803 25422014710326543616358705)
        ·
          refine ⟨19066511032744907712269029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25422014710326543616358705 19066511032744907712269029)
          ·
            refine ⟨3574970818639670196050443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19066511032744907712269029 3574970818639670196050443)
            ·
              refine ⟨5362456227959505294075665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574970818639670196050443 5362456227959505294075665)
              ·
                refine ⟨4021842170969628970556749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5362456227959505294075665 4021842170969628970556749)
                ·
                  refine ⟨1508190814113610863958781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4021842170969628970556749 1508190814113610863958781)
                  ·
                    refine ⟨565571555292604073984543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508190814113610863958781 565571555292604073984543)
                    ·
                      rfl

theorem cell22_1652170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_1652170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652170 prefixEnd_1652170 := by exact prefixLift 1652170
  have htrace : WordTrace (prefixWord ++ tailWord_1652170) baseStart_1652170 baseEnd_1652170 := by
    simpa [prefixWord, tailWord_1652170, baseEnd_1652170] using wordTrace_append hprefix tailTrace_1652170
  have hstable : (prefixWord ++ tailWord_1652170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652170).length < 2 ^ (prefixWord ++ tailWord_1652170).sum := by decide
  have hdescent : baseEnd_1652170 < baseStart_1652170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652277 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_1652277 : Nat := 118140960795 + 1652277 * 2 ^ 59
def prefixEnd_1652277 : Nat := 4983230072969 + 3 ^ 40 * 1652277 * 2
def baseEnd_1652277 : Nat := 565608183579291461559215

theorem tailTrace_1652277 : CollatzResearch.WordTrace tailWord_1652277 prefixEnd_1652277 565608183579291461559215 := by
  unfold tailWord_1652277
  simp only [CollatzResearch.WordTrace]
  refine ⟨60263493035090090290699085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40175662023393393527132723 60263493035090090290699085)
  ·
    refine ⟨22598809888158783859012157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60263493035090090290699085 22598809888158783859012157)
    ·
      refine ⟨8474553708059543947129559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22598809888158783859012157 8474553708059543947129559)
      ·
        refine ⟨12711830562089315920694339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474553708059543947129559 12711830562089315920694339)
        ·
          refine ⟨19067745843133973881041509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12711830562089315920694339 19067745843133973881041509)
          ·
            refine ⟨3575202345587620102695283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19067745843133973881041509 3575202345587620102695283)
            ·
              refine ⟨5362803518381430154042925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575202345587620102695283 5362803518381430154042925)
              ·
                refine ⟨2011051319393036307766097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5362803518381430154042925 2011051319393036307766097)
                ·
                  refine ⟨1508288489544777230824573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2011051319393036307766097 1508288489544777230824573)
                  ·
                    refine ⟨565608183579291461559215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508288489544777230824573 565608183579291461559215)
                    ·
                      rfl

theorem cell22_1652277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_1652277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652277 prefixEnd_1652277 := by exact prefixLift 1652277
  have htrace : WordTrace (prefixWord ++ tailWord_1652277) baseStart_1652277 baseEnd_1652277 := by
    simpa [prefixWord, tailWord_1652277, baseEnd_1652277] using wordTrace_append hprefix tailTrace_1652277
  have hstable : (prefixWord ++ tailWord_1652277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652277).length < 2 ^ (prefixWord ++ tailWord_1652277).sum := by decide
  have hdescent : baseEnd_1652277 < baseStart_1652277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652294 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1652294 : Nat := 118140960795 + 1652294 * 2 ^ 59
def prefixEnd_1652294 : Nat := 4983230072969 + 3 ^ 40 * 1652294 * 2
def baseEnd_1652294 : Nat := 565614003026709083884163

theorem tailTrace_1652294 : CollatzResearch.WordTrace tailWord_1652294 prefixEnd_1652294 565614003026709083884163 := by
  unfold tailWord_1652294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883253533625890693564623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40176075384019001462711957 1883253533625890693564623)
  ·
    refine ⟨2824880300438836040346935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1883253533625890693564623 2824880300438836040346935)
    ·
      refine ⟨4237320450658254060520403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824880300438836040346935 4237320450658254060520403)
      ·
        refine ⟨6355980675987381090780605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4237320450658254060520403 6355980675987381090780605)
        ·
          refine ⟨2383492753495267909042727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6355980675987381090780605 2383492753495267909042727)
          ·
            refine ⟨3575239130242901863564091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383492753495267909042727 3575239130242901863564091)
            ·
              refine ⟨5362858695364352795346137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575239130242901863564091 5362858695364352795346137)
              ·
                refine ⟨4022144021523264596509603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5362858695364352795346137 4022144021523264596509603)
                ·
                  refine ⟨6033216032284896894764405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022144021523264596509603 6033216032284896894764405)
                  ·
                    refine ⟨565614003026709083884163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6033216032284896894764405 565614003026709083884163)
                    ·
                      rfl

theorem cell22_1652294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1652294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652294 prefixEnd_1652294 := by exact prefixLift 1652294
  have htrace : WordTrace (prefixWord ++ tailWord_1652294) baseStart_1652294 baseEnd_1652294 := by
    simpa [prefixWord, tailWord_1652294, baseEnd_1652294] using wordTrace_append hprefix tailTrace_1652294
  have hstable : (prefixWord ++ tailWord_1652294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652294).length < 2 ^ (prefixWord ++ tailWord_1652294).sum := by decide
  have hdescent : baseEnd_1652294 < baseStart_1652294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652356 : List Nat := [2, 3, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1652356 : Nat := 118140960795 + 1652356 * 2 ^ 59
def prefixEnd_1652356 : Nat := 4983230072969 + 3 ^ 40 * 1652356 * 2
def baseEnd_1652356 : Nat := 565635226893761588833973

theorem tailTrace_1652356 : CollatzResearch.WordTrace tailWord_1652356 prefixEnd_1652356 565635226893761588833973 := by
  unfold tailWord_1652356
  simp only [CollatzResearch.WordTrace]
  refine ⟨30133187200901943391412461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40177582934535924521883281 30133187200901943391412461)
  ·
    refine ⟨11299945200338228771779673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30133187200901943391412461 11299945200338228771779673)
    ·
      refine ⟨8474958900253671578834755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11299945200338228771779673 8474958900253671578834755)
      ·
        refine ⟨12712438350380507368252133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474958900253671578834755 12712438350380507368252133)
        ·
          refine ⟨2383582190696345131547275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12712438350380507368252133 2383582190696345131547275)
          ·
            refine ⟨3575373286044517697320913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383582190696345131547275 3575373286044517697320913)
            ·
              refine ⟨2681529964533388272990685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3575373286044517697320913 2681529964533388272990685)
              ·
                refine ⟨1005573736700020602371507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2681529964533388272990685 1005573736700020602371507)
                ·
                  refine ⟨1508360605050030903557261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005573736700020602371507 1508360605050030903557261)
                  ·
                    refine ⟨565635226893761588833973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508360605050030903557261 565635226893761588833973)
                    ·
                      rfl

theorem cell22_1652356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1652356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652356 prefixEnd_1652356 := by exact prefixLift 1652356
  have htrace : WordTrace (prefixWord ++ tailWord_1652356) baseStart_1652356 baseEnd_1652356 := by
    simpa [prefixWord, tailWord_1652356, baseEnd_1652356] using wordTrace_append hprefix tailTrace_1652356
  have hstable : (prefixWord ++ tailWord_1652356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652356).length < 2 ^ (prefixWord ++ tailWord_1652356).sum := by decide
  have hdescent : baseEnd_1652356 < baseStart_1652356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652363 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 8]
def baseStart_1652363 : Nat := 118140960795 + 1652363 * 2 ^ 59
def prefixEnd_1652363 : Nat := 4983230072969 + 3 ^ 40 * 1652363 * 2
def baseEnd_1652363 : Nat := 188545874378938634636317

theorem tailTrace_1652363 : CollatzResearch.WordTrace tailWord_1652363 prefixEnd_1652363 188545874378938634636317 := by
  unfold tailWord_1652363
  simp only [CollatzResearch.WordTrace]
  refine ⟨60266629712778526978329743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40177753141852351318886495 60266629712778526978329743)
  ·
    refine ⟨90399944569167790467494615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60266629712778526978329743 90399944569167790467494615)
    ·
      refine ⟨135599916853751685701241923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90399944569167790467494615 135599916853751685701241923)
      ·
        refine ⟨203399875280627528551862885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135599916853751685701241923 203399875280627528551862885)
        ·
          refine ⟨38137476615117661603474291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203399875280627528551862885 38137476615117661603474291)
          ·
            refine ⟨57206214922676492405211437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38137476615117661603474291 57206214922676492405211437)
            ·
              refine ⟨21452330596003684651954289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57206214922676492405211437 21452330596003684651954289)
              ·
                refine ⟨16089247947002763488965717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21452330596003684651954289 16089247947002763488965717)
                ·
                  refine ⟨188545874378938634636317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16089247947002763488965717 188545874378938634636317)
                  ·
                    rfl

theorem cell22_1652363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 8].length) (baseStart_1652363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652363 prefixEnd_1652363 := by exact prefixLift 1652363
  have htrace : WordTrace (prefixWord ++ tailWord_1652363) baseStart_1652363 baseEnd_1652363 := by
    simpa [prefixWord, tailWord_1652363, baseEnd_1652363] using wordTrace_append hprefix tailTrace_1652363
  have hstable : (prefixWord ++ tailWord_1652363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652363).length < 2 ^ (prefixWord ++ tailWord_1652363).sum := by decide
  have hdescent : baseEnd_1652363 < baseStart_1652363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652386 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1652386 : Nat := 118140960795 + 1652386 * 2 ^ 59
def prefixEnd_1652386 : Nat := 4983230072969 + 3 ^ 40 * 1652386 * 2
def baseEnd_1652386 : Nat := 188548498835617170194627

theorem tailTrace_1652386 : CollatzResearch.WordTrace tailWord_1652386 prefixEnd_1652386 188548498835617170194627 := by
  unfold tailWord_1652386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15066867147923800476604253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40178312394463467937611341 15066867147923800476604253)
  ·
    refine ⟨5650075180471425178726595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15066867147923800476604253 5650075180471425178726595)
    ·
      refine ⟨8475112770707137768089893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650075180471425178726595 8475112770707137768089893)
      ·
        refine ⟨1589083644507588331516855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8475112770707137768089893 1589083644507588331516855)
        ·
          refine ⟨2383625466761382497275283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589083644507588331516855 2383625466761382497275283)
          ·
            refine ⟨3575438200142073745912925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383625466761382497275283 3575438200142073745912925)
            ·
              refine ⟨1340789325053277654717347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3575438200142073745912925 1340789325053277654717347)
              ·
                refine ⟨2011183987579916482076021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340789325053277654717347 2011183987579916482076021)
                ·
                  refine ⟨188548498835617170194627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2011183987579916482076021 188548498835617170194627)
                  ·
                    rfl

theorem cell22_1652386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1652386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652386 prefixEnd_1652386 := by exact prefixLift 1652386
  have htrace : WordTrace (prefixWord ++ tailWord_1652386) baseStart_1652386 baseEnd_1652386 := by
    simpa [prefixWord, tailWord_1652386, baseEnd_1652386] using wordTrace_append hprefix tailTrace_1652386
  have hstable : (prefixWord ++ tailWord_1652386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652386).length < 2 ^ (prefixWord ++ tailWord_1652386).sum := by decide
  have hdescent : baseEnd_1652386 < baseStart_1652386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652410 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1652410 : Nat := 118140960795 + 1652410 * 2 ^ 59
def prefixEnd_1652410 : Nat := 4983230072969 + 3 ^ 40 * 1652410 * 2
def baseEnd_1652410 : Nat := 565653712197323447983807

theorem tailTrace_1652410 : CollatzResearch.WordTrace tailWord_1652410 prefixEnd_1652410 565653712197323447983807 := by
  unfold tailWord_1652410
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067085985902063501322671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40178895962405502670193789 15067085985902063501322671)
  ·
    refine ⟨22600628978853095251984007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15067085985902063501322671 22600628978853095251984007)
    ·
      refine ⟨33900943468279642877976011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22600628978853095251984007 33900943468279642877976011)
      ·
        refine ⟨50851415202419464316964017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33900943468279642877976011 50851415202419464316964017)
        ·
          refine ⟨38138561401814598237723013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50851415202419464316964017 38138561401814598237723013)
          ·
            refine ⟨7150980262840237169573065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38138561401814598237723013 7150980262840237169573065)
            ·
              refine ⟨5363235197130177877179799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7150980262840237169573065 5363235197130177877179799)
              ·
                refine ⟨8044852795695266815769699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363235197130177877179799 8044852795695266815769699)
                ·
                  refine ⟨12067279193542900223654549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8044852795695266815769699 12067279193542900223654549)
                  ·
                    refine ⟨565653712197323447983807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12067279193542900223654549 565653712197323447983807)
                    ·
                      rfl

theorem cell22_1652410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1652410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652410 prefixEnd_1652410 := by exact prefixLift 1652410
  have htrace : WordTrace (prefixWord ++ tailWord_1652410) baseStart_1652410 baseEnd_1652410 := by
    simpa [prefixWord, tailWord_1652410, baseEnd_1652410] using wordTrace_append hprefix tailTrace_1652410
  have hstable : (prefixWord ++ tailWord_1652410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652410).length < 2 ^ (prefixWord ++ tailWord_1652410).sum := by decide
  have hdescent : baseEnd_1652410 < baseStart_1652410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652412 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1652412 : Nat := 118140960795 + 1652412 * 2 ^ 59
def prefixEnd_1652412 : Nat := 4983230072969 + 3 ^ 40 * 1652412 * 2
def baseEnd_1652412 : Nat := 565654396838196109433801

theorem tailTrace_1652412 : CollatzResearch.WordTrace tailWord_1652412 prefixEnd_1652412 565654396838196109433801 := by
  unfold tailWord_1652412
  simp only [CollatzResearch.WordTrace]
  refine ⟨30134208444800504173431745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40178944593067338897908993 30134208444800504173431745)
  ·
    refine ⟨22600656333600378130073809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30134208444800504173431745 22600656333600378130073809)
    ·
      refine ⟨16950492250200283597555357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22600656333600378130073809 16950492250200283597555357)
      ·
        refine ⟨6356434593825106349083259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16950492250200283597555357 6356434593825106349083259)
        ·
          refine ⟨9534651890737659523624889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6356434593825106349083259 9534651890737659523624889)
          ·
            refine ⟨7150988918053244642718667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9534651890737659523624889 7150988918053244642718667)
            ·
              refine ⟨10726483377079866964078001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150988918053244642718667 10726483377079866964078001)
              ·
                refine ⟨8044862532809900223058501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10726483377079866964078001 8044862532809900223058501)
                ·
                  refine ⟨1508411724901856291823469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8044862532809900223058501 1508411724901856291823469)
                  ·
                    refine ⟨565654396838196109433801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508411724901856291823469 565654396838196109433801)
                    ·
                      rfl

theorem cell22_1652412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1652412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652412 prefixEnd_1652412 := by exact prefixLift 1652412
  have htrace : WordTrace (prefixWord ++ tailWord_1652412) baseStart_1652412 baseEnd_1652412 := by
    simpa [prefixWord, tailWord_1652412, baseEnd_1652412] using wordTrace_append hprefix tailTrace_1652412
  have hstable : (prefixWord ++ tailWord_1652412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652412).length < 2 ^ (prefixWord ++ tailWord_1652412).sum := by decide
  have hdescent : baseEnd_1652412 < baseStart_1652412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652414 : List Nat := [4, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1652414 : Nat := 118140960795 + 1652414 * 2 ^ 59
def prefixEnd_1652414 : Nat := 4983230072969 + 3 ^ 40 * 1652414 * 2
def baseEnd_1652414 : Nat := 188551693826356256961265

theorem tailTrace_1652414 : CollatzResearch.WordTrace tailWord_1652414 prefixEnd_1652414 188551693826356256961265 := by
  unfold tailWord_1652414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7533561229449220336054537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40178993223729175125624197 7533561229449220336054537)
  ·
    refine ⟨5650170922086915252040903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7533561229449220336054537 5650170922086915252040903)
    ·
      refine ⟨8475256383130372878061355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650170922086915252040903 8475256383130372878061355)
      ·
        refine ⟨12712884574695559317092033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8475256383130372878061355 12712884574695559317092033)
        ·
          refine ⟨9534663431021669487819025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12712884574695559317092033 9534663431021669487819025)
          ·
            refine ⟨7150997573266252115864269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9534663431021669487819025 7150997573266252115864269)
            ·
              refine ⟨2681624089974844543449101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7150997573266252115864269 2681624089974844543449101)
              ·
                refine ⟨1005609033740566703793413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2681624089974844543449101 1005609033740566703793413)
                ·
                  refine ⟨188551693826356256961265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1005609033740566703793413 188551693826356256961265)
                  ·
                    rfl

theorem cell22_1652414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1652414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652414 prefixEnd_1652414 := by exact prefixLift 1652414
  have htrace : WordTrace (prefixWord ++ tailWord_1652414) baseStart_1652414 baseEnd_1652414 := by
    simpa [prefixWord, tailWord_1652414, baseEnd_1652414] using wordTrace_append hprefix tailTrace_1652414
  have hstable : (prefixWord ++ tailWord_1652414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652414).length < 2 ^ (prefixWord ++ tailWord_1652414).sum := by decide
  have hdescent : baseEnd_1652414 < baseStart_1652414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652474 : List Nat := [3, 1, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_1652474 : Nat := 118140960795 + 1652474 * 2 ^ 59
def prefixEnd_1652474 : Nat := 4983230072969 + 3 ^ 40 * 1652474 * 2
def baseEnd_1652474 : Nat := 565675620705248614383611

theorem tailTrace_1652474 : CollatzResearch.WordTrace tailWord_1652474 prefixEnd_1652474 565675620705248614383611 := by
  unfold tailWord_1652474
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067669553844098233905119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40180452143584261957080317 15067669553844098233905119)
  ·
    refine ⟨22601504330766147350857679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15067669553844098233905119 22601504330766147350857679)
    ·
      refine ⟨33902256496149221026286519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22601504330766147350857679 33902256496149221026286519)
      ·
        refine ⟨50853384744223831539429779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33902256496149221026286519 50853384744223831539429779)
        ·
          refine ⟨76280077116335747309144669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50853384744223831539429779 76280077116335747309144669)
          ·
            refine ⟨28605028918625905240929251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76280077116335747309144669 28605028918625905240929251)
            ·
              refine ⟨42907543377938857861393877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28605028918625905240929251 42907543377938857861393877)
              ·
                refine ⟨1005645547920441981126419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42907543377938857861393877 1005645547920441981126419)
                ·
                  refine ⟨1508468321880662971689629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005645547920441981126419 1508468321880662971689629)
                  ·
                    refine ⟨565675620705248614383611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508468321880662971689629 565675620705248614383611)
                    ·
                      rfl

theorem cell22_1652474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_1652474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652474 prefixEnd_1652474 := by exact prefixLift 1652474
  have htrace : WordTrace (prefixWord ++ tailWord_1652474) baseStart_1652474 baseEnd_1652474 := by
    simpa [prefixWord, tailWord_1652474, baseEnd_1652474] using wordTrace_append hprefix tailTrace_1652474
  have hstable : (prefixWord ++ tailWord_1652474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652474).length < 2 ^ (prefixWord ++ tailWord_1652474).sum := by decide
  have hdescent : baseEnd_1652474 < baseStart_1652474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652491 : List Nat := [1, 1, 1, 1, 5, 1, 6, 2, 1, 3]
def baseStart_1652491 : Nat := 118140960795 + 1652491 * 2 ^ 59
def prefixEnd_1652491 : Nat := 4983230072969 + 3 ^ 40 * 1652491 * 2
def baseEnd_1652491 : Nat := 565681440152666236708559

theorem tailTrace_1652491 : CollatzResearch.WordTrace tailWord_1652491 prefixEnd_1652491 565681440152666236708559 := by
  unfold tailWord_1652491
  simp only [CollatzResearch.WordTrace]
  refine ⟨60271298256314804838989327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40180865504209869892659551 60271298256314804838989327)
  ·
    refine ⟨90406947384472207258483991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60271298256314804838989327 90406947384472207258483991)
    ·
      refine ⟨135610421076708310887725987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90406947384472207258483991 135610421076708310887725987)
      ·
        refine ⟨203415631615062466331588981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135610421076708310887725987 203415631615062466331588981)
        ·
          refine ⟨19070215463912106218586467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203415631615062466331588981 19070215463912106218586467)
          ·
            refine ⟨28605323195868159327879701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19070215463912106218586467 28605323195868159327879701)
            ·
              refine ⟨1340874524806319968494361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28605323195868159327879701 1340874524806319968494361)
              ·
                refine ⟨1005655893604739976370771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340874524806319968494361 1005655893604739976370771)
                ·
                  refine ⟨1508483840407109964556157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005655893604739976370771 1508483840407109964556157)
                  ·
                    refine ⟨565681440152666236708559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508483840407109964556157 565681440152666236708559)
                    ·
                      rfl

theorem cell22_1652491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 3].length) (baseStart_1652491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652491 prefixEnd_1652491 := by exact prefixLift 1652491
  have htrace : WordTrace (prefixWord ++ tailWord_1652491) baseStart_1652491 baseEnd_1652491 := by
    simpa [prefixWord, tailWord_1652491, baseEnd_1652491] using wordTrace_append hprefix tailTrace_1652491
  have hstable : (prefixWord ++ tailWord_1652491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652491).length < 2 ^ (prefixWord ++ tailWord_1652491).sum := by decide
  have hdescent : baseEnd_1652491 < baseStart_1652491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652515 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 8]
def baseStart_1652515 : Nat := 118140960795 + 1652515 * 2 ^ 59
def prefixEnd_1652515 : Nat := 4983230072969 + 3 ^ 40 * 1652515 * 2
def baseEnd_1652515 : Nat := 188563218614379391369495

theorem tailTrace_1652515 : CollatzResearch.WordTrace tailWord_1652515 prefixEnd_1652515 188563218614379391369495 := by
  unfold tailWord_1652515
  simp only [CollatzResearch.WordTrace]
  refine ⟨60272173608227856937862999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40181449072151904625241999 60272173608227856937862999)
  ·
    refine ⟨90408260412341785406794499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60272173608227856937862999 90408260412341785406794499)
    ·
      refine ⟨135612390618512678110191749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90408260412341785406794499 135612390618512678110191749)
      ·
        refine ⟨25427323240971127145660953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135612390618512678110191749 25427323240971127145660953)
        ·
          refine ⟨19070492430728345359245715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25427323240971127145660953 19070492430728345359245715)
          ·
            refine ⟨28605738646092518038868573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19070492430728345359245715 28605738646092518038868573)
            ·
              refine ⟨10727151992284694264575715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28605738646092518038868573 10727151992284694264575715)
              ·
                refine ⟨16090727988427041396863573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10727151992284694264575715 16090727988427041396863573)
                ·
                  refine ⟨188563218614379391369495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16090727988427041396863573 188563218614379391369495)
                  ·
                    rfl

theorem cell22_1652515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 8].length) (baseStart_1652515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652515 prefixEnd_1652515 := by exact prefixLift 1652515
  have htrace : WordTrace (prefixWord ++ tailWord_1652515) baseStart_1652515 baseEnd_1652515 := by
    simpa [prefixWord, tailWord_1652515, baseEnd_1652515] using wordTrace_append hprefix tailTrace_1652515
  have hstable : (prefixWord ++ tailWord_1652515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652515).length < 2 ^ (prefixWord ++ tailWord_1652515).sum := by decide
  have hdescent : baseEnd_1652515 < baseStart_1652515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652517 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_1652517 : Nat := 118140960795 + 1652517 * 2 ^ 59
def prefixEnd_1652517 : Nat := 4983230072969 + 3 ^ 40 * 1652517 * 2
def baseEnd_1652517 : Nat := 565690340484010835558479

theorem tailTrace_1652517 : CollatzResearch.WordTrace tailWord_1652517 prefixEnd_1652517 565690340484010835558479 := by
  unfold tailWord_1652517
  simp only [CollatzResearch.WordTrace]
  refine ⟨60272246554220611279435805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40181497702813740852957203 60272246554220611279435805)
  ·
    refine ⟨22602092457832729229788427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60272246554220611279435805 22602092457832729229788427)
    ·
      refine ⟨33903138686749093844682641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22602092457832729229788427 33903138686749093844682641)
      ·
        refine ⟨25427354015061820383511981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33903138686749093844682641 25427354015061820383511981)
        ·
          refine ⟨9535257755648182643816993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25427354015061820383511981 9535257755648182643816993)
          ·
            refine ⟨7151443316736136982862745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9535257755648182643816993 7151443316736136982862745)
            ·
              refine ⟨5363582487552102737147059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7151443316736136982862745 5363582487552102737147059)
              ·
                refine ⟨8045373731328154105720589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363582487552102737147059 8045373731328154105720589)
                ·
                  refine ⟨3017015149248057789645221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8045373731328154105720589 3017015149248057789645221)
                  ·
                    refine ⟨565690340484010835558479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3017015149248057789645221 565690340484010835558479)
                    ·
                      rfl

theorem cell22_1652517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_1652517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652517 prefixEnd_1652517 := by exact prefixLift 1652517
  have htrace : WordTrace (prefixWord ++ tailWord_1652517) baseStart_1652517 baseEnd_1652517 := by
    simpa [prefixWord, tailWord_1652517, baseEnd_1652517] using wordTrace_append hprefix tailTrace_1652517
  have hstable : (prefixWord ++ tailWord_1652517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652517).length < 2 ^ (prefixWord ++ tailWord_1652517).sum := by decide
  have hdescent : baseEnd_1652517 < baseStart_1652517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652560 : List Nat := [2, 1, 1, 1, 1, 4, 1, 11]
def baseStart_1652560 : Nat := 118140960795 + 1652560 * 2 ^ 59
def prefixEnd_1652560 : Nat := 4983230072969 + 3 ^ 40 * 1652560 * 2
def baseEnd_1652560 : Nat := 62856117806974784081483

theorem tailTrace_1652560 : CollatzResearch.WordTrace tailWord_1652560 prefixEnd_1652560 62856117806974784081483 := by
  unfold tailWord_1652560
  simp only [CollatzResearch.WordTrace]
  refine ⟨30136907446532414811625567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40182543262043219748834089 30136907446532414811625567)
  ·
    refine ⟨45205361169798622217438351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30136907446532414811625567 45205361169798622217438351)
    ·
      refine ⟨67808041754697933326157527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45205361169798622217438351 67808041754697933326157527)
      ·
        refine ⟨101712062632046899989236291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67808041754697933326157527 101712062632046899989236291)
        ·
          refine ⟨152568093948070349983854437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101712062632046899989236291 152568093948070349983854437)
          ·
            refine ⟨28606517615263190621972707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152568093948070349983854437 28606517615263190621972707)
            ·
              refine ⟨42909776422894785932959061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28606517615263190621972707 42909776422894785932959061)
              ·
                refine ⟨62856117806974784081483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 42909776422894785932959061 62856117806974784081483)
                ·
                  rfl

theorem cell22_1652560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 11].length) (baseStart_1652560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652560 prefixEnd_1652560 := by exact prefixLift 1652560
  have htrace : WordTrace (prefixWord ++ tailWord_1652560) baseStart_1652560 baseEnd_1652560 := by
    simpa [prefixWord, tailWord_1652560, baseEnd_1652560] using wordTrace_append hprefix tailTrace_1652560
  have hstable : (prefixWord ++ tailWord_1652560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652560).length < 2 ^ (prefixWord ++ tailWord_1652560).sum := by decide
  have hdescent : baseEnd_1652560 < baseStart_1652560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652562 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1652562 : Nat := 118140960795 + 1652562 * 2 ^ 59
def prefixEnd_1652562 : Nat := 4983230072969 + 3 ^ 40 * 1652562 * 2
def baseEnd_1652562 : Nat := 565705744903645718183341

theorem tailTrace_1652562 : CollatzResearch.WordTrace tailWord_1652562 prefixEnd_1652562 565705744903645718183341 := by
  unfold tailWord_1652562
  simp only [CollatzResearch.WordTrace]
  refine ⟨15068471959764395991205985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40182591892705055976549293 15068471959764395991205985)
  ·
    refine ⟨11301353969823296993404489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15068471959764395991205985 11301353969823296993404489)
    ·
      refine ⟨8476015477367472745053367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11301353969823296993404489 8476015477367472745053367)
      ·
        refine ⟨12714023216051209117580051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8476015477367472745053367 12714023216051209117580051)
        ·
          refine ⟨19071034824076813676370077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12714023216051209117580051 19071034824076813676370077)
          ·
            refine ⟨7151638059028805128638779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19071034824076813676370077 7151638059028805128638779)
            ·
              refine ⟨10727457088543207692958169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151638059028805128638779 10727457088543207692958169)
              ·
                refine ⟨8045592816407405769718627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10727457088543207692958169 8045592816407405769718627)
                ·
                  refine ⟨12068389224611108654577941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045592816407405769718627 12068389224611108654577941)
                  ·
                    refine ⟨565705744903645718183341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12068389224611108654577941 565705744903645718183341)
                    ·
                      rfl

theorem cell22_1652562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1652562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652562 prefixEnd_1652562 := by exact prefixLift 1652562
  have htrace : WordTrace (prefixWord ++ tailWord_1652562) baseStart_1652562 baseEnd_1652562 := by
    simpa [prefixWord, tailWord_1652562, baseEnd_1652562] using wordTrace_append hprefix tailTrace_1652562
  have hstable : (prefixWord ++ tailWord_1652562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652562).length < 2 ^ (prefixWord ++ tailWord_1652562).sum := by decide
  have hdescent : baseEnd_1652562 < baseStart_1652562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652564 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1652564 : Nat := 118140960795 + 1652564 * 2 ^ 59
def prefixEnd_1652564 : Nat := 4983230072969 + 3 ^ 40 * 1652564 * 2
def baseEnd_1652564 : Nat := 565706429544518379633335

theorem tailTrace_1652564 : CollatzResearch.WordTrace tailWord_1652564 prefixEnd_1652564 565706429544518379633335 := by
  unfold tailWord_1652564
  simp only [CollatzResearch.WordTrace]
  refine ⟨30136980392525169153198373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40182640523366892204264497 30136980392525169153198373)
  ·
    refine ⟨5650683823598469216224695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30136980392525169153198373 5650683823598469216224695)
    ·
      refine ⟨8476025735397703824337043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650683823598469216224695 8476025735397703824337043)
      ·
        refine ⟨12714038603096555736505565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8476025735397703824337043 12714038603096555736505565)
        ·
          refine ⟨4767764476161208401189587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12714038603096555736505565 4767764476161208401189587)
          ·
            refine ⟨7151646714241812601784381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767764476161208401189587 7151646714241812601784381)
            ·
              refine ⟨2681867517840679725669143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7151646714241812601784381 2681867517840679725669143)
              ·
                refine ⟨4022801276761019588503715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681867517840679725669143 4022801276761019588503715)
                ·
                  refine ⟨6034201915141529382755573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022801276761019588503715 6034201915141529382755573)
                  ·
                    refine ⟨565706429544518379633335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6034201915141529382755573 565706429544518379633335)
                    ·
                      rfl

theorem cell22_1652564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1652564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652564 prefixEnd_1652564 := by exact prefixLift 1652564
  have htrace : WordTrace (prefixWord ++ tailWord_1652564) baseStart_1652564 baseEnd_1652564 := by
    simpa [prefixWord, tailWord_1652564, baseEnd_1652564] using wordTrace_append hprefix tailTrace_1652564
  have hstable : (prefixWord ++ tailWord_1652564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652564).length < 2 ^ (prefixWord ++ tailWord_1652564).sum := by decide
  have hdescent : baseEnd_1652564 < baseStart_1652564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652615 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 2, 3]
def baseStart_1652615 : Nat := 118140960795 + 1652615 * 2 ^ 59
def prefixEnd_1652615 : Nat := 4983230072969 + 3 ^ 40 * 1652615 * 2
def baseEnd_1652615 : Nat := 565723887886771246608179

theorem tailTrace_1652615 : CollatzResearch.WordTrace tailWord_1652615 prefixEnd_1652615 565723887886771246608179 := by
  unfold tailWord_1652615
  simp only [CollatzResearch.WordTrace]
  refine ⟨60275820907865574016503299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40183880605243716011002199 60275820907865574016503299)
  ·
    refine ⟨90413731361798361024754949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60275820907865574016503299 90413731361798361024754949)
    ·
      refine ⟨16952574630337192692141553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90413731361798361024754949 16952574630337192692141553)
      ·
        refine ⟨12714430972752894519106165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16952574630337192692141553 12714430972752894519106165)
        ·
          refine ⟨1191977903695583861166203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12714430972752894519106165 1191977903695583861166203)
          ·
            refine ⟨1787966855543375791749305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191977903695583861166203 1787966855543375791749305)
            ·
              refine ⟨1340975141657531843811979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1787966855543375791749305 1340975141657531843811979)
              ·
                refine ⟨2011462712486297765717969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340975141657531843811979 2011462712486297765717969)
                ·
                  refine ⟨1508597034364723324288477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2011462712486297765717969 1508597034364723324288477)
                  ·
                    refine ⟨565723887886771246608179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508597034364723324288477 565723887886771246608179)
                    ·
                      rfl

theorem cell22_1652615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_1652615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652615 prefixEnd_1652615 := by exact prefixLift 1652615
  have htrace : WordTrace (prefixWord ++ tailWord_1652615) baseStart_1652615 baseEnd_1652615 := by
    simpa [prefixWord, tailWord_1652615, baseEnd_1652615] using wordTrace_append hprefix tailTrace_1652615
  have hstable : (prefixWord ++ tailWord_1652615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652615).length < 2 ^ (prefixWord ++ tailWord_1652615).sum := by decide
  have hdescent : baseEnd_1652615 < baseStart_1652615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652630 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1652630 : Nat := 118140960795 + 1652630 * 2 ^ 59
def prefixEnd_1652630 : Nat := 4983230072969 + 3 ^ 40 * 1652630 * 2
def baseEnd_1652630 : Nat := 565729022693316207483133

theorem tailTrace_1652630 : CollatzResearch.WordTrace tailWord_1652630 prefixEnd_1652630 565729022693316207483133 := by
  unfold tailWord_1652630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767273000175701973643709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40184245335207487718866229 3767273000175701973643709)
  ·
    refine ⟨1412727375065888240116391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3767273000175701973643709 1412727375065888240116391)
    ·
      refine ⟨2119091062598832360174587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412727375065888240116391 2119091062598832360174587)
      ·
        refine ⟨3178636593898248540261881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119091062598832360174587 3178636593898248540261881)
        ·
          refine ⟨2383977445423686405196411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3178636593898248540261881 2383977445423686405196411)
          ·
            refine ⟨3575966168135529607794617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383977445423686405196411 3575966168135529607794617)
            ·
              refine ⟨2681974626101647205845963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3575966168135529607794617 2681974626101647205845963)
              ·
                refine ⟨4022961939152470808768945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681974626101647205845963 4022961939152470808768945)
                ·
                  refine ⟨3017221454364353106576709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4022961939152470808768945 3017221454364353106576709)
                  ·
                    refine ⟨565729022693316207483133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3017221454364353106576709 565729022693316207483133)
                    ·
                      rfl

theorem cell22_1652630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1652630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652630 prefixEnd_1652630 := by exact prefixLift 1652630
  have htrace : WordTrace (prefixWord ++ tailWord_1652630) baseStart_1652630 baseEnd_1652630 := by
    simpa [prefixWord, tailWord_1652630, baseEnd_1652630] using wordTrace_append hprefix tailTrace_1652630
  have hstable : (prefixWord ++ tailWord_1652630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652630).length < 2 ^ (prefixWord ++ tailWord_1652630).sum := by decide
  have hdescent : baseEnd_1652630 < baseStart_1652630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652652 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_1652652 : Nat := 118140960795 + 1652652 * 2 ^ 59
def prefixEnd_1652652 : Nat := 4983230072969 + 3 ^ 40 * 1652652 * 2
def baseEnd_1652652 : Nat := 565736553742915483433065

theorem tailTrace_1652652 : CollatzResearch.WordTrace tailWord_1652652 prefixEnd_1652652 565736553742915483433065 := by
  unfold tailWord_1652652
  simp only [CollatzResearch.WordTrace]
  refine ⟨30138585204365764667800105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40184780272487686223733473 30138585204365764667800105)
  ·
    refine ⟨22603938903274323500850079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30138585204365764667800105 22603938903274323500850079)
    ·
      refine ⟨33905908354911485251275119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22603938903274323500850079 33905908354911485251275119)
      ·
        refine ⟨50858862532367227876912679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33905908354911485251275119 50858862532367227876912679)
        ·
          refine ⟨76288293798550841815369019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50858862532367227876912679 76288293798550841815369019)
          ·
            refine ⟨114432440697826262723053529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76288293798550841815369019 114432440697826262723053529)
            ·
              refine ⟨85824330523369697042290147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114432440697826262723053529 85824330523369697042290147)
              ·
                refine ⟨128736495785054545563435221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85824330523369697042290147 128736495785054545563435221)
                ·
                  refine ⟨3017261619962215911643013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128736495785054545563435221 3017261619962215911643013)
                  ·
                    refine ⟨565736553742915483433065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3017261619962215911643013 565736553742915483433065)
                    ·
                      rfl

theorem cell22_1652652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_1652652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652652 prefixEnd_1652652 := by exact prefixLift 1652652
  have htrace : WordTrace (prefixWord ++ tailWord_1652652) baseStart_1652652 baseEnd_1652652 := by
    simpa [prefixWord, tailWord_1652652, baseEnd_1652652] using wordTrace_append hprefix tailTrace_1652652
  have hstable : (prefixWord ++ tailWord_1652652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652652).length < 2 ^ (prefixWord ++ tailWord_1652652).sum := by decide
  have hdescent : baseEnd_1652652 < baseStart_1652652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652669 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1652669 : Nat := 118140960795 + 1652669 * 2 ^ 59
def prefixEnd_1652669 : Nat := 4983230072969 + 3 ^ 40 * 1652669 * 2
def baseEnd_1652669 : Nat := 565742373190333105758013

theorem tailTrace_1652669 : CollatzResearch.WordTrace tailWord_1652669 prefixEnd_1652669 565742373190333105758013 := by
  unfold tailWord_1652669
  simp only [CollatzResearch.WordTrace]
  refine ⟨60277790449669941238969061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40185193633113294159312707 60277790449669941238969061)
  ·
    refine ⟨11302085709313113982306699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60277790449669941238969061 11302085709313113982306699)
    ·
      refine ⟨16953128563969670973460049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11302085709313113982306699 16953128563969670973460049)
      ·
        refine ⟨12714846422977253230095037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16953128563969670973460049 12714846422977253230095037)
        ·
          refine ⟨4768067408616469961285639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12714846422977253230095037 4768067408616469961285639)
          ·
            refine ⟨7152101112924704941928459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768067408616469961285639 7152101112924704941928459)
            ·
              refine ⟨10728151669387057412892689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152101112924704941928459 10728151669387057412892689)
              ·
                refine ⟨8046113752040293059669517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10728151669387057412892689 8046113752040293059669517)
                ·
                  refine ⟨3017292657015109897376069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8046113752040293059669517 3017292657015109897376069)
                  ·
                    refine ⟨565742373190333105758013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3017292657015109897376069 565742373190333105758013)
                    ·
                      rfl

theorem cell22_1652669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1652669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652669 prefixEnd_1652669 := by exact prefixLift 1652669
  have htrace : WordTrace (prefixWord ++ tailWord_1652669) baseStart_1652669 baseEnd_1652669 := by
    simpa [prefixWord, tailWord_1652669, baseEnd_1652669] using wordTrace_append hprefix tailTrace_1652669
  have hstable : (prefixWord ++ tailWord_1652669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652669).length < 2 ^ (prefixWord ++ tailWord_1652669).sum := by decide
  have hdescent : baseEnd_1652669 < baseStart_1652669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652684 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 6]
def baseStart_1652684 : Nat := 118140960795 + 1652684 * 2 ^ 59
def prefixEnd_1652684 : Nat := 4983230072969 + 3 ^ 40 * 1652684 * 2
def baseEnd_1652684 : Nat := 188582502665626022210989

theorem tailTrace_1652684 : CollatzResearch.WordTrace tailWord_1652684 prefixEnd_1652684 188582502665626022210989 := by
  unfold tailWord_1652684
  simp only [CollatzResearch.WordTrace]
  refine ⟨30139168772307799400382553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40185558363077065867176737 30139168772307799400382553)
  ·
    refine ⟨22604376579230849550286915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30139168772307799400382553 22604376579230849550286915)
    ·
      refine ⟨33906564868846274325430373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22604376579230849550286915 33906564868846274325430373)
      ·
        refine ⟨6357480912908676436018195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33906564868846274325430373 6357480912908676436018195)
        ·
          refine ⟨9536221369363014654027293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357480912908676436018195 9536221369363014654027293)
          ·
            refine ⟨3576083013511130495260235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9536221369363014654027293 3576083013511130495260235)
            ·
              refine ⟨5364124520266695742890353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576083013511130495260235 5364124520266695742890353)
              ·
                refine ⟨4023093390200021807167765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5364124520266695742890353 4023093390200021807167765)
                ·
                  refine ⟨188582502665626022210989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4023093390200021807167765 188582502665626022210989)
                  ·
                    rfl

theorem cell22_1652684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_1652684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652684 prefixEnd_1652684 := by exact prefixLift 1652684
  have htrace : WordTrace (prefixWord ++ tailWord_1652684) baseStart_1652684 baseEnd_1652684 := by
    simpa [prefixWord, tailWord_1652684, baseEnd_1652684] using wordTrace_append hprefix tailTrace_1652684
  have hstable : (prefixWord ++ tailWord_1652684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652684).length < 2 ^ (prefixWord ++ tailWord_1652684).sum := by decide
  have hdescent : baseEnd_1652684 < baseStart_1652684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652703 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 1, 4]
def baseStart_1652703 : Nat := 118140960795 + 1652703 * 2 ^ 59
def prefixEnd_1652703 : Nat := 4983230072969 + 3 ^ 40 * 1652703 * 2
def baseEnd_1652703 : Nat := 565754012085168350407909

theorem tailTrace_1652703 : CollatzResearch.WordTrace tailWord_1652703 prefixEnd_1652703 565754012085168350407909 := by
  unfold tailWord_1652703
  simp only [CollatzResearch.WordTrace]
  refine ⟨60279030531546765045706763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40186020354364510030471175 60279030531546765045706763)
  ·
    refine ⟨90418545797320147568560145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60279030531546765045706763 90418545797320147568560145)
    ·
      refine ⟨67813909347990110676420109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90418545797320147568560145 67813909347990110676420109)
      ·
        refine ⟨25430216005496291503657541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67813909347990110676420109 25430216005496291503657541)
        ·
          refine ⟨4768165501030554656935789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25430216005496291503657541 4768165501030554656935789)
          ·
            refine ⟨1788062062886457996350921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4768165501030554656935789 1788062062886457996350921)
            ·
              refine ⟨1341046547164843497263191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788062062886457996350921 1341046547164843497263191)
              ·
                refine ⟨2011569820747265245894787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341046547164843497263191 2011569820747265245894787)
                ·
                  refine ⟨3017354731120897868842181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011569820747265245894787 3017354731120897868842181)
                  ·
                    refine ⟨565754012085168350407909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3017354731120897868842181 565754012085168350407909)
                    ·
                      rfl

theorem cell22_1652703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 1, 4].length) (baseStart_1652703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652703 prefixEnd_1652703 := by exact prefixLift 1652703
  have htrace : WordTrace (prefixWord ++ tailWord_1652703) baseStart_1652703 baseEnd_1652703 := by
    simpa [prefixWord, tailWord_1652703, baseEnd_1652703] using wordTrace_append hprefix tailTrace_1652703
  have hstable : (prefixWord ++ tailWord_1652703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652703).length < 2 ^ (prefixWord ++ tailWord_1652703).sum := by decide
  have hdescent : baseEnd_1652703 < baseStart_1652703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652714 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1652714 : Nat := 118140960795 + 1652714 * 2 ^ 59
def prefixEnd_1652714 : Nat := 4983230072969 + 3 ^ 40 * 1652714 * 2
def baseEnd_1652714 : Nat := 565757777609967988382875

theorem tailTrace_1652714 : CollatzResearch.WordTrace tailWord_1652714 prefixEnd_1652714 565757777609967988382875 := by
  unfold tailWord_1652714
  simp only [CollatzResearch.WordTrace]
  refine ⟨15069857933626728481089299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40186287823004609282904797 15069857933626728481089299)
  ·
    refine ⟨22604786900440092721633949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15069857933626728481089299 22604786900440092721633949)
    ·
      refine ⟨8476795087665034770612731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22604786900440092721633949 8476795087665034770612731)
      ·
        refine ⟨12715192631497552155919097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8476795087665034770612731 12715192631497552155919097)
        ·
          refine ⟨9536394473623164116939323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12715192631497552155919097 9536394473623164116939323)
          ·
            refine ⟨14304591710434746175408985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9536394473623164116939323 14304591710434746175408985)
            ·
              refine ⟨10728443782826059631556739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14304591710434746175408985 10728443782826059631556739)
              ·
                refine ⟨16092665674239089447335109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10728443782826059631556739 16092665674239089447335109)
                ·
                  refine ⟨3017374813919829271375333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16092665674239089447335109 3017374813919829271375333)
                  ·
                    refine ⟨565757777609967988382875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3017374813919829271375333 565757777609967988382875)
                    ·
                      rfl

theorem cell22_1652714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1652714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652714 prefixEnd_1652714 := by exact prefixLift 1652714
  have htrace : WordTrace (prefixWord ++ tailWord_1652714) baseStart_1652714 baseEnd_1652714 := by
    simpa [prefixWord, tailWord_1652714, baseEnd_1652714] using wordTrace_append hprefix tailTrace_1652714
  have hstable : (prefixWord ++ tailWord_1652714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652714).length < 2 ^ (prefixWord ++ tailWord_1652714).sum := by decide
  have hdescent : baseEnd_1652714 < baseStart_1652714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652778 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1652778 : Nat := 118140960795 + 1652778 * 2 ^ 59
def prefixEnd_1652778 : Nat := 4983230072969 + 3 ^ 40 * 1652778 * 2
def baseEnd_1652778 : Nat := 565779686117893154782679

theorem tailTrace_1652778 : CollatzResearch.WordTrace tailWord_1652778 prefixEnd_1652778 565779686117893154782679 := by
  unfold tailWord_1652778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15070441501568763213671747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40187844004183368569791325 15070441501568763213671747)
  ·
    refine ⟨22605662252353144820507621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15070441501568763213671747 22605662252353144820507621)
    ·
      refine ⟨4238561672316214653845179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22605662252353144820507621 4238561672316214653845179)
      ·
        refine ⟨6357842508474321980767769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238561672316214653845179 6357842508474321980767769)
        ·
          refine ⟨4768381881355741485575827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6357842508474321980767769 4768381881355741485575827)
          ·
            refine ⟨7152572822033612228363741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768381881355741485575827 7152572822033612228363741)
            ·
              refine ⟨2682214808262604585636403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7152572822033612228363741 2682214808262604585636403)
              ·
                refine ⟨4023322212393906878454605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682214808262604585636403 4023322212393906878454605)
                ·
                  refine ⟨1508745829647715079420477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4023322212393906878454605 1508745829647715079420477)
                  ·
                    refine ⟨565779686117893154782679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508745829647715079420477 565779686117893154782679)
                    ·
                      rfl

theorem cell22_1652778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1652778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652778 prefixEnd_1652778 := by exact prefixLift 1652778
  have htrace : WordTrace (prefixWord ++ tailWord_1652778) baseStart_1652778 baseEnd_1652778 := by
    simpa [prefixWord, tailWord_1652778, baseEnd_1652778] using wordTrace_append hprefix tailTrace_1652778
  have hstable : (prefixWord ++ tailWord_1652778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652778).length < 2 ^ (prefixWord ++ tailWord_1652778).sum := by decide
  have hdescent : baseEnd_1652778 < baseStart_1652778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652789 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1652789 : Nat := 118140960795 + 1652789 * 2 ^ 59
def prefixEnd_1652789 : Nat := 4983230072969 + 3 ^ 40 * 1652789 * 2
def baseEnd_1652789 : Nat := 565783451642692792757645

theorem tailTrace_1652789 : CollatzResearch.WordTrace tailWord_1652789 prefixEnd_1652789 565783451642692792757645 := by
  unfold tailWord_1652789
  simp only [CollatzResearch.WordTrace]
  refine ⟨60282167209235201733337421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40188111472823467822224947 60282167209235201733337421)
  ·
    refine ⟨22605812703463200650001533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60282167209235201733337421 22605812703463200650001533)
    ·
      refine ⟨8477179763798700243750575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22605812703463200650001533 8477179763798700243750575)
      ·
        refine ⟨12715769645698050365625863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8477179763798700243750575 12715769645698050365625863)
        ·
          refine ⟨19073654468547075548438795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12715769645698050365625863 19073654468547075548438795)
          ·
            refine ⟨28610481702820613322658193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19073654468547075548438795 28610481702820613322658193)
            ·
              refine ⟨21457861277115459991993645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28610481702820613322658193 21457861277115459991993645)
              ·
                refine ⟨8046697978918297496997617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21457861277115459991993645 8046697978918297496997617)
                ·
                  refine ⟨6035023484188723122748213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8046697978918297496997617 6035023484188723122748213)
                  ·
                    refine ⟨565783451642692792757645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6035023484188723122748213 565783451642692792757645)
                    ·
                      rfl

theorem cell22_1652789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1652789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652789 prefixEnd_1652789 := by exact prefixLift 1652789
  have htrace : WordTrace (prefixWord ++ tailWord_1652789) baseStart_1652789 baseEnd_1652789 := by
    simpa [prefixWord, tailWord_1652789, baseEnd_1652789] using wordTrace_append hprefix tailTrace_1652789
  have hstable : (prefixWord ++ tailWord_1652789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652789).length < 2 ^ (prefixWord ++ tailWord_1652789).sum := by decide
  have hdescent : baseEnd_1652789 < baseStart_1652789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652791 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 5]
def baseStart_1652791 : Nat := 118140960795 + 1652791 * 2 ^ 59
def prefixEnd_1652791 : Nat := 4983230072969 + 3 ^ 40 * 1652791 * 2
def baseEnd_1652791 : Nat := 188594712094521818069213

theorem tailTrace_1652791 : CollatzResearch.WordTrace tailWord_1652791 prefixEnd_1652791 188594712094521818069213 := by
  unfold tailWord_1652791
  simp only [CollatzResearch.WordTrace]
  refine ⟨60282240155227956074910227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40188160103485304049940151 60282240155227956074910227)
  ·
    refine ⟨90423360232841934112365341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60282240155227956074910227 90423360232841934112365341)
    ·
      refine ⟨33908760087315725292137003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90423360232841934112365341 33908760087315725292137003)
      ·
        refine ⟨50863140130973587938205505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33908760087315725292137003 50863140130973587938205505)
        ·
          refine ⟨38147355098230190953654129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50863140130973587938205505 38147355098230190953654129)
          ·
            refine ⟨28610516323672643215240597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38147355098230190953654129 28610516323672643215240597)
            ·
              refine ⟨1341117952672155150714403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28610516323672643215240597 1341117952672155150714403)
              ·
                refine ⟨2011676929008232726071605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341117952672155150714403 2011676929008232726071605)
                ·
                  refine ⟨188594712094521818069213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2011676929008232726071605 188594712094521818069213)
                  ·
                    rfl

theorem cell22_1652791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 5].length) (baseStart_1652791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652791 prefixEnd_1652791 := by exact prefixLift 1652791
  have htrace : WordTrace (prefixWord ++ tailWord_1652791) baseStart_1652791 baseEnd_1652791 := by
    simpa [prefixWord, tailWord_1652791, baseEnd_1652791] using wordTrace_append hprefix tailTrace_1652791
  have hstable : (prefixWord ++ tailWord_1652791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652791).length < 2 ^ (prefixWord ++ tailWord_1652791).sum := by decide
  have hdescent : baseEnd_1652791 < baseStart_1652791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652829 : List Nat := [1, 4, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1652829 : Nat := 118140960795 + 1652829 * 2 ^ 59
def prefixEnd_1652829 : Nat := 4983230072969 + 3 ^ 40 * 1652829 * 2
def baseEnd_1652829 : Nat := 565797144460146021757523

theorem tailTrace_1652829 : CollatzResearch.WordTrace tailWord_1652829 prefixEnd_1652829 565797144460146021757523 := by
  unfold tailWord_1652829
  simp only [CollatzResearch.WordTrace]
  refine ⟨60283626129090288564793541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40189084086060192376529027 60283626129090288564793541)
  ·
    refine ⟨11303179899204429105898789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60283626129090288564793541 11303179899204429105898789)
    ·
      refine ⟨2119346231100830457356023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11303179899204429105898789 2119346231100830457356023)
      ·
        refine ⟨3179019346651245686034035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119346231100830457356023 3179019346651245686034035)
        ·
          refine ⟨4768529019976868529051053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179019346651245686034035 4768529019976868529051053)
          ·
            refine ⟨1788198382491325698394145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4768529019976868529051053 1788198382491325698394145)
            ·
              refine ⟨1341148786868494273795609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788198382491325698394145 1341148786868494273795609)
              ·
                refine ⟨1005861590151370705346707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341148786868494273795609 1005861590151370705346707)
                ·
                  refine ⟨1508792385227056058020061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005861590151370705346707 1508792385227056058020061)
                  ·
                    refine ⟨565797144460146021757523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508792385227056058020061 565797144460146021757523)
                    ·
                      rfl

theorem cell22_1652829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1652829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652829 prefixEnd_1652829 := by exact prefixLift 1652829
  have htrace : WordTrace (prefixWord ++ tailWord_1652829) baseStart_1652829 baseEnd_1652829 := by
    simpa [prefixWord, tailWord_1652829, baseEnd_1652829] using wordTrace_append hprefix tailTrace_1652829
  have hstable : (prefixWord ++ tailWord_1652829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652829).length < 2 ^ (prefixWord ++ tailWord_1652829).sum := by decide
  have hdescent : baseEnd_1652829 < baseStart_1652829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652849 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_1652849 : Nat := 118140960795 + 1652849 * 2 ^ 59
def prefixEnd_1652849 : Nat := 4983230072969 + 3 ^ 40 * 1652849 * 2
def baseEnd_1652849 : Nat := 565803990868872636257461

theorem tailTrace_1652849 : CollatzResearch.WordTrace tailWord_1652849 prefixEnd_1652849 565803990868872636257461 := by
  unfold tailWord_1652849
  simp only [CollatzResearch.WordTrace]
  refine ⟨60284355589017831980521601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40189570392678554653681067 60284355589017831980521601)
  ·
    refine ⟨45213266691763373985391201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60284355589017831980521601 45213266691763373985391201)
    ·
      refine ⟨33909950018822530489043401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45213266691763373985391201 33909950018822530489043401)
      ·
        refine ⟨25432462514116897866782551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33909950018822530489043401 25432462514116897866782551)
        ·
          refine ⟨38148693771175346800173827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25432462514116897866782551 38148693771175346800173827)
          ·
            refine ⟨57223040656763020200260741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38148693771175346800173827 57223040656763020200260741)
            ·
              refine ⟨10729320123143066287548889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57223040656763020200260741 10729320123143066287548889)
              ·
                refine ⟨8046990092357299715661667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10729320123143066287548889 8046990092357299715661667)
                ·
                  refine ⟨12070485138535949573492501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046990092357299715661667 12070485138535949573492501)
                  ·
                    refine ⟨565803990868872636257461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12070485138535949573492501 565803990868872636257461)
                    ·
                      rfl

theorem cell22_1652849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_1652849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652849 prefixEnd_1652849 := by exact prefixLift 1652849
  have htrace : WordTrace (prefixWord ++ tailWord_1652849) baseStart_1652849 baseEnd_1652849 := by
    simpa [prefixWord, tailWord_1652849, baseEnd_1652849] using wordTrace_append hprefix tailTrace_1652849
  have hstable : (prefixWord ++ tailWord_1652849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652849).length < 2 ^ (prefixWord ++ tailWord_1652849).sum := by decide
  have hdescent : baseEnd_1652849 < baseStart_1652849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652986 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1652986 : Nat := 118140960795 + 1652986 * 2 ^ 59
def prefixEnd_1652986 : Nat := 4983230072969 + 3 ^ 40 * 1652986 * 2
def baseEnd_1652986 : Nat := 565850888768649945582041

theorem tailTrace_1652986 : CollatzResearch.WordTrace tailWord_1652986 prefixEnd_1652986 565850888768649945582041 := by
  unfold tailWord_1652986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15072338097380376094564703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40192901593014336252172541 15072338097380376094564703)
  ·
    refine ⟨22608507146070564141847055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15072338097380376094564703 22608507146070564141847055)
    ·
      refine ⟨33912760719105846212770583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22608507146070564141847055 33912760719105846212770583)
      ·
        refine ⟨50869141078658769319155875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33912760719105846212770583 50869141078658769319155875)
        ·
          refine ⟨76303711617988153978733813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50869141078658769319155875 76303711617988153978733813)
          ·
            refine ⟨7153472964186389435506295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76303711617988153978733813 7153472964186389435506295)
            ·
              refine ⟨10730209446279584153259443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7153472964186389435506295 10730209446279584153259443)
              ·
                refine ⟨16095314169419376229889165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10730209446279584153259443 16095314169419376229889165)
                ·
                  refine ⟨6035742813532266086208437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16095314169419376229889165 6035742813532266086208437)
                  ·
                    refine ⟨565850888768649945582041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6035742813532266086208437 565850888768649945582041)
                    ·
                      rfl

theorem cell22_1652986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1652986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1652986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1652986 prefixEnd_1652986 := by exact prefixLift 1652986
  have htrace : WordTrace (prefixWord ++ tailWord_1652986) baseStart_1652986 baseEnd_1652986 := by
    simpa [prefixWord, tailWord_1652986, baseEnd_1652986] using wordTrace_append hprefix tailTrace_1652986
  have hstable : (prefixWord ++ tailWord_1652986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652986).length < 2 ^ (prefixWord ++ tailWord_1652986).sum := by decide
  have hdescent : baseEnd_1652986 < baseStart_1652986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653084 : List Nat := [2, 2, 4, 3, 2, 1, 2, 6]
def baseStart_1653084 : Nat := 118140960795 + 1653084 * 2 ^ 59
def prefixEnd_1653084 : Nat := 4983230072969 + 3 ^ 40 * 1653084 * 2
def baseEnd_1653084 : Nat := 62876048463490039625749

theorem tailTrace_1653084 : CollatzResearch.WordTrace tailWord_1653084 prefixEnd_1653084 62876048463490039625749 := by
  unfold tailWord_1653084
  simp only [CollatzResearch.WordTrace]
  refine ⟨30146463371583233557663153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40195284495444311410217537 30146463371583233557663153)
  ·
    refine ⟨22609847528687425168247365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30146463371583233557663153 22609847528687425168247365)
    ·
      refine ⟨4239346411628892219046381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22609847528687425168247365 4239346411628892219046381)
      ·
        refine ⟨1589754904360834582142393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4239346411628892219046381 1589754904360834582142393)
        ·
          refine ⟨1192316178270625936606795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589754904360834582142393 1192316178270625936606795)
          ·
            refine ⟨1788474267405938904910193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192316178270625936606795 1788474267405938904910193)
            ·
              refine ⟨1341355700554454178682645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788474267405938904910193 1341355700554454178682645)
              ·
                refine ⟨62876048463490039625749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1341355700554454178682645 62876048463490039625749)
                ·
                  rfl

theorem cell22_1653084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 6].length) (baseStart_1653084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653084 prefixEnd_1653084 := by exact prefixLift 1653084
  have htrace : WordTrace (prefixWord ++ tailWord_1653084) baseStart_1653084 baseEnd_1653084 := by
    simpa [prefixWord, tailWord_1653084, baseEnd_1653084] using wordTrace_append hprefix tailTrace_1653084
  have hstable : (prefixWord ++ tailWord_1653084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653084).length < 2 ^ (prefixWord ++ tailWord_1653084).sum := by decide
  have hdescent : baseEnd_1653084 < baseStart_1653084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653198 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1653198 : Nat := 118140960795 + 1653198 * 2 ^ 59
def prefixEnd_1653198 : Nat := 4983230072969 + 3 ^ 40 * 1653198 * 2
def baseEnd_1653198 : Nat := 565923460701152059281391

theorem tailTrace_1653198 : CollatzResearch.WordTrace tailWord_1653198 prefixEnd_1653198 565923460701152059281391 := by
  unfold tailWord_1653198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537135583094183073122031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40198056443168976389984165 7537135583094183073122031)
  ·
    refine ⟨11305703374641274609683047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7537135583094183073122031 11305703374641274609683047)
    ·
      refine ⟨16958555061961911914524571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11305703374641274609683047 16958555061961911914524571)
      ·
        refine ⟨25437832592942867871786857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16958555061961911914524571 25437832592942867871786857)
        ·
          refine ⟨19078374444707150903840143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25437832592942867871786857 19078374444707150903840143)
          ·
            refine ⟨28617561667060726355760215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19078374444707150903840143 28617561667060726355760215)
            ·
              refine ⟨42926342500591089533640323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28617561667060726355760215 42926342500591089533640323)
              ·
                refine ⟨64389513750886634300460485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42926342500591089533640323 64389513750886634300460485)
                ·
                  refine ⟨12073033828291243931336341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64389513750886634300460485 12073033828291243931336341)
                  ·
                    refine ⟨565923460701152059281391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12073033828291243931336341 565923460701152059281391)
                    ·
                      rfl

theorem cell22_1653198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1653198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653198 prefixEnd_1653198 := by exact prefixLift 1653198
  have htrace : WordTrace (prefixWord ++ tailWord_1653198) baseStart_1653198 baseEnd_1653198 := by
    simpa [prefixWord, tailWord_1653198, baseEnd_1653198] using wordTrace_append hprefix tailTrace_1653198
  have hstable : (prefixWord ++ tailWord_1653198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653198).length < 2 ^ (prefixWord ++ tailWord_1653198).sum := by decide
  have hdescent : baseEnd_1653198 < baseStart_1653198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653228 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_1653228 : Nat := 118140960795 + 1653228 * 2 ^ 59
def prefixEnd_1653228 : Nat := 4983230072969 + 3 ^ 40 * 1653228 * 2
def baseEnd_1653228 : Nat := 565933730314241981031299

theorem tailTrace_1653228 : CollatzResearch.WordTrace tailWord_1653228 prefixEnd_1653228 565933730314241981031299 := by
  unfold tailWord_1653228
  simp only [CollatzResearch.WordTrace]
  refine ⟨30149089427322389854284169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40198785903096519805712225 30149089427322389854284169)
  ·
    refine ⟨22611817070491792390713127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30149089427322389854284169 22611817070491792390713127)
    ·
      refine ⟨33917725605737688586069691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22611817070491792390713127 33917725605737688586069691)
      ·
        refine ⟨50876588408606532879104537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33917725605737688586069691 50876588408606532879104537)
        ·
          refine ⟨38157441306454899659328403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50876588408606532879104537 38157441306454899659328403)
          ·
            refine ⟨57236161959682349488992605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38157441306454899659328403 57236161959682349488992605)
            ·
              refine ⟨21463560734880881058372227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57236161959682349488992605 21463560734880881058372227)
              ·
                refine ⟨32195341102321321587558341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21463560734880881058372227 32195341102321321587558341)
                ·
                  refine ⟨6036626456685247797667189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32195341102321321587558341 6036626456685247797667189)
                  ·
                    refine ⟨565933730314241981031299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6036626456685247797667189 565933730314241981031299)
                    ·
                      rfl

theorem cell22_1653228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_1653228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653228 prefixEnd_1653228 := by exact prefixLift 1653228
  have htrace : WordTrace (prefixWord ++ tailWord_1653228) baseStart_1653228 baseEnd_1653228 := by
    simpa [prefixWord, tailWord_1653228, baseEnd_1653228] using wordTrace_append hprefix tailTrace_1653228
  have hstable : (prefixWord ++ tailWord_1653228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653228).length < 2 ^ (prefixWord ++ tailWord_1653228).sum := by decide
  have hdescent : baseEnd_1653228 < baseStart_1653228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653230 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_1653230 : Nat := 118140960795 + 1653230 * 2 ^ 59
def prefixEnd_1653230 : Nat := 4983230072969 + 3 ^ 40 * 1653230 * 2
def baseEnd_1653230 : Nat := 188644804985038214160431

theorem tailTrace_1653230 : CollatzResearch.WordTrace tailWord_1653230 prefixEnd_1653230 188644804985038214160431 := by
  unfold tailWord_1653230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537281475079691756267643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40198834533758356033427429 7537281475079691756267643)
  ·
    refine ⟨11305922212619537634401465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7537281475079691756267643 11305922212619537634401465)
    ·
      refine ⟨8479441659464653225801099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11305922212619537634401465 8479441659464653225801099)
      ·
        refine ⟨12719162489196979838701649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479441659464653225801099 12719162489196979838701649)
        ·
          refine ⟨9539371866897734879026237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12719162489196979838701649 9539371866897734879026237)
          ·
            refine ⟨3577264450086650579634839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9539371866897734879026237 3577264450086650579634839)
            ·
              refine ⟨5365896675129975869452259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577264450086650579634839 5365896675129975869452259)
              ·
                refine ⟨8048845012694963804178389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365896675129975869452259 8048845012694963804178389)
                ·
                  refine ⟨188644804985038214160431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8048845012694963804178389 188644804985038214160431)
                  ·
                    rfl

theorem cell22_1653230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_1653230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653230 prefixEnd_1653230 := by exact prefixLift 1653230
  have htrace : WordTrace (prefixWord ++ tailWord_1653230) baseStart_1653230 baseEnd_1653230 := by
    simpa [prefixWord, tailWord_1653230, baseEnd_1653230] using wordTrace_append hprefix tailTrace_1653230
  have hstable : (prefixWord ++ tailWord_1653230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653230).length < 2 ^ (prefixWord ++ tailWord_1653230).sum := by decide
  have hdescent : baseEnd_1653230 < baseStart_1653230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653234 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_1653234 : Nat := 118140960795 + 1653234 * 2 ^ 59
def prefixEnd_1653234 : Nat := 4983230072969 + 3 ^ 40 * 1653234 * 2
def baseEnd_1653234 : Nat := 565935784236859965381281

theorem tailTrace_1653234 : CollatzResearch.WordTrace tailWord_1653234 prefixEnd_1653234 565935784236859965381281 := by
  unfold tailWord_1653234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074599423155760683321689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40198931795082028488857837 15074599423155760683321689)
  ·
    refine ⟨11305949567366820512491267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15074599423155760683321689 11305949567366820512491267)
    ·
      refine ⟨16958924351050230768736901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11305949567366820512491267 16958924351050230768736901)
      ·
        refine ⟨3179798315821918269138169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16958924351050230768736901 3179798315821918269138169)
        ·
          refine ⟨2384848736866438701853627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3179798315821918269138169 2384848736866438701853627)
          ·
            refine ⟨3577273105299658052780441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384848736866438701853627 3577273105299658052780441)
            ·
              refine ⟨2682954828974743539585331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577273105299658052780441 2682954828974743539585331)
              ·
                refine ⟨4024432243462115309377997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682954828974743539585331 4024432243462115309377997)
                ·
                  refine ⟨1509162091298293241016749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4024432243462115309377997 1509162091298293241016749)
                  ·
                    refine ⟨565935784236859965381281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1509162091298293241016749 565935784236859965381281)
                    ·
                      rfl

theorem cell22_1653234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_1653234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653234 prefixEnd_1653234 := by exact prefixLift 1653234
  have htrace : WordTrace (prefixWord ++ tailWord_1653234) baseStart_1653234 baseEnd_1653234 := by
    simpa [prefixWord, tailWord_1653234, baseEnd_1653234] using wordTrace_append hprefix tailTrace_1653234
  have hstable : (prefixWord ++ tailWord_1653234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653234).length < 2 ^ (prefixWord ++ tailWord_1653234).sum := by decide
  have hdescent : baseEnd_1653234 < baseStart_1653234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653268 : List Nat := [2, 4, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1653268 : Nat := 118140960795 + 1653268 * 2 ^ 59
def prefixEnd_1653268 : Nat := 4983230072969 + 3 ^ 40 * 1653268 * 2
def baseEnd_1653268 : Nat := 565947423131695210031177

theorem tailTrace_1653268 : CollatzResearch.WordTrace tailWord_1653268 prefixEnd_1653268 565947423131695210031177 := by
  unfold tailWord_1653268
  simp only [CollatzResearch.WordTrace]
  refine ⟨30149818887249933270012229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40199758516333244360016305 30149818887249933270012229)
  ·
    refine ⟨5653091041359362488127293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30149818887249933270012229 5653091041359362488127293)
    ·
      refine ⟨2119909140509760933047735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5653091041359362488127293 2119909140509760933047735)
      ·
        refine ⟨3179863710764641399571603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119909140509760933047735 3179863710764641399571603)
        ·
          refine ⟨4769795566146962099357405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179863710764641399571603 4769795566146962099357405)
          ·
            refine ⟨1788673337305110787259027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4769795566146962099357405 1788673337305110787259027)
            ·
              refine ⟨2683010005957666180888541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788673337305110787259027 2683010005957666180888541)
              ·
                refine ⟨1006128752234124817833203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2683010005957666180888541 1006128752234124817833203)
                ·
                  refine ⟨1509193128351187226749805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006128752234124817833203 1509193128351187226749805)
                  ·
                    refine ⟨565947423131695210031177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1509193128351187226749805 565947423131695210031177)
                    ·
                      rfl

theorem cell22_1653268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1653268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653268 prefixEnd_1653268 := by exact prefixLift 1653268
  have htrace : WordTrace (prefixWord ++ tailWord_1653268) baseStart_1653268 baseEnd_1653268 := by
    simpa [prefixWord, tailWord_1653268, baseEnd_1653268] using wordTrace_append hprefix tailTrace_1653268
  have hstable : (prefixWord ++ tailWord_1653268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653268).length < 2 ^ (prefixWord ++ tailWord_1653268).sum := by decide
  have hdescent : baseEnd_1653268 < baseStart_1653268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653277 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1653277 : Nat := 118140960795 + 1653277 * 2 ^ 59
def prefixEnd_1653277 : Nat := 4983230072969 + 3 ^ 40 * 1653277 * 2
def baseEnd_1653277 : Nat := 565950504015622186556149

theorem tailTrace_1653277 : CollatzResearch.WordTrace tailWord_1653277 prefixEnd_1653277 565950504015622186556149 := by
  unfold tailWord_1653277
  simp only [CollatzResearch.WordTrace]
  refine ⟨60299966031467261077102085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40199977354311507384734723 60299966031467261077102085)
  ·
    refine ⟨11306243630900111451956641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60299966031467261077102085 11306243630900111451956641)
    ·
      refine ⟨8479682723175083588967481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11306243630900111451956641 8479682723175083588967481)
      ·
        refine ⟨6359762042381312691725611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8479682723175083588967481 6359762042381312691725611)
        ·
          refine ⟨9539643063571969037588417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359762042381312691725611 9539643063571969037588417)
          ·
            refine ⟨7154732297678976778191313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9539643063571969037588417 7154732297678976778191313)
            ·
              refine ⟨5366049223259232583643485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7154732297678976778191313 5366049223259232583643485)
              ·
                refine ⟨2012268458722212218866307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5366049223259232583643485 2012268458722212218866307)
                ·
                  refine ⟨3018402688083318328299461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012268458722212218866307 3018402688083318328299461)
                  ·
                    refine ⟨565950504015622186556149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018402688083318328299461 565950504015622186556149)
                    ·
                      rfl

theorem cell22_1653277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1653277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653277 prefixEnd_1653277 := by exact prefixLift 1653277
  have htrace : WordTrace (prefixWord ++ tailWord_1653277) baseStart_1653277 baseEnd_1653277 := by
    simpa [prefixWord, tailWord_1653277, baseEnd_1653277] using wordTrace_append hprefix tailTrace_1653277
  have hstable : (prefixWord ++ tailWord_1653277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653277).length < 2 ^ (prefixWord ++ tailWord_1653277).sum := by decide
  have hdescent : baseEnd_1653277 < baseStart_1653277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653305 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_1653305 : Nat := 118140960795 + 1653305 * 2 ^ 59
def prefixEnd_1653305 : Nat := 4983230072969 + 3 ^ 40 * 1653305 * 2
def baseEnd_1653305 : Nat := 565960088987839446856063

theorem tailTrace_1653305 : CollatzResearch.WordTrace tailWord_1653305 prefixEnd_1653305 565960088987839446856063 := by
  unfold tailWord_1653305
  simp only [CollatzResearch.WordTrace]
  refine ⟨60300987275365821859121369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40200658183577214572747579 60300987275365821859121369)
  ·
    refine ⟨45225740456524366394341027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60300987275365821859121369 45225740456524366394341027)
    ·
      refine ⟨67838610684786549591511541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45225740456524366394341027 67838610684786549591511541)
      ·
        refine ⟨6359869751698739024204207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67838610684786549591511541 6359869751698739024204207)
        ·
          refine ⟨9539804627548108536306311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359869751698739024204207 9539804627548108536306311)
          ·
            refine ⟨14309706941322162804459467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539804627548108536306311 14309706941322162804459467)
            ·
              refine ⟨21464560411983244206689201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309706941322162804459467 21464560411983244206689201)
              ·
                refine ⟨16098420308987433155016901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21464560411983244206689201 16098420308987433155016901)
                ·
                  refine ⟨3018453807935143716565669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16098420308987433155016901 3018453807935143716565669)
                  ·
                    refine ⟨565960088987839446856063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018453807935143716565669 565960088987839446856063)
                    ·
                      rfl

theorem cell22_1653305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_1653305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653305 prefixEnd_1653305 := by exact prefixLift 1653305
  have htrace : WordTrace (prefixWord ++ tailWord_1653305) baseStart_1653305 baseEnd_1653305 := by
    simpa [prefixWord, tailWord_1653305, baseEnd_1653305] using wordTrace_append hprefix tailTrace_1653305
  have hstable : (prefixWord ++ tailWord_1653305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653305).length < 2 ^ (prefixWord ++ tailWord_1653305).sum := by decide
  have hdescent : baseEnd_1653305 < baseStart_1653305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653322 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_1653322 : Nat := 118140960795 + 1653322 * 2 ^ 59
def prefixEnd_1653322 : Nat := 4983230072969 + 3 ^ 40 * 1653322 * 2
def baseEnd_1653322 : Nat := 565965908435257069181011

theorem tailTrace_1653322 : CollatzResearch.WordTrace tailWord_1653322 prefixEnd_1653322 565965908435257069181011 := by
  unfold tailWord_1653322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15075401829076058440622555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40201071544202822508326813 15075401829076058440622555)
  ·
    refine ⟨22613102743614087660933833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15075401829076058440622555 22613102743614087660933833)
    ·
      refine ⟨16959827057710565745700375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22613102743614087660933833 16959827057710565745700375)
      ·
        refine ⟨25439740586565848618550563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16959827057710565745700375 25439740586565848618550563)
        ·
          refine ⟨38159610879848772927825845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25439740586565848618550563 38159610879848772927825845)
          ·
            refine ⟨3577463519985822461983673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38159610879848772927825845 3577463519985822461983673)
            ·
              refine ⟨2683097639989366846487755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577463519985822461983673 2683097639989366846487755)
              ·
                refine ⟨4024646459984050269731633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683097639989366846487755 4024646459984050269731633)
                ·
                  refine ⟨3018484844988037702298725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024646459984050269731633 3018484844988037702298725)
                  ·
                    refine ⟨565965908435257069181011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018484844988037702298725 565965908435257069181011)
                    ·
                      rfl

theorem cell22_1653322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_1653322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653322 prefixEnd_1653322 := by exact prefixLift 1653322
  have htrace : WordTrace (prefixWord ++ tailWord_1653322) baseStart_1653322 baseEnd_1653322 := by
    simpa [prefixWord, tailWord_1653322, baseEnd_1653322] using wordTrace_append hprefix tailTrace_1653322
  have hstable : (prefixWord ++ tailWord_1653322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653322).length < 2 ^ (prefixWord ++ tailWord_1653322).sum := by decide
  have hdescent : baseEnd_1653322 < baseStart_1653322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653429 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_1653429 : Nat := 118140960795 + 1653429 * 2 ^ 59
def prefixEnd_1653429 : Nat := 4983230072969 + 3 ^ 40 * 1653429 * 2
def baseEnd_1653429 : Nat := 566002536721944456755683

theorem tailTrace_1653429 : CollatzResearch.WordTrace tailWord_1653429 prefixEnd_1653429 566002536721944456755683 := by
  unfold tailWord_1653429
  simp only [CollatzResearch.WordTrace]
  refine ⟨60305509926916591036635341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40203673284611060691090227 60305509926916591036635341)
  ·
    refine ⟨22614566222593721638738253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60305509926916591036635341 22614566222593721638738253)
    ·
      refine ⟨8480462333472645614526845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22614566222593721638738253 8480462333472645614526845)
      ·
        refine ⟨3180173375052242105447567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8480462333472645614526845 3180173375052242105447567)
        ·
          refine ⟨4770260062578363158171351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180173375052242105447567 4770260062578363158171351)
          ·
            refine ⟨7155390093867544737257027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4770260062578363158171351 7155390093867544737257027)
            ·
              refine ⟨10733085140801317105885541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155390093867544737257027 10733085140801317105885541)
              ·
                refine ⟨2012453463900246957353539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10733085140801317105885541 2012453463900246957353539)
                ·
                  refine ⟨3018680195850370436030309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012453463900246957353539 3018680195850370436030309)
                  ·
                    refine ⟨566002536721944456755683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018680195850370436030309 566002536721944456755683)
                    ·
                      rfl

theorem cell22_1653429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_1653429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653429 prefixEnd_1653429 := by exact prefixLift 1653429
  have htrace : WordTrace (prefixWord ++ tailWord_1653429) baseStart_1653429 baseEnd_1653429 := by
    simpa [prefixWord, tailWord_1653429, baseEnd_1653429] using wordTrace_append hprefix tailTrace_1653429
  have hstable : (prefixWord ++ tailWord_1653429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653429).length < 2 ^ (prefixWord ++ tailWord_1653429).sum := by decide
  have hdescent : baseEnd_1653429 < baseStart_1653429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653457 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_1653457 : Nat := 118140960795 + 1653457 * 2 ^ 59
def prefixEnd_1653457 : Nat := 4983230072969 + 3 ^ 40 * 1653457 * 2
def baseEnd_1653457 : Nat := 566012121694161717055597

theorem tailTrace_1653457 : CollatzResearch.WordTrace tailWord_1653457 prefixEnd_1653457 566012121694161717055597 := by
  unfold tailWord_1653457
  simp only [CollatzResearch.WordTrace]
  refine ⟨60306531170815151818654625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40204354113876767879103083 60306531170815151818654625)
  ·
    refine ⟨45229898378111363863990969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60306531170815151818654625 45229898378111363863990969)
    ·
      refine ⟨33922423783583522897993227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45229898378111363863990969 33922423783583522897993227)
      ·
        refine ⟨50883635675375284346989841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33922423783583522897993227 50883635675375284346989841)
        ·
          refine ⟨38162726756531463260242381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50883635675375284346989841 38162726756531463260242381)
          ·
            refine ⟨14311022533699298722590893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38162726756531463260242381 14311022533699298722590893)
            ·
              refine ⟨5366633450137237020971585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14311022533699298722590893 5366633450137237020971585)
              ·
                refine ⟨4024975087602927765728689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5366633450137237020971585 4024975087602927765728689)
                ·
                  refine ⟨3018731315702195824296517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024975087602927765728689 3018731315702195824296517)
                  ·
                    refine ⟨566012121694161717055597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018731315702195824296517 566012121694161717055597)
                    ·
                      rfl

theorem cell22_1653457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_1653457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653457 prefixEnd_1653457 := by exact prefixLift 1653457
  have htrace : WordTrace (prefixWord ++ tailWord_1653457) baseStart_1653457 baseEnd_1653457 := by
    simpa [prefixWord, tailWord_1653457, baseEnd_1653457] using wordTrace_append hprefix tailTrace_1653457
  have hstable : (prefixWord ++ tailWord_1653457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653457).length < 2 ^ (prefixWord ++ tailWord_1653457).sum := by decide
  have hdescent : baseEnd_1653457 < baseStart_1653457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653461 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 6]
def baseStart_1653461 : Nat := 118140960795 + 1653461 * 2 ^ 59
def prefixEnd_1653461 : Nat := 4983230072969 + 3 ^ 40 * 1653461 * 2
def baseEnd_1653461 : Nat := 188671163658635679985195

theorem tailTrace_1653461 : CollatzResearch.WordTrace tailWord_1653461 prefixEnd_1653461 188671163658635679985195 := by
  unfold tailWord_1653461
  simp only [CollatzResearch.WordTrace]
  refine ⟨60306677062800660501800237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40204451375200440334533491 60306677062800660501800237)
  ·
    refine ⟨22615003898550247688175089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60306677062800660501800237 22615003898550247688175089)
    ·
      refine ⟨16961252923912685766131317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22615003898550247688175089 16961252923912685766131317)
      ·
        refine ⟨1590117461616814290574811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16961252923912685766131317 1590117461616814290574811)
        ·
          refine ⟨2385176192425221435862217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590117461616814290574811 2385176192425221435862217)
          ·
            refine ⟨1788882144318916076896663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385176192425221435862217 1788882144318916076896663)
            ·
              refine ⟨2683323216478374115344995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788882144318916076896663 2683323216478374115344995)
              ·
                refine ⟨4024984824717561173017493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683323216478374115344995 4024984824717561173017493)
                ·
                  refine ⟨188671163658635679985195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4024984824717561173017493 188671163658635679985195)
                  ·
                    rfl

theorem cell22_1653461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_1653461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653461 prefixEnd_1653461 := by exact prefixLift 1653461
  have htrace : WordTrace (prefixWord ++ tailWord_1653461) baseStart_1653461 baseEnd_1653461 := by
    simpa [prefixWord, tailWord_1653461, baseEnd_1653461] using wordTrace_append hprefix tailTrace_1653461
  have hstable : (prefixWord ++ tailWord_1653461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653461).length < 2 ^ (prefixWord ++ tailWord_1653461).sum := by decide
  have hdescent : baseEnd_1653461 < baseStart_1653461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653476 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_1653476 : Nat := 118140960795 + 1653476 * 2 ^ 59
def prefixEnd_1653476 : Nat := 4983230072969 + 3 ^ 40 * 1653476 * 2
def baseEnd_1653476 : Nat := 566018625782452000830539

theorem tailTrace_1653476 : CollatzResearch.WordTrace tailWord_1653476 prefixEnd_1653476 566018625782452000830539 := by
  unfold tailWord_1653476
  simp only [CollatzResearch.WordTrace]
  refine ⟨30153612078873159031798141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40204816105164212042397521 30153612078873159031798141)
  ·
    refine ⟨11307604529577434636924303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30153612078873159031798141 11307604529577434636924303)
    ·
      refine ⟨16961406794366151955386455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11307604529577434636924303 16961406794366151955386455)
      ·
        refine ⟨25442110191549227933079683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16961406794366151955386455 25442110191549227933079683)
        ·
          refine ⟨38163165287323841899619525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25442110191549227933079683 38163165287323841899619525)
          ·
            refine ⟨7155593491373220356178661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38163165287323841899619525 7155593491373220356178661)
            ·
              refine ⟨1341673779632478816783499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7155593491373220356178661 1341673779632478816783499)
              ·
                refine ⟨2012510669448718225175249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341673779632478816783499 2012510669448718225175249)
                ·
                  refine ⟨1509383002086538668881437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2012510669448718225175249 1509383002086538668881437)
                  ·
                    refine ⟨566018625782452000830539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1509383002086538668881437 566018625782452000830539)
                    ·
                      rfl

theorem cell22_1653476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_1653476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653476 prefixEnd_1653476 := by exact prefixLift 1653476
  have htrace : WordTrace (prefixWord ++ tailWord_1653476) baseStart_1653476 baseEnd_1653476 := by
    simpa [prefixWord, tailWord_1653476, baseEnd_1653476] using wordTrace_append hprefix tailTrace_1653476
  have hstable : (prefixWord ++ tailWord_1653476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653476).length < 2 ^ (prefixWord ++ tailWord_1653476).sum := by decide
  have hdescent : baseEnd_1653476 < baseStart_1653476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653493 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1653493 : Nat := 118140960795 + 1653493 * 2 ^ 59
def prefixEnd_1653493 : Nat := 4983230072969 + 3 ^ 40 * 1653493 * 2
def baseEnd_1653493 : Nat := 566024445229869623155487

theorem tailTrace_1653493 : CollatzResearch.WordTrace tailWord_1653493 prefixEnd_1653493 566024445229869623155487 := by
  unfold tailWord_1653493
  simp only [CollatzResearch.WordTrace]
  refine ⟨60307844198684729966965133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40205229465789819977976755 60307844198684729966965133)
  ·
    refine ⟨22615441574506773737611925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60307844198684729966965133 22615441574506773737611925)
    ·
      refine ⟨1060098823805005018950559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22615441574506773737611925 1060098823805005018950559)
      ·
        refine ⟨1590148235707507528425839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060098823805005018950559 1590148235707507528425839)
        ·
          refine ⟨2385222353561261292638759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590148235707507528425839 2385222353561261292638759)
          ·
            refine ⟨3577833530341891938958139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385222353561261292638759 3577833530341891938958139)
            ·
              refine ⟨5366750295512837908437209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577833530341891938958139 5366750295512837908437209)
              ·
                refine ⟨4025062721634628431327907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5366750295512837908437209 4025062721634628431327907)
                ·
                  refine ⟨6037594082451942646991861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025062721634628431327907 6037594082451942646991861)
                  ·
                    refine ⟨566024445229869623155487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6037594082451942646991861 566024445229869623155487)
                    ·
                      rfl

theorem cell22_1653493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1653493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653493 prefixEnd_1653493 := by exact prefixLift 1653493
  have htrace : WordTrace (prefixWord ++ tailWord_1653493) baseStart_1653493 baseEnd_1653493 := by
    simpa [prefixWord, tailWord_1653493, baseEnd_1653493] using wordTrace_append hprefix tailTrace_1653493
  have hstable : (prefixWord ++ tailWord_1653493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653493).length < 2 ^ (prefixWord ++ tailWord_1653493).sum := by decide
  have hdescent : baseEnd_1653493 < baseStart_1653493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653532 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1653532 : Nat := 118140960795 + 1653532 * 2 ^ 59
def prefixEnd_1653532 : Nat := 4983230072969 + 3 ^ 40 * 1653532 * 2
def baseEnd_1653532 : Nat := 566037795726886521430367

theorem tailTrace_1653532 : CollatzResearch.WordTrace tailWord_1653532 prefixEnd_1653532 566037795726886521430367 := by
  unfold tailWord_1653532
  simp only [CollatzResearch.WordTrace]
  refine ⟨30154633322771719813817425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40206177763695626418423233 30154633322771719813817425)
  ·
    refine ⟨22615974992078789860363069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30154633322771719813817425 22615974992078789860363069)
    ·
      refine ⟨8480990622029546197636151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22615974992078789860363069 8480990622029546197636151)
      ·
        refine ⟨12721485933044319296454227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8480990622029546197636151 12721485933044319296454227)
        ·
          refine ⟨19082228899566478944681341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12721485933044319296454227 19082228899566478944681341)
          ·
            refine ⟨7155835837337429604255503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19082228899566478944681341 7155835837337429604255503)
            ·
              refine ⟨10733753756006144406383255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155835837337429604255503 10733753756006144406383255)
              ·
                refine ⟨16100630634009216609574883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10733753756006144406383255 16100630634009216609574883)
                ·
                  refine ⟨24150945951013824914362325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16100630634009216609574883 24150945951013824914362325)
                  ·
                    refine ⟨566037795726886521430367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24150945951013824914362325 566037795726886521430367)
                    ·
                      rfl

theorem cell22_1653532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1653532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653532 prefixEnd_1653532 := by exact prefixLift 1653532
  have htrace : WordTrace (prefixWord ++ tailWord_1653532) baseStart_1653532 baseEnd_1653532 := by
    simpa [prefixWord, tailWord_1653532, baseEnd_1653532] using wordTrace_append hprefix tailTrace_1653532
  have hstable : (prefixWord ++ tailWord_1653532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653532).length < 2 ^ (prefixWord ++ tailWord_1653532).sum := by decide
  have hdescent : baseEnd_1653532 < baseStart_1653532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653594 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_1653594 : Nat := 118140960795 + 1653594 * 2 ^ 59
def prefixEnd_1653594 : Nat := 4983230072969 + 3 ^ 40 * 1653594 * 2
def baseEnd_1653594 : Nat := 566059019593939026380177

theorem tailTrace_1653594 : CollatzResearch.WordTrace tailWord_1653594 prefixEnd_1653594 566059019593939026380177 := by
  unfold tailWord_1653594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15077881992829706054097959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40207685314212549477594557 15077881992829706054097959)
  ·
    refine ⟨22616822989244559081146939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15077881992829706054097959 22616822989244559081146939)
    ·
      refine ⟨33925234483866838621720409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22616822989244559081146939 33925234483866838621720409)
      ·
        refine ⟨25443925862900128966290307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33925234483866838621720409 25443925862900128966290307)
        ·
          refine ⟨38165888794350193449435461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25443925862900128966290307 38165888794350193449435461)
          ·
            refine ⟨7156104148940661271769149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38165888794350193449435461 7156104148940661271769149)
            ·
              refine ⟨2683539055852747976913431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7156104148940661271769149 2683539055852747976913431)
              ·
                refine ⟨4025308583779121965370147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683539055852747976913431 4025308583779121965370147)
                ·
                  refine ⟨6037962875668682948055221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025308583779121965370147 6037962875668682948055221)
                  ·
                    refine ⟨566059019593939026380177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6037962875668682948055221 566059019593939026380177)
                    ·
                      rfl

theorem cell22_1653594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_1653594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653594 prefixEnd_1653594 := by exact prefixLift 1653594
  have htrace : WordTrace (prefixWord ++ tailWord_1653594) baseStart_1653594 baseEnd_1653594 := by
    simpa [prefixWord, tailWord_1653594, baseEnd_1653594] using wordTrace_append hprefix tailTrace_1653594
  have hstable : (prefixWord ++ tailWord_1653594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653594).length < 2 ^ (prefixWord ++ tailWord_1653594).sum := by decide
  have hdescent : baseEnd_1653594 < baseStart_1653594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653630 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_1653630 : Nat := 118140960795 + 1653630 * 2 ^ 59
def prefixEnd_1653630 : Nat := 4983230072969 + 3 ^ 40 * 1653630 * 2
def baseEnd_1653630 : Nat := 188690447709882310826689

theorem tailTrace_1653630 : CollatzResearch.WordTrace tailWord_1653630 prefixEnd_1653630 188690447709882310826689 := by
  unfold tailWord_1653630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539105124898550295587793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40208560666125601576468229 7539105124898550295587793)
  ·
    refine ⟨5654328843673912721690845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7539105124898550295587793 5654328843673912721690845)
    ·
      refine ⟨2120373316377717270634067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5654328843673912721690845 2120373316377717270634067)
      ·
        refine ⟨3180559974566575905951101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120373316377717270634067 3180559974566575905951101)
        ·
          refine ⟨1192709990462465964731663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3180559974566575905951101 1192709990462465964731663)
          ·
            refine ⟨1789064985693698947097495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192709990462465964731663 1789064985693698947097495)
            ·
              refine ⟨2683597478540548420646243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789064985693698947097495 2683597478540548420646243)
              ·
                refine ⟨4025396217810822630969365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683597478540548420646243 4025396217810822630969365)
                ·
                  refine ⟨188690447709882310826689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4025396217810822630969365 188690447709882310826689)
                  ·
                    rfl

theorem cell22_1653630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_1653630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653630 prefixEnd_1653630 := by exact prefixLift 1653630
  have htrace : WordTrace (prefixWord ++ tailWord_1653630) baseStart_1653630 baseEnd_1653630 := by
    simpa [prefixWord, tailWord_1653630, baseEnd_1653630] using wordTrace_append hprefix tailTrace_1653630
  have hstable : (prefixWord ++ tailWord_1653630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653630).length < 2 ^ (prefixWord ++ tailWord_1653630).sum := by decide
  have hdescent : baseEnd_1653630 < baseStart_1653630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653716 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1653716 : Nat := 118140960795 + 1653716 * 2 ^ 59
def prefixEnd_1653716 : Nat := 4983230072969 + 3 ^ 40 * 1653716 * 2
def baseEnd_1653716 : Nat := 566100782687171374829803

theorem tailTrace_1653716 : CollatzResearch.WordTrace tailWord_1653716 prefixEnd_1653716 566100782687171374829803 := by
  unfold tailWord_1653716
  simp only [CollatzResearch.WordTrace]
  refine ⟨30157988838438419526166501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40210651784584559368222001 30157988838438419526166501)
  ·
    refine ⟨5654622907207203661156219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30157988838438419526166501 5654622907207203661156219)
    ·
      refine ⟨8481934360810805491734329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654622907207203661156219 8481934360810805491734329)
      ·
        refine ⟨6361450770608104118800747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8481934360810805491734329 6361450770608104118800747)
        ·
          refine ⟨9542176155912156178201121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361450770608104118800747 9542176155912156178201121)
          ·
            refine ⟨7156632116934117133650841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9542176155912156178201121 7156632116934117133650841)
            ·
              refine ⟨5367474087700587850238131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7156632116934117133650841 5367474087700587850238131)
              ·
                refine ⟨8051211131550881775357197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5367474087700587850238131 8051211131550881775357197)
                ·
                  refine ⟨3019204174331580665758949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8051211131550881775357197 3019204174331580665758949)
                  ·
                    refine ⟨566100782687171374829803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3019204174331580665758949 566100782687171374829803)
                    ·
                      rfl

theorem cell22_1653716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1653716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653716 prefixEnd_1653716 := by exact prefixLift 1653716
  have htrace : WordTrace (prefixWord ++ tailWord_1653716) baseStart_1653716 baseEnd_1653716 := by
    simpa [prefixWord, tailWord_1653716, baseEnd_1653716] using wordTrace_append hprefix tailTrace_1653716
  have hstable : (prefixWord ++ tailWord_1653716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653716).length < 2 ^ (prefixWord ++ tailWord_1653716).sum := by decide
  have hdescent : baseEnd_1653716 < baseStart_1653716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653744 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_1653744 : Nat := 118140960795 + 1653744 * 2 ^ 59
def prefixEnd_1653744 : Nat := 4983230072969 + 3 ^ 40 * 1653744 * 2
def baseEnd_1653744 : Nat := 566110367659388635129717

theorem tailTrace_1653744 : CollatzResearch.WordTrace tailWord_1653744 prefixEnd_1653744 566110367659388635129717 := by
  unfold tailWord_1653744
  simp only [CollatzResearch.WordTrace]
  refine ⟨30158499460387699917176143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40211332613850266556234857 30158499460387699917176143)
  ·
    refine ⟨45237749190581549875764215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30158499460387699917176143 45237749190581549875764215)
    ·
      refine ⟨67856623785872324813646323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45237749190581549875764215 67856623785872324813646323)
      ·
        refine ⟨101784935678808487220469485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67856623785872324813646323 101784935678808487220469485)
        ·
          refine ⟨38169350879553182707676057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101784935678808487220469485 38169350879553182707676057)
          ·
            refine ⟨28627013159664887030757043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38169350879553182707676057 28627013159664887030757043)
            ·
              refine ⟨42940519739497330546135565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28627013159664887030757043 42940519739497330546135565)
              ·
                refine ⟨16102694902311498954800837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42940519739497330546135565 16102694902311498954800837)
                ·
                  refine ⟨3019255294183406054025157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16102694902311498954800837 3019255294183406054025157)
                  ·
                    refine ⟨566110367659388635129717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3019255294183406054025157 566110367659388635129717)
                    ·
                      rfl

theorem cell22_1653744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_1653744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653744 prefixEnd_1653744 := by exact prefixLift 1653744
  have htrace : WordTrace (prefixWord ++ tailWord_1653744) baseStart_1653744 baseEnd_1653744 := by
    simpa [prefixWord, tailWord_1653744, baseEnd_1653744] using wordTrace_append hprefix tailTrace_1653744
  have hstable : (prefixWord ++ tailWord_1653744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653744).length < 2 ^ (prefixWord ++ tailWord_1653744).sum := by decide
  have hdescent : baseEnd_1653744 < baseStart_1653744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653804 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 7]
def baseStart_1653804 : Nat := 118140960795 + 1653804 * 2 ^ 59
def prefixEnd_1653804 : Nat := 4983230072969 + 3 ^ 40 * 1653804 * 2
def baseEnd_1653804 : Nat := 188710302295189492876511

theorem tailTrace_1653804 : CollatzResearch.WordTrace tailWord_1653804 prefixEnd_1653804 188710302295189492876511 := by
  unfold tailWord_1653804
  simp only [CollatzResearch.WordTrace]
  refine ⟨30159593650279015040768233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40212791533705353387690977 30159593650279015040768233)
  ·
    refine ⟨22619695237709261280576175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30159593650279015040768233 22619695237709261280576175)
    ·
      refine ⟨33929542856563891920864263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22619695237709261280576175 33929542856563891920864263)
      ·
        refine ⟨50894314284845837881296395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33929542856563891920864263 50894314284845837881296395)
        ·
          refine ⟨76341471427268756821944593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50894314284845837881296395 76341471427268756821944593)
          ·
            refine ⟨57256103570451567616458445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76341471427268756821944593 57256103570451567616458445)
            ·
              refine ⟨21471038838919337856171917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57256103570451567616458445 21471038838919337856171917)
              ·
                refine ⟨8051639564594751696064469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21471038838919337856171917 8051639564594751696064469)
                ·
                  refine ⟨188710302295189492876511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8051639564594751696064469 188710302295189492876511)
                  ·
                    rfl

theorem cell22_1653804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_1653804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653804 prefixEnd_1653804 := by exact prefixLift 1653804
  have htrace : WordTrace (prefixWord ++ tailWord_1653804) baseStart_1653804 baseEnd_1653804 := by
    simpa [prefixWord, tailWord_1653804, baseEnd_1653804] using wordTrace_append hprefix tailTrace_1653804
  have hstable : (prefixWord ++ tailWord_1653804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653804).length < 2 ^ (prefixWord ++ tailWord_1653804).sum := by decide
  have hdescent : baseEnd_1653804 < baseStart_1653804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653806 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1653806 : Nat := 118140960795 + 1653806 * 2 ^ 59
def prefixEnd_1653806 : Nat := 4983230072969 + 3 ^ 40 * 1653806 * 2
def baseEnd_1653806 : Nat := 566131591526441140079527

theorem tailTrace_1653806 : CollatzResearch.WordTrace tailWord_1653806 prefixEnd_1653806 566131591526441140079527 := by
  unfold tailWord_1653806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539907530818848052888659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40212840164367189615406181 7539907530818848052888659)
  ·
    refine ⟨11309861296228272079332989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7539907530818848052888659 11309861296228272079332989)
    ·
      refine ⟨4241197986085602029749871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11309861296228272079332989 4241197986085602029749871)
      ·
        refine ⟨6361796979128403044624807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241197986085602029749871 6361796979128403044624807)
        ·
          refine ⟨9542695468692604566937211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361796979128403044624807 9542695468692604566937211)
          ·
            refine ⟨14314043203038906850405817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542695468692604566937211 14314043203038906850405817)
            ·
              refine ⟨10735532402279180137804363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14314043203038906850405817 10735532402279180137804363)
              ·
                refine ⟨16103298603418770206706545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735532402279180137804363 16103298603418770206706545)
                ·
                  refine ⟨12077473952564077655029909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16103298603418770206706545 12077473952564077655029909)
                  ·
                    refine ⟨566131591526441140079527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12077473952564077655029909 566131591526441140079527)
                    ·
                      rfl

theorem cell22_1653806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1653806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653806 prefixEnd_1653806 := by exact prefixLift 1653806
  have htrace : WordTrace (prefixWord ++ tailWord_1653806) baseStart_1653806 baseEnd_1653806 := by
    simpa [prefixWord, tailWord_1653806, baseEnd_1653806] using wordTrace_append hprefix tailTrace_1653806
  have hstable : (prefixWord ++ tailWord_1653806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653806).length < 2 ^ (prefixWord ++ tailWord_1653806).sum := by decide
  have hdescent : baseEnd_1653806 < baseStart_1653806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653849 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 10]
def baseStart_1653849 : Nat := 118140960795 + 1653849 * 2 ^ 59
def prefixEnd_1653849 : Nat := 4983230072969 + 3 ^ 40 * 1653849 * 2
def baseEnd_1653849 : Nat := 188715437101734453751465

theorem tailTrace_1653849 : CollatzResearch.WordTrace tailWord_1653849 prefixEnd_1653849 188715437101734453751465 := by
  unfold tailWord_1653849
  simp only [CollatzResearch.WordTrace]
  refine ⟨60320828585395002766924601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40213885723596668511283067 60320828585395002766924601)
  ·
    refine ⟨45240621439046252075193451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60320828585395002766924601 45240621439046252075193451)
    ·
      refine ⟨67860932158569378112790177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45240621439046252075193451 67860932158569378112790177)
      ·
        refine ⟨50895699118927033584592633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67860932158569378112790177 50895699118927033584592633)
        ·
          refine ⟨38171774339195275188444475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50895699118927033584592633 38171774339195275188444475)
          ·
            refine ⟨57257661508792912782666713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38171774339195275188444475 57257661508792912782666713)
            ·
              refine ⟨42943246131594684587000035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57257661508792912782666713 42943246131594684587000035)
              ·
                refine ⟨64414869197392026880500053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42943246131594684587000035 64414869197392026880500053)
                ·
                  refine ⟨188715437101734453751465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 64414869197392026880500053 188715437101734453751465)
                  ·
                    rfl

theorem cell22_1653849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_1653849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653849 prefixEnd_1653849 := by exact prefixLift 1653849
  have htrace : WordTrace (prefixWord ++ tailWord_1653849) baseStart_1653849 baseEnd_1653849 := by
    simpa [prefixWord, tailWord_1653849, baseEnd_1653849] using wordTrace_append hprefix tailTrace_1653849
  have hstable : (prefixWord ++ tailWord_1653849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653849).length < 2 ^ (prefixWord ++ tailWord_1653849).sum := by decide
  have hdescent : baseEnd_1653849 < baseStart_1653849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653898 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_1653898 : Nat := 118140960795 + 1653898 * 2 ^ 59
def prefixEnd_1653898 : Nat := 4983230072969 + 3 ^ 40 * 1653898 * 2
def baseEnd_1653898 : Nat := 566163085006583566779245

theorem tailTrace_1653898 : CollatzResearch.WordTrace tailWord_1653898 prefixEnd_1653898 566163085006583566779245 := by
  unfold tailWord_1653898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15080653940554371033864587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40215077174811656090305565 15080653940554371033864587)
  ·
    refine ⟨22620980910831556550796881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15080653940554371033864587 22620980910831556550796881)
    ·
      refine ⟨16965735683123667413097661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22620980910831556550796881 16965735683123667413097661)
      ·
        refine ⟨6362150881171375279911623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16965735683123667413097661 6362150881171375279911623)
        ·
          refine ⟨9543226321757062919867435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6362150881171375279911623 9543226321757062919867435)
          ·
            refine ⟨14314839482635594379801153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9543226321757062919867435 14314839482635594379801153)
            ·
              refine ⟨10736129611976695784850865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14314839482635594379801153 10736129611976695784850865)
              ·
                refine ⟨8052097208982521838638149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10736129611976695784850865 8052097208982521838638149)
                ·
                  refine ⟨1509768226684222844744653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8052097208982521838638149 1509768226684222844744653)
                  ·
                    refine ⟨566163085006583566779245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1509768226684222844744653 566163085006583566779245)
                    ·
                      rfl

theorem cell22_1653898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_1653898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653898 prefixEnd_1653898 := by exact prefixLift 1653898
  have htrace : WordTrace (prefixWord ++ tailWord_1653898) baseStart_1653898 baseEnd_1653898 := by
    simpa [prefixWord, tailWord_1653898, baseEnd_1653898] using wordTrace_append hprefix tailTrace_1653898
  have hstable : (prefixWord ++ tailWord_1653898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653898).length < 2 ^ (prefixWord ++ tailWord_1653898).sum := by decide
  have hdescent : baseEnd_1653898 < baseStart_1653898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653902 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_1653902 : Nat := 118140960795 + 1653902 * 2 ^ 59
def prefixEnd_1653902 : Nat := 4983230072969 + 3 ^ 40 * 1653902 * 2
def baseEnd_1653902 : Nat := 566164454288328889679233

theorem tailTrace_1653902 : CollatzResearch.WordTrace tailWord_1653902 prefixEnd_1653902 566164454288328889679233 := by
  unfold tailWord_1653902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540345206775374102325495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40215174436135328545735973 7540345206775374102325495)
  ·
    refine ⟨11310517810163061153488243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7540345206775374102325495 11310517810163061153488243)
    ·
      refine ⟨16965776715244591730232365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11310517810163061153488243 16965776715244591730232365)
      ·
        refine ⟨6362166268216721898837137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16965776715244591730232365 6362166268216721898837137)
        ·
          refine ⟨4771624701162541424127853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6362166268216721898837137 4771624701162541424127853)
          ·
            refine ⟨1789359262935953034047945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4771624701162541424127853 1789359262935953034047945)
            ·
              refine ⟨1342019447201964775535959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789359262935953034047945 1342019447201964775535959)
              ·
                refine ⟨2013029170802947163303939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342019447201964775535959 2013029170802947163303939)
                ·
                  refine ⟨3019543756204420744955909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013029170802947163303939 3019543756204420744955909)
                  ·
                    refine ⟨566164454288328889679233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3019543756204420744955909 566164454288328889679233)
                    ·
                      rfl

theorem cell22_1653902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_1653902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653902 prefixEnd_1653902 := by exact prefixLift 1653902
  have htrace : WordTrace (prefixWord ++ tailWord_1653902) baseStart_1653902 baseEnd_1653902 := by
    simpa [prefixWord, tailWord_1653902, baseEnd_1653902] using wordTrace_append hprefix tailTrace_1653902
  have hstable : (prefixWord ++ tailWord_1653902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653902).length < 2 ^ (prefixWord ++ tailWord_1653902).sum := by decide
  have hdescent : baseEnd_1653902 < baseStart_1653902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653911 : List Nat := [1, 1, 3, 3, 3, 2, 9]
def baseStart_1653911 : Nat := 118140960795 + 1653911 * 2 ^ 59
def prefixEnd_1653911 : Nat := 4983230072969 + 3 ^ 40 * 1653911 * 2
def baseEnd_1653911 : Nat := 20969167969342809859415

theorem tailTrace_1653911 : CollatzResearch.WordTrace tailWord_1653911 prefixEnd_1653911 20969167969342809859415 := by
  unfold tailWord_1653911
  simp only [CollatzResearch.WordTrace]
  refine ⟨60323089911170387355681587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40215393274113591570454391 60323089911170387355681587)
  ·
    refine ⟨90484634866755581033522381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60323089911170387355681587 90484634866755581033522381)
    ·
      refine ⟨33931738075033342887570893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90484634866755581033522381 33931738075033342887570893)
      ·
        refine ⟨12724401778137503582839085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33931738075033342887570893 12724401778137503582839085)
        ·
          refine ⟨4771650666801563843564657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12724401778137503582839085 4771650666801563843564657)
          ·
            refine ⟨3578738000101172882673493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771650666801563843564657 3578738000101172882673493)
            ·
              refine ⟨20969167969342809859415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3578738000101172882673493 20969167969342809859415)
              ·
                rfl

theorem cell22_1653911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 9].length) (baseStart_1653911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653911 prefixEnd_1653911 := by exact prefixLift 1653911
  have htrace : WordTrace (prefixWord ++ tailWord_1653911) baseStart_1653911 baseEnd_1653911 := by
    simpa [prefixWord, tailWord_1653911, baseEnd_1653911] using wordTrace_append hprefix tailTrace_1653911
  have hstable : (prefixWord ++ tailWord_1653911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653911).length < 2 ^ (prefixWord ++ tailWord_1653911).sum := by decide
  have hdescent : baseEnd_1653911 < baseStart_1653911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653943 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 3, 3]
def baseStart_1653943 : Nat := 118140960795 + 1653943 * 2 ^ 59
def prefixEnd_1653943 : Nat := 4983230072969 + 3 ^ 40 * 1653943 * 2
def baseEnd_1653943 : Nat := 566178489426218449404107

theorem tailTrace_1653943 : CollatzResearch.WordTrace tailWord_1653943 prefixEnd_1653943 566178489426218449404107 := by
  unfold tailWord_1653943
  simp only [CollatzResearch.WordTrace]
  refine ⟨60324257047054456820846483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40216171364702971213897655 60324257047054456820846483)
  ·
    refine ⟨90486385570581685231269725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60324257047054456820846483 90486385570581685231269725)
    ·
      refine ⟨33932394588968131961726147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90486385570581685231269725 33932394588968131961726147)
      ·
        refine ⟨50898591883452197942589221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33932394588968131961726147 50898591883452197942589221)
        ·
          refine ⟨9543485978147287114235479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50898591883452197942589221 9543485978147287114235479)
          ·
            refine ⟨14315228967220930671353219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9543485978147287114235479 14315228967220930671353219)
            ·
              refine ⟨21472843450831396007029829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14315228967220930671353219 21472843450831396007029829)
              ·
                refine ⟨4026158147030886751318093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21472843450831396007029829 4026158147030886751318093)
                ·
                  refine ⟨1509809305136582531744285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4026158147030886751318093 1509809305136582531744285)
                  ·
                    refine ⟨566178489426218449404107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1509809305136582531744285 566178489426218449404107)
                    ·
                      rfl

theorem cell22_1653943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_1653943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653943 prefixEnd_1653943 := by exact prefixLift 1653943
  have htrace : WordTrace (prefixWord ++ tailWord_1653943) baseStart_1653943 baseEnd_1653943 := by
    simpa [prefixWord, tailWord_1653943, baseEnd_1653943] using wordTrace_append hprefix tailTrace_1653943
  have hstable : (prefixWord ++ tailWord_1653943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653943).length < 2 ^ (prefixWord ++ tailWord_1653943).sum := by decide
  have hdescent : baseEnd_1653943 < baseStart_1653943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653973 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 7]
def baseStart_1653973 : Nat := 118140960795 + 1653973 * 2 ^ 59
def prefixEnd_1653973 : Nat := 4983230072969 + 3 ^ 40 * 1653973 * 2
def baseEnd_1653973 : Nat := 188729586346436123718005

theorem tailTrace_1653973 : CollatzResearch.WordTrace tailWord_1653973 prefixEnd_1653973 188729586346436123718005 := by
  unfold tailWord_1653973
  simp only [CollatzResearch.WordTrace]
  refine ⟨60325351236945771944438573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40216900824630514629625715 60325351236945771944438573)
  ·
    refine ⟨22622006713854664479164465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60325351236945771944438573 22622006713854664479164465)
    ·
      refine ⟨16966505035390998359373349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22622006713854664479164465 16966505035390998359373349)
      ·
        refine ⟨3181219694135812192382503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16966505035390998359373349 3181219694135812192382503)
        ·
          refine ⟨4771829541203718288573755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181219694135812192382503 4771829541203718288573755)
          ·
            refine ⟨7157744311805577432860633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771829541203718288573755 7157744311805577432860633)
            ·
              refine ⟨5368308233854183074645475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7157744311805577432860633 5368308233854183074645475)
              ·
                refine ⟨8052462350781274611968213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368308233854183074645475 8052462350781274611968213)
                ·
                  refine ⟨188729586346436123718005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8052462350781274611968213 188729586346436123718005)
                  ·
                    rfl

theorem cell22_1653973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_1653973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1653973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1653973 prefixEnd_1653973 := by exact prefixLift 1653973
  have htrace : WordTrace (prefixWord ++ tailWord_1653973) baseStart_1653973 baseEnd_1653973 := by
    simpa [prefixWord, tailWord_1653973, baseEnd_1653973] using wordTrace_append hprefix tailTrace_1653973
  have hstable : (prefixWord ++ tailWord_1653973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653973).length < 2 ^ (prefixWord ++ tailWord_1653973).sum := by decide
  have hdescent : baseEnd_1653973 < baseStart_1653973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654001 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 8]
def baseStart_1654001 : Nat := 118140960795 + 1654001 * 2 ^ 59
def prefixEnd_1654001 : Nat := 4983230072969 + 3 ^ 40 * 1654001 * 2
def baseEnd_1654001 : Nat := 188732781337175210484643

theorem tailTrace_1654001 : CollatzResearch.WordTrace tailWord_1654001 prefixEnd_1654001 188732781337175210484643 := by
  unfold tailWord_1654001
  simp only [CollatzResearch.WordTrace]
  refine ⟨60326372480844332726457857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40217581653896221817638571 60326372480844332726457857)
  ·
    refine ⟨45244779360633249544843393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60326372480844332726457857 45244779360633249544843393)
    ·
      refine ⟨33933584520474937158632545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45244779360633249544843393 33933584520474937158632545)
      ·
        refine ⟨25450188390356202868974409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33933584520474937158632545 25450188390356202868974409)
        ·
          refine ⟨19087641292767152151730807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25450188390356202868974409 19087641292767152151730807)
          ·
            refine ⟨28631461939150728227596211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19087641292767152151730807 28631461939150728227596211)
            ·
              refine ⟨42947192908726092341394317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28631461939150728227596211 42947192908726092341394317)
              ·
                refine ⟨16105197340772284628022869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42947192908726092341394317 16105197340772284628022869)
                ·
                  refine ⟨188732781337175210484643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16105197340772284628022869 188732781337175210484643)
                  ·
                    rfl

theorem cell22_1654001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_1654001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654001 prefixEnd_1654001 := by exact prefixLift 1654001
  have htrace : WordTrace (prefixWord ++ tailWord_1654001) baseStart_1654001 baseEnd_1654001 := by
    simpa [prefixWord, tailWord_1654001, baseEnd_1654001] using wordTrace_append hprefix tailTrace_1654001
  have hstable : (prefixWord ++ tailWord_1654001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654001).length < 2 ^ (prefixWord ++ tailWord_1654001).sum := by decide
  have hdescent : baseEnd_1654001 < baseStart_1654001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654003 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 3, 4]
def baseStart_1654003 : Nat := 118140960795 + 1654003 * 2 ^ 59
def prefixEnd_1654003 : Nat := 4983230072969 + 3 ^ 40 * 1654003 * 2
def baseEnd_1654003 : Nat := 566199028652398292903923

theorem tailTrace_1654003 : CollatzResearch.WordTrace tailWord_1654003 prefixEnd_1654003 566199028652398292903923 := by
  unfold tailWord_1654003
  simp only [CollatzResearch.WordTrace]
  refine ⟨60326445426837087068030663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40217630284558058045353775 60326445426837087068030663)
  ·
    refine ⟨90489668140255630602045995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60326445426837087068030663 90489668140255630602045995)
    ·
      refine ⟨135734502210383445903068993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90489668140255630602045995 135734502210383445903068993)
      ·
        refine ⟨101800876657787584427301745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135734502210383445903068993 101800876657787584427301745)
        ·
          refine ⟨76350657493340688320476309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101800876657787584427301745 76350657493340688320476309)
          ·
            refine ⟨3578937070000344765022327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76350657493340688320476309 3578937070000344765022327)
            ·
              refine ⟨5368405605000517147533491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578937070000344765022327 5368405605000517147533491)
              ·
                refine ⟨8052608407500775721300237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368405605000517147533491 8052608407500775721300237)
                ·
                  refine ⟨3019728152812790895487589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8052608407500775721300237 3019728152812790895487589)
                  ·
                    refine ⟨566199028652398292903923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3019728152812790895487589 566199028652398292903923)
                    ·
                      rfl

theorem cell22_1654003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 4].length) (baseStart_1654003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654003 prefixEnd_1654003 := by exact prefixLift 1654003
  have htrace : WordTrace (prefixWord ++ tailWord_1654003) baseStart_1654003 baseEnd_1654003 := by
    simpa [prefixWord, tailWord_1654003, baseEnd_1654003] using wordTrace_append hprefix tailTrace_1654003
  have hstable : (prefixWord ++ tailWord_1654003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654003).length < 2 ^ (prefixWord ++ tailWord_1654003).sum := by decide
  have hdescent : baseEnd_1654003 < baseStart_1654003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654031 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 5, 6]
def baseStart_1654031 : Nat := 118140960795 + 1654031 * 2 ^ 59
def prefixEnd_1654031 : Nat := 4983230072969 + 3 ^ 40 * 1654031 * 2
def baseEnd_1654031 : Nat := 566208613624615553203837

theorem tailTrace_1654031 : CollatzResearch.WordTrace tailWord_1654031 prefixEnd_1654031 566208613624615553203837 := by
  unfold tailWord_1654031
  simp only [CollatzResearch.WordTrace]
  refine ⟨60327466670735647850049947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40218311113823765233366631 60327466670735647850049947)
  ·
    refine ⟨90491200006103471775074921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60327466670735647850049947 90491200006103471775074921)
    ·
      refine ⟨67868400004577603831306191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90491200006103471775074921 67868400004577603831306191)
      ·
        refine ⟨101802600006866405746959287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67868400004577603831306191 101802600006866405746959287)
        ·
          refine ⟨152703900010299608620438931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101802600006866405746959287 152703900010299608620438931)
          ·
            refine ⟨229055850015449412930658397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152703900010299608620438931 229055850015449412930658397)
            ·
              refine ⟨85895943755793529848996899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229055850015449412930658397 85895943755793529848996899)
              ·
                refine ⟨128843915633690294773495349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85895943755793529848996899 128843915633690294773495349)
                ·
                  refine ⟨12079117090658465135015189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128843915633690294773495349 12079117090658465135015189)
                  ·
                    refine ⟨566208613624615553203837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12079117090658465135015189 566208613624615553203837)
                    ·
                      rfl

theorem cell22_1654031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_1654031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654031 prefixEnd_1654031 := by exact prefixLift 1654031
  have htrace : WordTrace (prefixWord ++ tailWord_1654031) baseStart_1654031 baseEnd_1654031 := by
    simpa [prefixWord, tailWord_1654031, baseEnd_1654031] using wordTrace_append hprefix tailTrace_1654031
  have hstable : (prefixWord ++ tailWord_1654031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654031).length < 2 ^ (prefixWord ++ tailWord_1654031).sum := by decide
  have hdescent : baseEnd_1654031 < baseStart_1654031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654065 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_1654065 : Nat := 118140960795 + 1654065 * 2 ^ 59
def prefixEnd_1654065 : Nat := 4983230072969 + 3 ^ 40 * 1654065 * 2
def baseEnd_1654065 : Nat := 566220252519450797853733

theorem tailTrace_1654065 : CollatzResearch.WordTrace tailWord_1654065 prefixEnd_1654065 566220252519450797853733 := by
  unfold tailWord_1654065
  simp only [CollatzResearch.WordTrace]
  refine ⟨60328706752612471656787649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40219137835074981104525099 60328706752612471656787649)
  ·
    refine ⟨45246530064459353742590737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60328706752612471656787649 45246530064459353742590737)
    ·
      refine ⟨33934897548344515306943053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45246530064459353742590737 33934897548344515306943053)
      ·
        refine ⟨12725586580629193240103645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33934897548344515306943053 12725586580629193240103645)
        ·
          refine ⟨4772094967735947465038867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12725586580629193240103645 4772094967735947465038867)
          ·
            refine ⟨7158142451603921197558301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772094967735947465038867 7158142451603921197558301)
            ·
              refine ⟨2684303419351470449084363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7158142451603921197558301 2684303419351470449084363)
              ·
                refine ⟨4026455129027205673626545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684303419351470449084363 4026455129027205673626545)
                ·
                  refine ⟨3019841346770404255219909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4026455129027205673626545 3019841346770404255219909)
                  ·
                    refine ⟨566220252519450797853733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3019841346770404255219909 566220252519450797853733)
                    ·
                      rfl

theorem cell22_1654065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_1654065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654065 prefixEnd_1654065 := by exact prefixLift 1654065
  have htrace : WordTrace (prefixWord ++ tailWord_1654065) baseStart_1654065 baseEnd_1654065 := by
    simpa [prefixWord, tailWord_1654065, baseEnd_1654065] using wordTrace_append hprefix tailTrace_1654065
  have hstable : (prefixWord ++ tailWord_1654065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654065).length < 2 ^ (prefixWord ++ tailWord_1654065).sum := by decide
  have hdescent : baseEnd_1654065 < baseStart_1654065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654084 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1654084 : Nat := 118140960795 + 1654084 * 2 ^ 59
def prefixEnd_1654084 : Nat := 4983230072969 + 3 ^ 40 * 1654084 * 2
def baseEnd_1654084 : Nat := 566226756607741081628675

theorem tailTrace_1654084 : CollatzResearch.WordTrace tailWord_1654084 prefixEnd_1654084 566226756607741081628675 := by
  unfold tailWord_1654084
  simp only [CollatzResearch.WordTrace]
  refine ⟨30164699869771818950864653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40219599826362425267819537 30164699869771818950864653)
  ·
    refine ⟨11311762451164432106574245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30164699869771818950864653 11311762451164432106574245)
    ·
      refine ⟨2120955459593331019982671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11311762451164432106574245 2120955459593331019982671)
      ·
        refine ⟨3181433189389996529974007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120955459593331019982671 3181433189389996529974007)
        ·
          refine ⟨4772149784084994794961011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181433189389996529974007 4772149784084994794961011)
          ·
            refine ⟨7158224676127492192441517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772149784084994794961011 7158224676127492192441517)
            ·
              refine ⟨2684334253547809572165569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7158224676127492192441517 2684334253547809572165569)
              ·
                refine ⟨2013250690160857179124177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684334253547809572165569 2013250690160857179124177)
                ·
                  refine ⟨1509938017620642884343133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2013250690160857179124177 1509938017620642884343133)
                  ·
                    refine ⟨566226756607741081628675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1509938017620642884343133 566226756607741081628675)
                    ·
                      rfl

theorem cell22_1654084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1654084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654084 prefixEnd_1654084 := by exact prefixLift 1654084
  have htrace : WordTrace (prefixWord ++ tailWord_1654084) baseStart_1654084 baseEnd_1654084 := by
    simpa [prefixWord, tailWord_1654084, baseEnd_1654084] using wordTrace_append hprefix tailTrace_1654084
  have hstable : (prefixWord ++ tailWord_1654084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654084).length < 2 ^ (prefixWord ++ tailWord_1654084).sum := by decide
  have hdescent : baseEnd_1654084 < baseStart_1654084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654146 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1654146 : Nat := 118140960795 + 1654146 * 2 ^ 59
def prefixEnd_1654146 : Nat := 4983230072969 + 3 ^ 40 * 1654146 * 2
def baseEnd_1654146 : Nat := 566247980474793586578485

theorem tailTrace_1654146 : CollatzResearch.WordTrace tailWord_1654146 prefixEnd_1654146 566247980474793586578485 := by
  unfold tailWord_1654146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15082915266329755622621573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40221107376879348326990861 15082915266329755622621573)
  ·
    refine ⟨2828046612436829179241545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15082915266329755622621573 2828046612436829179241545)
    ·
      refine ⟨2121034959327621884431159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2828046612436829179241545 2121034959327621884431159)
      ·
        refine ⟨3181552438991432826646739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121034959327621884431159 3181552438991432826646739)
        ·
          refine ⟨4772328658487149239970109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181552438991432826646739 4772328658487149239970109)
          ·
            refine ⟨1789623246932680964988791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4772328658487149239970109 1789623246932680964988791)
            ·
              refine ⟨2684434870399021447483187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789623246932680964988791 2684434870399021447483187)
              ·
                refine ⟨4026652305598532171224781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684434870399021447483187 4026652305598532171224781)
                ·
                  refine ⟨1509994614599449564209293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4026652305598532171224781 1509994614599449564209293)
                  ·
                    refine ⟨566247980474793586578485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1509994614599449564209293 566247980474793586578485)
                    ·
                      rfl

theorem cell22_1654146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1654146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654146 prefixEnd_1654146 := by exact prefixLift 1654146
  have htrace : WordTrace (prefixWord ++ tailWord_1654146) baseStart_1654146 baseEnd_1654146 := by
    simpa [prefixWord, tailWord_1654146, baseEnd_1654146] using wordTrace_append hprefix tailTrace_1654146
  have hstable : (prefixWord ++ tailWord_1654146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654146).length < 2 ^ (prefixWord ++ tailWord_1654146).sum := by decide
  have hdescent : baseEnd_1654146 < baseStart_1654146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654200 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_1654200 : Nat := 118140960795 + 1654200 * 2 ^ 59
def prefixEnd_1654200 : Nat := 4983230072969 + 3 ^ 40 * 1654200 * 2
def baseEnd_1654200 : Nat := 566266465778355445728319

theorem tailTrace_1654200 : CollatzResearch.WordTrace tailWord_1654200 prefixEnd_1654200 566266465778355445728319 := by
  unfold tailWord_1654200
  simp only [CollatzResearch.WordTrace]
  refine ⟨30166815303561694856476027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40222420404748926475301369 30166815303561694856476027)
  ·
    refine ⟨45250222955342542284714041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30166815303561694856476027 45250222955342542284714041)
    ·
      refine ⟨33937667216506906713535531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45250222955342542284714041 33937667216506906713535531)
      ·
        refine ⟨50906500824760360070303297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33937667216506906713535531 50906500824760360070303297)
        ·
          refine ⟨38179875618570270052727473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50906500824760360070303297 38179875618570270052727473)
          ·
            refine ⟨28634906713927702539545605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38179875618570270052727473 28634906713927702539545605)
            ·
              refine ⟨5369045008861444226164801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28634906713927702539545605 5369045008861444226164801)
              ·
                refine ⟨4026783756646083169623601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5369045008861444226164801 4026783756646083169623601)
                ·
                  refine ⟨3020087817484562377217701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4026783756646083169623601 3020087817484562377217701)
                  ·
                    refine ⟨566266465778355445728319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020087817484562377217701 566266465778355445728319)
                    ·
                      rfl

theorem cell22_1654200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_1654200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654200 prefixEnd_1654200 := by exact prefixLift 1654200
  have htrace : WordTrace (prefixWord ++ tailWord_1654200) baseStart_1654200 baseEnd_1654200 := by
    simpa [prefixWord, tailWord_1654200, baseEnd_1654200] using wordTrace_append hprefix tailTrace_1654200
  have hstable : (prefixWord ++ tailWord_1654200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654200).length < 2 ^ (prefixWord ++ tailWord_1654200).sum := by decide
  have hdescent : baseEnd_1654200 < baseStart_1654200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654204 : List Nat := [2, 2, 2, 4, 2, 1, 1, 4, 4]
def baseStart_1654204 : Nat := 118140960795 + 1654204 * 2 ^ 59
def prefixEnd_1654204 : Nat := 4983230072969 + 3 ^ 40 * 1654204 * 2
def baseEnd_1654204 : Nat := 188755945020033589542769

theorem tailTrace_1654204 : CollatzResearch.WordTrace tailWord_1654204 prefixEnd_1654204 188755945020033589542769 := by
  unfold tailWord_1654204
  simp only [CollatzResearch.WordTrace]
  refine ⟨30166888249554449198048833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40222517666072598930731777 30166888249554449198048833)
  ·
    refine ⟨22625166187165836898536625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30166888249554449198048833 22625166187165836898536625)
    ·
      refine ⟨16968874640374377673902469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22625166187165836898536625 16968874640374377673902469)
      ·
        refine ⟨3181663995070195813856713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16968874640374377673902469 3181663995070195813856713)
        ·
          refine ⟨2386247996302646860392535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3181663995070195813856713 2386247996302646860392535)
          ·
            refine ⟨3579371994453970290588803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2386247996302646860392535 3579371994453970290588803)
            ·
              refine ⟨5369057991680955435883205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579371994453970290588803 5369057991680955435883205)
              ·
                refine ⟨1006698373440179144228101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5369057991680955435883205 1006698373440179144228101)
                ·
                  refine ⟨188755945020033589542769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006698373440179144228101 188755945020033589542769)
                  ·
                    rfl

theorem cell22_1654204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_1654204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654204 prefixEnd_1654204 := by exact prefixLift 1654204
  have htrace : WordTrace (prefixWord ++ tailWord_1654204) baseStart_1654204 baseEnd_1654204 := by
    simpa [prefixWord, tailWord_1654204, baseEnd_1654204] using wordTrace_append hprefix tailTrace_1654204
  have hstable : (prefixWord ++ tailWord_1654204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654204).length < 2 ^ (prefixWord ++ tailWord_1654204).sum := by decide
  have hdescent : baseEnd_1654204 < baseStart_1654204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654253 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_1654253 : Nat := 118140960795 + 1654253 * 2 ^ 59
def prefixEnd_1654253 : Nat := 4983230072969 + 3 ^ 40 * 1654253 * 2
def baseEnd_1654253 : Nat := 566284608761480974153157

theorem tailTrace_1654253 : CollatzResearch.WordTrace tailWord_1654253 prefixEnd_1654253 566284608761480974153157 := by
  unfold tailWord_1654253
  simp only [CollatzResearch.WordTrace]
  refine ⟨60335563675931379764631413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40223709117287586509754275 60335563675931379764631413)
  ·
    refine ⟨5656459094618566852934195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60335563675931379764631413 5656459094618566852934195)
    ·
      refine ⟨8484688641927850279401293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5656459094618566852934195 8484688641927850279401293)
      ·
        refine ⟨3181758240722943854775485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8484688641927850279401293 3181758240722943854775485)
        ·
          refine ⟨1193159340271103945540807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3181758240722943854775485 1193159340271103945540807)
          ·
            refine ⟨1789739010406655918311211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193159340271103945540807 1789739010406655918311211)
            ·
              refine ⟨2684608515609983877466817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789739010406655918311211 2684608515609983877466817)
              ·
                refine ⟨2013456386707487908100113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684608515609983877466817 2013456386707487908100113)
                ·
                  refine ⟨1510092290030615931075085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2013456386707487908100113 1510092290030615931075085)
                  ·
                    refine ⟨566284608761480974153157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510092290030615931075085 566284608761480974153157)
                    ·
                      rfl

theorem cell22_1654253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_1654253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654253 prefixEnd_1654253 := by exact prefixLift 1654253
  have htrace : WordTrace (prefixWord ++ tailWord_1654253) baseStart_1654253 baseEnd_1654253 := by
    simpa [prefixWord, tailWord_1654253, baseEnd_1654253] using wordTrace_append hprefix tailTrace_1654253
  have hstable : (prefixWord ++ tailWord_1654253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654253).length < 2 ^ (prefixWord ++ tailWord_1654253).sum := by decide
  have hdescent : baseEnd_1654253 < baseStart_1654253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654264 : List Nat := [2, 1, 2, 1, 1, 5, 2, 4, 1, 3]
def baseStart_1654264 : Nat := 118140960795 + 1654264 * 2 ^ 59
def prefixEnd_1654264 : Nat := 4983230072969 + 3 ^ 40 * 1654264 * 2
def baseEnd_1654264 : Nat := 566288374286280612128123

theorem tailTrace_1654264 : CollatzResearch.WordTrace tailWord_1654264 prefixEnd_1654264 566288374286280612128123 := by
  unfold tailWord_1654264
  simp only [CollatzResearch.WordTrace]
  refine ⟨30167982439445764321640923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40223976585927685762187897 30167982439445764321640923)
  ·
    refine ⟨45251973659168646482461385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30167982439445764321640923 45251973659168646482461385)
    ·
      refine ⟨33938980244376484861846039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45251973659168646482461385 33938980244376484861846039)
      ·
        refine ⟨50908470366564727292769059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33938980244376484861846039 50908470366564727292769059)
        ·
          refine ⟨76362705549847090939153589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50908470366564727292769059 76362705549847090939153589)
          ·
            refine ⟨7159003645298164775545649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76362705549847090939153589 7159003645298164775545649)
            ·
              refine ⟨5369252733973623581659237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7159003645298164775545649 5369252733973623581659237)
              ·
                refine ⟨1006734887620054421561107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5369252733973623581659237 1006734887620054421561107)
                ·
                  refine ⟨1510102331430081632341661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006734887620054421561107 1510102331430081632341661)
                  ·
                    refine ⟨566288374286280612128123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510102331430081632341661 566288374286280612128123)
                    ·
                      rfl

theorem cell22_1654264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_1654264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654264 prefixEnd_1654264 := by exact prefixLift 1654264
  have htrace : WordTrace (prefixWord ++ tailWord_1654264) baseStart_1654264 baseEnd_1654264 := by
    simpa [prefixWord, tailWord_1654264, baseEnd_1654264] using wordTrace_append hprefix tailTrace_1654264
  have hstable : (prefixWord ++ tailWord_1654264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654264).length < 2 ^ (prefixWord ++ tailWord_1654264).sum := by decide
  have hdescent : baseEnd_1654264 < baseStart_1654264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654337 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1654337 : Nat := 118140960795 + 1654337 * 2 ^ 59
def prefixEnd_1654337 : Nat := 4983230072969 + 3 ^ 40 * 1654337 * 2
def baseEnd_1654337 : Nat := 566313363678132755052899

theorem tailTrace_1654337 : CollatzResearch.WordTrace tailWord_1654337 prefixEnd_1654337 566313363678132755052899 := by
  unfold tailWord_1654337
  simp only [CollatzResearch.WordTrace]
  refine ⟨60338627407627062110689265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40225751605084708073792843 60338627407627062110689265)
  ·
    refine ⟨45253970555720296583016949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60338627407627062110689265 45253970555720296583016949)
    ·
      refine ⟨4242559739598777804657839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45253970555720296583016949 4242559739598777804657839)
      ·
        refine ⟨6363839609398166706986759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4242559739598777804657839 6363839609398166706986759)
        ·
          refine ⟨9545759414097250060480139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6363839609398166706986759 9545759414097250060480139)
          ·
            refine ⟨14318639121145875090720209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9545759414097250060480139 14318639121145875090720209)
            ·
              refine ⟨10738979340859406318040157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14318639121145875090720209 10738979340859406318040157)
              ·
                refine ⟨4027117252822277369265059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10738979340859406318040157 4027117252822277369265059)
                ·
                  refine ⟨6040675879233416053897589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027117252822277369265059 6040675879233416053897589)
                  ·
                    refine ⟨566313363678132755052899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6040675879233416053897589 566313363678132755052899)
                    ·
                      rfl

theorem cell22_1654337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1654337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654337 prefixEnd_1654337 := by exact prefixLift 1654337
  have htrace : WordTrace (prefixWord ++ tailWord_1654337) baseStart_1654337 baseEnd_1654337 := by
    simpa [prefixWord, tailWord_1654337, baseEnd_1654337] using wordTrace_append hprefix tailTrace_1654337
  have hstable : (prefixWord ++ tailWord_1654337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654337).length < 2 ^ (prefixWord ++ tailWord_1654337).sum := by decide
  have hdescent : baseEnd_1654337 < baseStart_1654337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654352 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_1654352 : Nat := 118140960795 + 1654352 * 2 ^ 59
def prefixEnd_1654352 : Nat := 4983230072969 + 3 ^ 40 * 1654352 * 2
def baseEnd_1654352 : Nat := 566318498484677715927853

theorem tailTrace_1654352 : CollatzResearch.WordTrace tailWord_1654352 prefixEnd_1654352 566318498484677715927853 := by
  unfold tailWord_1654352
  simp only [CollatzResearch.WordTrace]
  refine ⟨30169587251286359836242655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40226116335048479781656873 30169587251286359836242655)
  ·
    refine ⟨45254380876929539754363983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30169587251286359836242655 45254380876929539754363983)
    ·
      refine ⟨67881571315394309631545975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45254380876929539754363983 67881571315394309631545975)
      ·
        refine ⟨101822356973091464447318963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67881571315394309631545975 101822356973091464447318963)
        ·
          refine ⟨152733535459637196670978445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101822356973091464447318963 152733535459637196670978445)
          ·
            refine ⟨57275075797363948751616917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152733535459637196670978445 57275075797363948751616917)
            ·
              refine ⟨2684769178001435097732043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57275075797363948751616917 2684769178001435097732043)
              ·
                refine ⟨4027153767002152646598065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684769178001435097732043 4027153767002152646598065)
                ·
                  refine ⟨3020365325251614484948549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4027153767002152646598065 3020365325251614484948549)
                  ·
                    refine ⟨566318498484677715927853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020365325251614484948549 566318498484677715927853)
                    ·
                      rfl

theorem cell22_1654352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_1654352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654352 prefixEnd_1654352 := by exact prefixLift 1654352
  have htrace : WordTrace (prefixWord ++ tailWord_1654352) baseStart_1654352 baseEnd_1654352 := by
    simpa [prefixWord, tailWord_1654352, baseEnd_1654352] using wordTrace_append hprefix tailTrace_1654352
  have hstable : (prefixWord ++ tailWord_1654352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654352).length < 2 ^ (prefixWord ++ tailWord_1654352).sum := by decide
  have hdescent : baseEnd_1654352 < baseStart_1654352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654457 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 6]
def baseStart_1654457 : Nat := 118140960795 + 1654457 * 2 ^ 59
def prefixEnd_1654457 : Nat := 4983230072969 + 3 ^ 40 * 1654457 * 2
def baseEnd_1654457 : Nat := 188784814043497480684177

theorem tailTrace_1654457 : CollatzResearch.WordTrace tailWord_1654457 prefixEnd_1654457 188784814043497480684177 := by
  unfold tailWord_1654457
  simp only [CollatzResearch.WordTrace]
  refine ⟨60343004167192322605057625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40228669444794881736705083 60343004167192322605057625)
  ·
    refine ⟨45257253125394241953793219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60343004167192322605057625 45257253125394241953793219)
    ·
      refine ⟨67885879688091362930689829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45257253125394241953793219 67885879688091362930689829)
      ·
        refine ⟨12728602441517130549504343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67885879688091362930689829 12728602441517130549504343)
        ·
          refine ⟨19092903662275695824256515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12728602441517130549504343 19092903662275695824256515)
          ·
            refine ⟨28639355493413543736384773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19092903662275695824256515 28639355493413543736384773)
            ·
              refine ⟨5369879155015039450572145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28639355493413543736384773 5369879155015039450572145)
              ·
                refine ⟨4027409366261279587929109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5369879155015039450572145 4027409366261279587929109)
                ·
                  refine ⟨188784814043497480684177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4027409366261279587929109 188784814043497480684177)
                  ·
                    rfl

theorem cell22_1654457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_1654457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654457 prefixEnd_1654457 := by exact prefixLift 1654457
  have htrace : WordTrace (prefixWord ++ tailWord_1654457) baseStart_1654457 baseEnd_1654457 := by
    simpa [prefixWord, tailWord_1654457, baseEnd_1654457] using wordTrace_append hprefix tailTrace_1654457
  have hstable : (prefixWord ++ tailWord_1654457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654457).length < 2 ^ (prefixWord ++ tailWord_1654457).sum := by decide
  have hdescent : baseEnd_1654457 < baseStart_1654457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654472 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1654472 : Nat := 118140960795 + 1654472 * 2 ^ 59
def prefixEnd_1654472 : Nat := 4983230072969 + 3 ^ 40 * 1654472 * 2
def baseEnd_1654472 : Nat := 566359576937037402927485

theorem tailTrace_1654472 : CollatzResearch.WordTrace tailWord_1654472 prefixEnd_1654472 566359576937037402927485 := by
  unfold tailWord_1654472
  simp only [CollatzResearch.WordTrace]
  refine ⟨30171775631068990083426835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40229034174758653444569113 30171775631068990083426835)
  ·
    refine ⟨45257663446603485125140253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30171775631068990083426835 45257663446603485125140253)
    ·
      refine ⟨16971623792476306921927595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45257663446603485125140253 16971623792476306921927595)
      ·
        refine ⟨25457435688714460382891393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16971623792476306921927595 25457435688714460382891393)
        ·
          refine ⟨19093076766535845287168545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25457435688714460382891393 19093076766535845287168545)
          ·
            refine ⟨14319807574901883965376409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19093076766535845287168545 14319807574901883965376409)
            ·
              refine ⟨10739855681176412974032307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14319807574901883965376409 10739855681176412974032307)
              ·
                refine ⟨16109783521764619461048461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10739855681176412974032307 16109783521764619461048461)
                ·
                  refine ⟨6041168820661732297893173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16109783521764619461048461 6041168820661732297893173)
                  ·
                    refine ⟨566359576937037402927485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6041168820661732297893173 566359576937037402927485)
                    ·
                      rfl

theorem cell22_1654472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1654472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654472 prefixEnd_1654472 := by exact prefixLift 1654472
  have htrace : WordTrace (prefixWord ++ tailWord_1654472) baseStart_1654472 baseEnd_1654472 := by
    simpa [prefixWord, tailWord_1654472, baseEnd_1654472] using wordTrace_append hprefix tailTrace_1654472
  have hstable : (prefixWord ++ tailWord_1654472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654472).length < 2 ^ (prefixWord ++ tailWord_1654472).sum := by decide
  have hdescent : baseEnd_1654472 < baseStart_1654472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654489 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 4, 3]
def baseStart_1654489 : Nat := 118140960795 + 1654489 * 2 ^ 59
def prefixEnd_1654489 : Nat := 4983230072969 + 3 ^ 40 * 1654489 * 2
def baseEnd_1654489 : Nat := 566365396384455025252433

theorem tailTrace_1654489 : CollatzResearch.WordTrace tailWord_1654489 prefixEnd_1654489 566365396384455025252433 := by
  unfold tailWord_1654489
  simp only [CollatzResearch.WordTrace]
  refine ⟨60344171303076392070222521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40229447535384261380148347 60344171303076392070222521)
  ·
    refine ⟨45258128477307294052666891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60344171303076392070222521 45258128477307294052666891)
    ·
      refine ⟨67887192715960941079000337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45258128477307294052666891 67887192715960941079000337)
      ·
        refine ⟨50915394536970705809250253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67887192715960941079000337 50915394536970705809250253)
        ·
          refine ⟨19093272951364014678468845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50915394536970705809250253 19093272951364014678468845)
          ·
            refine ⟨7159977356761505504425817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19093272951364014678468845 7159977356761505504425817)
            ·
              refine ⟨5369983017571129128319363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7159977356761505504425817 5369983017571129128319363)
              ·
                refine ⟨8054974526356693692479045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369983017571129128319363 8054974526356693692479045)
                ·
                  refine ⟨1510307723691880067339821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8054974526356693692479045 1510307723691880067339821)
                  ·
                    refine ⟨566365396384455025252433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510307723691880067339821 566365396384455025252433)
                    ·
                      rfl

theorem cell22_1654489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_1654489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654489 prefixEnd_1654489 := by exact prefixLift 1654489
  have htrace : WordTrace (prefixWord ++ tailWord_1654489) baseStart_1654489 baseEnd_1654489 := by
    simpa [prefixWord, tailWord_1654489, baseEnd_1654489] using wordTrace_append hprefix tailTrace_1654489
  have hstable : (prefixWord ++ tailWord_1654489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654489).length < 2 ^ (prefixWord ++ tailWord_1654489).sum := by decide
  have hdescent : baseEnd_1654489 < baseStart_1654489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654598 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1654598 : Nat := 118140960795 + 1654598 * 2 ^ 59
def prefixEnd_1654598 : Nat := 4983230072969 + 3 ^ 40 * 1654598 * 2
def baseEnd_1654598 : Nat := 188800903104005024759033

theorem tailTrace_1654598 : CollatzResearch.WordTrace tailWord_1654598 prefixEnd_1654598 188800903104005024759033 := by
  unfold tailWord_1654598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885879589365046990185639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40232097906454335790626965 1885879589365046990185639)
  ·
    refine ⟨2828819384047570485278459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1885879589365046990185639 2828819384047570485278459)
    ·
      refine ⟨4243229076071355727917689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828819384047570485278459 4243229076071355727917689)
      ·
        refine ⟨3182421807053516795938267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4243229076071355727917689 3182421807053516795938267)
        ·
          refine ⟨4773632710580275193907401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182421807053516795938267 4773632710580275193907401)
          ·
            refine ⟨3580224532935206395430551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4773632710580275193907401 3580224532935206395430551)
            ·
              refine ⟨5370336799402809593145827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580224532935206395430551 5370336799402809593145827)
              ·
                refine ⟨8055505199104214389718741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370336799402809593145827 8055505199104214389718741)
                ·
                  refine ⟨188800903104005024759033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8055505199104214389718741 188800903104005024759033)
                  ·
                    rfl

theorem cell22_1654598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1654598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654598 prefixEnd_1654598 := by exact prefixLift 1654598
  have htrace : WordTrace (prefixWord ++ tailWord_1654598) baseStart_1654598 baseEnd_1654598 := by
    simpa [prefixWord, tailWord_1654598, baseEnd_1654598] using wordTrace_append hprefix tailTrace_1654598
  have hstable : (prefixWord ++ tailWord_1654598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654598).length < 2 ^ (prefixWord ++ tailWord_1654598).sum := by decide
  have hdescent : baseEnd_1654598 < baseStart_1654598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654607 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 11]
def baseStart_1654607 : Nat := 118140960795 + 1654607 * 2 ^ 59
def prefixEnd_1654607 : Nat := 4983230072969 + 3 ^ 40 * 1654607 * 2
def baseEnd_1654607 : Nat := 566405790195942050802071

theorem tailTrace_1654607 : CollatzResearch.WordTrace tailWord_1654607 prefixEnd_1654607 566405790195942050802071 := by
  unfold tailWord_1654607
  simp only [CollatzResearch.WordTrace]
  refine ⟨60348475116648898223018075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40232316744432598815345383 60348475116648898223018075)
  ·
    refine ⟨90522712674973347334527113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60348475116648898223018075 90522712674973347334527113)
    ·
      refine ⟨67892034506230010500895335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90522712674973347334527113 67892034506230010500895335)
      ·
        refine ⟨101838051759345015751343003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67892034506230010500895335 101838051759345015751343003)
        ·
          refine ⟨152757077639017523627014505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101838051759345015751343003 152757077639017523627014505)
          ·
            refine ⟨114567808229263142720260879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152757077639017523627014505 114567808229263142720260879)
            ·
              refine ⟨171851712343894714080391319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114567808229263142720260879 171851712343894714080391319)
              ·
                refine ⟨257777568515842071120586979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171851712343894714080391319 257777568515842071120586979)
                ·
                  refine ⟨386666352773763106680880469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257777568515842071120586979 386666352773763106680880469)
                  ·
                    refine ⟨566405790195942050802071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 386666352773763106680880469 566405790195942050802071)
                    ·
                      rfl

theorem cell22_1654607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_1654607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654607 prefixEnd_1654607 := by exact prefixLift 1654607
  have htrace : WordTrace (prefixWord ++ tailWord_1654607) baseStart_1654607 baseEnd_1654607 := by
    simpa [prefixWord, tailWord_1654607, baseEnd_1654607] using wordTrace_append hprefix tailTrace_1654607
  have hstable : (prefixWord ++ tailWord_1654607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654607).length < 2 ^ (prefixWord ++ tailWord_1654607).sum := by decide
  have hdescent : baseEnd_1654607 < baseStart_1654607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654609 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 6]
def baseStart_1654609 : Nat := 118140960795 + 1654609 * 2 ^ 59
def prefixEnd_1654609 : Nat := 4983230072969 + 3 ^ 40 * 1654609 * 2
def baseEnd_1654609 : Nat := 188802158278938237417355

theorem tailTrace_1654609 : CollatzResearch.WordTrace tailWord_1654609 prefixEnd_1654609 188802158278938237417355 := by
  unfold tailWord_1654609
  simp only [CollatzResearch.WordTrace]
  refine ⟨60348548062641652564590881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40232365375094435043060587 60348548062641652564590881)
  ·
    refine ⟨45261411046981239423443161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60348548062641652564590881 45261411046981239423443161)
    ·
      refine ⟨33946058285235929567582371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45261411046981239423443161 33946058285235929567582371)
      ·
        refine ⟨50919087427853894351373557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33946058285235929567582371 50919087427853894351373557)
        ·
          refine ⟨4773664446361302595441271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50919087427853894351373557 4773664446361302595441271)
          ·
            refine ⟨7160496669541953893161907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773664446361302595441271 7160496669541953893161907)
            ·
              refine ⟨10740745004312930839742861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160496669541953893161907 10740745004312930839742861)
              ·
                refine ⟨4027779376617349064903573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10740745004312930839742861 4027779376617349064903573)
                ·
                  refine ⟨188802158278938237417355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4027779376617349064903573 188802158278938237417355)
                  ·
                    rfl

theorem cell22_1654609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_1654609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654609 prefixEnd_1654609 := by exact prefixLift 1654609
  have htrace : WordTrace (prefixWord ++ tailWord_1654609) baseStart_1654609 baseEnd_1654609 := by
    simpa [prefixWord, tailWord_1654609, baseEnd_1654609] using wordTrace_append hprefix tailTrace_1654609
  have hstable : (prefixWord ++ tailWord_1654609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654609).length < 2 ^ (prefixWord ++ tailWord_1654609).sum := by decide
  have hdescent : baseEnd_1654609 < baseStart_1654609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654626 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1654626 : Nat := 118140960795 + 1654626 * 2 ^ 59
def prefixEnd_1654626 : Nat := 4983230072969 + 3 ^ 40 * 1654626 * 2
def baseEnd_1654626 : Nat := 188804098094744111525671

theorem tailTrace_1654626 : CollatzResearch.WordTrace tailWord_1654626 prefixEnd_1654626 188804098094744111525671 := by
  unfold tailWord_1654626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15087292025895016116989933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40232778735720042978639821 15087292025895016116989933)
  ·
    refine ⟨5657734509710631043871225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15087292025895016116989933 5657734509710631043871225)
    ·
      refine ⟨4243300882282973282903419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5657734509710631043871225 4243300882282973282903419)
      ·
        refine ⟨6364951323424459924355129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243300882282973282903419 6364951323424459924355129)
        ·
          refine ⟨4773713492568344943266347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6364951323424459924355129 4773713492568344943266347)
          ·
            refine ⟨7160570238852517414899521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773713492568344943266347 7160570238852517414899521)
            ·
              refine ⟨5370427679139388061174641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7160570238852517414899521 5370427679139388061174641)
              ·
                refine ⟨4027820759354541045880981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5370427679139388061174641 4027820759354541045880981)
                ·
                  refine ⟨188804098094744111525671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4027820759354541045880981 188804098094744111525671)
                  ·
                    rfl

theorem cell22_1654626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1654626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654626 prefixEnd_1654626 := by exact prefixLift 1654626
  have htrace : WordTrace (prefixWord ++ tailWord_1654626) baseStart_1654626 baseEnd_1654626 := by
    simpa [prefixWord, tailWord_1654626, baseEnd_1654626] using wordTrace_append hprefix tailTrace_1654626
  have hstable : (prefixWord ++ tailWord_1654626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654626).length < 2 ^ (prefixWord ++ tailWord_1654626).sum := by decide
  have hdescent : baseEnd_1654626 < baseStart_1654626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654628 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1654628 : Nat := 118140960795 + 1654628 * 2 ^ 59
def prefixEnd_1654628 : Nat := 4983230072969 + 3 ^ 40 * 1654628 * 2
def baseEnd_1654628 : Nat := 566412978925104996027007

theorem tailTrace_1654628 : CollatzResearch.WordTrace tailWord_1654628 prefixEnd_1654628 566412978925104996027007 := by
  unfold tailWord_1654628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30174620524786409404766269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40232827366381879206355025 30174620524786409404766269)
  ·
    refine ⟨11315482696794903526787351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30174620524786409404766269 11315482696794903526787351)
    ·
      refine ⟨16973224045192355290181027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315482696794903526787351 16973224045192355290181027)
      ·
        refine ⟨25459836067788532935271541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16973224045192355290181027 25459836067788532935271541)
        ·
          refine ⟨2386859631355174962681707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25459836067788532935271541 2386859631355174962681707)
          ·
            refine ⟨3580289447032762444022561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2386859631355174962681707 3580289447032762444022561)
            ·
              refine ⟨2685217085274571833016921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3580289447032762444022561 2685217085274571833016921)
              ·
                refine ⟨2013912813955928874762691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2685217085274571833016921 2013912813955928874762691)
                ·
                  refine ⟨3020869220933893312144037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013912813955928874762691 3020869220933893312144037)
                  ·
                    refine ⟨566412978925104996027007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020869220933893312144037 566412978925104996027007)
                    ·
                      rfl

theorem cell22_1654628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1654628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654628 prefixEnd_1654628 := by exact prefixLift 1654628
  have htrace : WordTrace (prefixWord ++ tailWord_1654628) baseStart_1654628 baseEnd_1654628 := by
    simpa [prefixWord, tailWord_1654628, baseEnd_1654628] using wordTrace_append hprefix tailTrace_1654628
  have hstable : (prefixWord ++ tailWord_1654628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654628).length < 2 ^ (prefixWord ++ tailWord_1654628).sum := by decide
  have hdescent : baseEnd_1654628 < baseStart_1654628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654703 : List Nat := [1, 1, 2, 1, 2, 2, 4, 5, 1, 3]
def baseStart_1654703 : Nat := 118140960795 + 1654703 * 2 ^ 59
def prefixEnd_1654703 : Nat := 4983230072969 + 3 ^ 40 * 1654703 * 2
def baseEnd_1654703 : Nat := 566438652957829800401777

theorem tailTrace_1654703 : CollatzResearch.WordTrace tailWord_1654703 prefixEnd_1654703 566438652957829800401777 := by
  unfold tailWord_1654703
  simp only [CollatzResearch.WordTrace]
  refine ⟨60351976524301106618512763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40234651016200737745675175 60351976524301106618512763)
  ·
    refine ⟨90527964786451659927769145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60351976524301106618512763 90527964786451659927769145)
    ·
      refine ⟨67895973589838744945826859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90527964786451659927769145 67895973589838744945826859)
      ·
        refine ⟨101843960384758117418740289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67895973589838744945826859 101843960384758117418740289)
        ·
          refine ⟨76382970288568588064055217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101843960384758117418740289 76382970288568588064055217)
          ·
            refine ⟨57287227716426441048041413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76382970288568588064055217 57287227716426441048041413)
            ·
              refine ⟨10741355196829957696507765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57287227716426441048041413 10741355196829957696507765)
              ·
                refine ⟨1007002049702808534047603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10741355196829957696507765 1007002049702808534047603)
                ·
                  refine ⟨1510503074554212801071405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007002049702808534047603 1510503074554212801071405)
                  ·
                    refine ⟨566438652957829800401777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510503074554212801071405 566438652957829800401777)
                    ·
                      rfl

theorem cell22_1654703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 1, 3].length) (baseStart_1654703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654703 prefixEnd_1654703 := by exact prefixLift 1654703
  have htrace : WordTrace (prefixWord ++ tailWord_1654703) baseStart_1654703 baseEnd_1654703 := by
    simpa [prefixWord, tailWord_1654703, baseEnd_1654703] using wordTrace_append hprefix tailTrace_1654703
  have hstable : (prefixWord ++ tailWord_1654703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654703).length < 2 ^ (prefixWord ++ tailWord_1654703).sum := by decide
  have hdescent : baseEnd_1654703 < baseStart_1654703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654754 : List Nat := [3, 3, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1654754 : Nat := 118140960795 + 1654754 * 2 ^ 59
def prefixEnd_1654754 : Nat := 4983230072969 + 3 ^ 40 * 1654754 * 2
def baseEnd_1654754 : Nat := 566456111300082667376621

theorem tailTrace_1654754 : CollatzResearch.WordTrace tailWord_1654754 prefixEnd_1654754 566456111300082667376621 := by
  unfold tailWord_1654754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15088459161779085582154829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40235891098077561552412877 15088459161779085582154829)
  ·
    refine ⟨5658172185667157093308061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15088459161779085582154829 5658172185667157093308061)
    ·
      refine ⟨2121814569625183909990523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5658172185667157093308061 2121814569625183909990523)
      ·
        refine ⟨3182721854437775864985785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121814569625183909990523 3182721854437775864985785)
        ·
          refine ⟨2387041390828331898739339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182721854437775864985785 2387041390828331898739339)
          ·
            refine ⟨3580562086242497848109009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387041390828331898739339 3580562086242497848109009)
            ·
              refine ⟨2685421564681873386081757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3580562086242497848109009 2685421564681873386081757)
              ·
                refine ⟨1007033086755702519780659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2685421564681873386081757 1007033086755702519780659)
                ·
                  refine ⟨1510549630133553779670989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007033086755702519780659 1510549630133553779670989)
                  ·
                    refine ⟨566456111300082667376621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510549630133553779670989 566456111300082667376621)
                    ·
                      rfl

theorem cell22_1654754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1654754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654754 prefixEnd_1654754 := by exact prefixLift 1654754
  have htrace : WordTrace (prefixWord ++ tailWord_1654754) baseStart_1654754 baseEnd_1654754 := by
    simpa [prefixWord, tailWord_1654754, baseEnd_1654754] using wordTrace_append hprefix tailTrace_1654754
  have hstable : (prefixWord ++ tailWord_1654754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654754).length < 2 ^ (prefixWord ++ tailWord_1654754).sum := by decide
  have hdescent : baseEnd_1654754 < baseStart_1654754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654791 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1654791 : Nat := 118140960795 + 1654791 * 2 ^ 59
def prefixEnd_1654791 : Nat := 4983230072969 + 3 ^ 40 * 1654791 * 2
def baseEnd_1654791 : Nat := 566468777156226904201507

theorem tailTrace_1654791 : CollatzResearch.WordTrace tailWord_1654791 prefixEnd_1654791 566468777156226904201507 := by
  unfold tailWord_1654791
  simp only [CollatzResearch.WordTrace]
  refine ⟨60355186147982297647716227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40236790765321531765144151 60355186147982297647716227)
  ·
    refine ⟨90532779221973446471574341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60355186147982297647716227 90532779221973446471574341)
    ·
      refine ⟨16974896104120021213420189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90532779221973446471574341 16974896104120021213420189)
      ·
        refine ⟨6365586039045007955032571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16974896104120021213420189 6365586039045007955032571)
        ·
          refine ⟨9548379058567511932548857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365586039045007955032571 9548379058567511932548857)
          ·
            refine ⟨7161284293925633949411643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9548379058567511932548857 7161284293925633949411643)
            ·
              refine ⟨10741926440888450924117465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161284293925633949411643 10741926440888450924117465)
              ·
                refine ⟨8056444830666338193088099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10741926440888450924117465 8056444830666338193088099)
                ·
                  refine ⟨12084667245999507289632149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8056444830666338193088099 12084667245999507289632149)
                  ·
                    refine ⟨566468777156226904201507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12084667245999507289632149 566468777156226904201507)
                    ·
                      rfl

theorem cell22_1654791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1654791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654791 prefixEnd_1654791 := by exact prefixLift 1654791
  have htrace : WordTrace (prefixWord ++ tailWord_1654791) baseStart_1654791 baseEnd_1654791 := by
    simpa [prefixWord, tailWord_1654791, baseEnd_1654791] using wordTrace_append hprefix tailTrace_1654791
  have hstable : (prefixWord ++ tailWord_1654791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654791).length < 2 ^ (prefixWord ++ tailWord_1654791).sum := by decide
  have hdescent : baseEnd_1654791 < baseStart_1654791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654898 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_1654898 : Nat := 118140960795 + 1654898 * 2 ^ 59
def prefixEnd_1654898 : Nat := 4983230072969 + 3 ^ 40 * 1654898 * 2
def baseEnd_1654898 : Nat := 566505405442914291776179

theorem tailTrace_1654898 : CollatzResearch.WordTrace tailWord_1654898 prefixEnd_1654898 566505405442914291776179 := by
  unfold tailWord_1654898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089772189648663730465337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40239392505729769947907565 15089772189648663730465337)
  ·
    refine ⟨11317329142236497797849003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15089772189648663730465337 11317329142236497797849003)
    ·
      refine ⟨16975993713354746696773505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11317329142236497797849003 16975993713354746696773505)
      ·
        refine ⟨12731995285016060022580129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16975993713354746696773505 12731995285016060022580129)
        ·
          refine ⟨9548996463762045016935097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12731995285016060022580129 9548996463762045016935097)
          ·
            refine ⟨7161747347821533762701323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9548996463762045016935097 7161747347821533762701323)
            ·
              refine ⟨10742621021732300644051985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161747347821533762701323 10742621021732300644051985)
              ·
                refine ⟨8056965766299225483038989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10742621021732300644051985 8056965766299225483038989)
                ·
                  refine ⟨3021362162362209556139621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8056965766299225483038989 3021362162362209556139621)
                  ·
                    refine ⟨566505405442914291776179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3021362162362209556139621 566505405442914291776179)
                    ·
                      rfl

theorem cell22_1654898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_1654898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654898 prefixEnd_1654898 := by exact prefixLift 1654898
  have htrace : WordTrace (prefixWord ++ tailWord_1654898) baseStart_1654898 baseEnd_1654898 := by
    simpa [prefixWord, tailWord_1654898, baseEnd_1654898] using wordTrace_append hprefix tailTrace_1654898
  have hstable : (prefixWord ++ tailWord_1654898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654898).length < 2 ^ (prefixWord ++ tailWord_1654898).sum := by decide
  have hdescent : baseEnd_1654898 < baseStart_1654898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654928 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 4, 3]
def baseStart_1654928 : Nat := 118140960795 + 1654928 * 2 ^ 59
def prefixEnd_1654928 : Nat := 4983230072969 + 3 ^ 40 * 1654928 * 2
def baseEnd_1654928 : Nat := 566515675056004213526087

theorem tailTrace_1654928 : CollatzResearch.WordTrace tailWord_1654928 prefixEnd_1654928 566515675056004213526087 := by
  unfold tailWord_1654928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30180091474242985022726719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40240121965657313363635625 30180091474242985022726719)
  ·
    refine ⟨45270137211364477534090079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30180091474242985022726719 45270137211364477534090079)
    ·
      refine ⟨67905205817046716301135119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45270137211364477534090079 67905205817046716301135119)
      ·
        refine ⟨101857808725570074451702679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67905205817046716301135119 101857808725570074451702679)
        ·
          refine ⟨152786713088355111677554019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101857808725570074451702679 152786713088355111677554019)
          ·
            refine ⟨229180069632532667516331029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152786713088355111677554019 229180069632532667516331029)
            ·
              refine ⟨10742815764024968789828017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229180069632532667516331029 10742815764024968789828017)
              ·
                refine ⟨8057111823018726592371013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10742815764024968789828017 8057111823018726592371013)
                ·
                  refine ⟨1510708466816011236069565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8057111823018726592371013 1510708466816011236069565)
                  ·
                    refine ⟨566515675056004213526087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510708466816011236069565 566515675056004213526087)
                    ·
                      rfl

theorem cell22_1654928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_1654928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654928 prefixEnd_1654928 := by exact prefixLift 1654928
  have htrace : WordTrace (prefixWord ++ tailWord_1654928) baseStart_1654928 baseEnd_1654928 := by
    simpa [prefixWord, tailWord_1654928, baseEnd_1654928] using wordTrace_append hprefix tailTrace_1654928
  have hstable : (prefixWord ++ tailWord_1654928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654928).length < 2 ^ (prefixWord ++ tailWord_1654928).sum := by decide
  have hdescent : baseEnd_1654928 < baseStart_1654928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654945 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 4, 3]
def baseStart_1654945 : Nat := 118140960795 + 1654945 * 2 ^ 59
def prefixEnd_1654945 : Nat := 4983230072969 + 3 ^ 40 * 1654945 * 2
def baseEnd_1654945 : Nat := 566521494503421835851035

theorem tailTrace_1654945 : CollatzResearch.WordTrace tailWord_1654945 prefixEnd_1654945 566521494503421835851035 := by
  unfold tailWord_1654945
  simp only [CollatzResearch.WordTrace]
  refine ⟨60360802989424381948822289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40240535326282921299214859 60360802989424381948822289)
  ·
    refine ⟨45270602242068286461616717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60360802989424381948822289 45270602242068286461616717)
    ·
      refine ⟨16976475840775607423106269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45270602242068286461616717 16976475840775607423106269)
      ·
        refine ⟨6366178440290852783664851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16976475840775607423106269 6366178440290852783664851)
        ·
          refine ⟨9549267660436279175497277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6366178440290852783664851 9549267660436279175497277)
          ·
            refine ⟨3580975372663604690811479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9549267660436279175497277 3580975372663604690811479)
            ·
              refine ⟨5371463058995407036217219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580975372663604690811479 5371463058995407036217219)
              ·
                refine ⟨8057194588493110554325829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371463058995407036217219 8057194588493110554325829)
                ·
                  refine ⟨1510723985342458228936093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8057194588493110554325829 1510723985342458228936093)
                  ·
                    refine ⟨566521494503421835851035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510723985342458228936093 566521494503421835851035)
                    ·
                      rfl

theorem cell22_1654945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_1654945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654945 prefixEnd_1654945 := by exact prefixLift 1654945
  have htrace : WordTrace (prefixWord ++ tailWord_1654945) baseStart_1654945 baseEnd_1654945 := by
    simpa [prefixWord, tailWord_1654945, baseEnd_1654945] using wordTrace_append hprefix tailTrace_1654945
  have hstable : (prefixWord ++ tailWord_1654945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654945).length < 2 ^ (prefixWord ++ tailWord_1654945).sum := by decide
  have hdescent : baseEnd_1654945 < baseStart_1654945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654962 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_1654962 : Nat := 118140960795 + 1654962 * 2 ^ 59
def prefixEnd_1654962 : Nat := 4983230072969 + 3 ^ 40 * 1654962 * 2
def baseEnd_1654962 : Nat := 566527313950839458175983

theorem tailTrace_1654962 : CollatzResearch.WordTrace tailWord_1654962 prefixEnd_1654962 566527313950839458175983 := by
  unfold tailWord_1654962
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090355757590698463047785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40240948686908529234794093 15090355757590698463047785)
  ·
    refine ⟨11317766818193023847285839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15090355757590698463047785 11317766818193023847285839)
    ·
      refine ⟨16976650227289535770928759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11317766818193023847285839 16976650227289535770928759)
      ·
        refine ⟨25464975340934303656393139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16976650227289535770928759 25464975340934303656393139)
        ·
          refine ⟨38197463011401455484589709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25464975340934303656393139 38197463011401455484589709)
          ·
            refine ⟨14324048629275545806721141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38197463011401455484589709 14324048629275545806721141)
            ·
              refine ⟨1342879558994582419380107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14324048629275545806721141 1342879558994582419380107)
              ·
                refine ⟨2014319338491873629070161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342879558994582419380107 2014319338491873629070161)
                ·
                  refine ⟨1510739503868905221802621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2014319338491873629070161 1510739503868905221802621)
                  ·
                    refine ⟨566527313950839458175983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510739503868905221802621 566527313950839458175983)
                    ·
                      rfl

theorem cell22_1654962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_1654962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1654962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1654962 prefixEnd_1654962 := by exact prefixLift 1654962
  have htrace : WordTrace (prefixWord ++ tailWord_1654962) baseStart_1654962 baseEnd_1654962 := by
    simpa [prefixWord, tailWord_1654962, baseEnd_1654962] using wordTrace_append hprefix tailTrace_1654962
  have hstable : (prefixWord ++ tailWord_1654962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654962).length < 2 ^ (prefixWord ++ tailWord_1654962).sum := by decide
  have hdescent : baseEnd_1654962 < baseStart_1654962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655018 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1655018 : Nat := 118140960795 + 1655018 * 2 ^ 59
def prefixEnd_1655018 : Nat := 4983230072969 + 3 ^ 40 * 1655018 * 2
def baseEnd_1655018 : Nat := 566546483895273978775811

theorem tailTrace_1655018 : CollatzResearch.WordTrace tailWord_1655018 prefixEnd_1655018 566546483895273978775811 := by
  unfold tailWord_1655018
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090866379539978854057427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40242310345439943610819805 15090866379539978854057427)
  ·
    refine ⟨22636299569309968281086141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15090866379539978854057427 22636299569309968281086141)
    ·
      refine ⟨8488612338491238105407303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22636299569309968281086141 8488612338491238105407303)
      ·
        refine ⟨12732918507736857158110955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8488612338491238105407303 12732918507736857158110955)
        ·
          refine ⟨19099377761605285737166433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12732918507736857158110955 19099377761605285737166433)
          ·
            refine ⟨14324533321203964302874825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19099377761605285737166433 14324533321203964302874825)
            ·
              refine ⟨10743399990902973227156119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14324533321203964302874825 10743399990902973227156119)
              ·
                refine ⟨16115099986354459840734179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10743399990902973227156119 16115099986354459840734179)
                ·
                  refine ⟨24172649979531689761101269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16115099986354459840734179 24172649979531689761101269)
                  ·
                    refine ⟨566546483895273978775811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24172649979531689761101269 566546483895273978775811)
                    ·
                      rfl

theorem cell22_1655018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1655018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655018 prefixEnd_1655018 := by exact prefixLift 1655018
  have htrace : WordTrace (prefixWord ++ tailWord_1655018) baseStart_1655018 baseEnd_1655018 := by
    simpa [prefixWord, tailWord_1655018, baseEnd_1655018] using wordTrace_append hprefix tailTrace_1655018
  have hstable : (prefixWord ++ tailWord_1655018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655018).length < 2 ^ (prefixWord ++ tailWord_1655018).sum := by decide
  have hdescent : baseEnd_1655018 < baseStart_1655018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655050 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_1655050 : Nat := 118140960795 + 1655050 * 2 ^ 59
def prefixEnd_1655050 : Nat := 4983230072969 + 3 ^ 40 * 1655050 * 2
def baseEnd_1655050 : Nat := 566557438149236561975713

theorem tailTrace_1655050 : CollatzResearch.WordTrace tailWord_1655050 prefixEnd_1655050 566557438149236561975713 := by
  unfold tailWord_1655050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15091158163510996220348651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40243088436029323254263069 15091158163510996220348651)
  ·
    refine ⟨22636737245266494330522977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15091158163510996220348651 22636737245266494330522977)
    ·
      refine ⟨16977552933949870747892233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22636737245266494330522977 16977552933949870747892233)
      ·
        refine ⟨12733164700462403060919175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16977552933949870747892233 12733164700462403060919175)
        ·
          refine ⟨19099747050693604591378763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12733164700462403060919175 19099747050693604591378763)
          ·
            refine ⟨28649620576040406887068145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19099747050693604591378763 28649620576040406887068145)
            ·
              refine ⟨21487215432030305165301109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28649620576040406887068145 21487215432030305165301109)
              ·
                refine ⟨2014426446752841109246979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21487215432030305165301109 2014426446752841109246979)
                ·
                  refine ⟨3021639670129261663870469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014426446752841109246979 3021639670129261663870469)
                  ·
                    refine ⟨566557438149236561975713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3021639670129261663870469 566557438149236561975713)
                    ·
                      rfl

theorem cell22_1655050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_1655050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655050 prefixEnd_1655050 := by exact prefixLift 1655050
  have htrace : WordTrace (prefixWord ++ tailWord_1655050) baseStart_1655050 baseEnd_1655050 := by
    simpa [prefixWord, tailWord_1655050, baseEnd_1655050] using wordTrace_append hprefix tailTrace_1655050
  have hstable : (prefixWord ++ tailWord_1655050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655050).length < 2 ^ (prefixWord ++ tailWord_1655050).sum := by decide
  have hdescent : baseEnd_1655050 < baseStart_1655050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655082 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_1655082 : Nat := 118140960795 + 1655082 * 2 ^ 59
def prefixEnd_1655082 : Nat := 4983230072969 + 3 ^ 40 * 1655082 * 2
def baseEnd_1655082 : Nat := 188856130801066381725205

theorem tailTrace_1655082 : CollatzResearch.WordTrace tailWord_1655082 prefixEnd_1655082 188856130801066381725205 := by
  unfold tailWord_1655082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15091449947482013586639875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40243866526618702897706333 15091449947482013586639875)
  ·
    refine ⟨22637174921223020379959813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15091449947482013586639875 22637174921223020379959813)
    ·
      refine ⟨4244470297729316321242465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22637174921223020379959813 4244470297729316321242465)
      ·
        refine ⟨3183352723296987240931849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4244470297729316321242465 3183352723296987240931849)
        ·
          refine ⟨2387514542472740430698887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3183352723296987240931849 2387514542472740430698887)
          ·
            refine ⟨3581271813709110646048331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387514542472740430698887 3581271813709110646048331)
            ·
              refine ⟨5371907720563665969072497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3581271813709110646048331 5371907720563665969072497)
              ·
                refine ⟨4028930790422749476804373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5371907720563665969072497 4028930790422749476804373)
                ·
                  refine ⟨188856130801066381725205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4028930790422749476804373 188856130801066381725205)
                  ·
                    rfl

theorem cell22_1655082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_1655082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655082 prefixEnd_1655082 := by exact prefixLift 1655082
  have htrace : WordTrace (prefixWord ++ tailWord_1655082) baseStart_1655082 baseEnd_1655082 := by
    simpa [prefixWord, tailWord_1655082, baseEnd_1655082] using wordTrace_append hprefix tailTrace_1655082
  have hstable : (prefixWord ++ tailWord_1655082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655082).length < 2 ^ (prefixWord ++ tailWord_1655082).sum := by decide
  have hdescent : baseEnd_1655082 < baseStart_1655082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655123 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 2, 6]
def baseStart_1655123 : Nat := 118140960795 + 1655123 * 2 ^ 59
def prefixEnd_1655123 : Nat := 4983230072969 + 3 ^ 40 * 1655123 * 2
def baseEnd_1655123 : Nat := 566582427541088704900489

theorem tailTrace_1655123 : CollatzResearch.WordTrace tailWord_1655123 prefixEnd_1655123 566582427541088704900489 := by
  unfold tailWord_1655123
  simp only [CollatzResearch.WordTrace]
  refine ⟨60367295182779518348802023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40244863455186345565868015 60367295182779518348802023)
  ·
    refine ⟨90550942774169277523203035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60367295182779518348802023 90550942774169277523203035)
    ·
      refine ⟨135826414161253916284804553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90550942774169277523203035 135826414161253916284804553)
      ·
        refine ⟨101869810620940437213603415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135826414161253916284804553 101869810620940437213603415)
        ·
          refine ⟨152804715931410655820405123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101869810620940437213603415 152804715931410655820405123)
          ·
            refine ⟨229207073897115983730607685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152804715931410655820405123 229207073897115983730607685)
            ·
              refine ⟨42976326355709246949488941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229207073897115983730607685 42976326355709246949488941)
              ·
                refine ⟨16116122383390967606058353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42976326355709246949488941 16116122383390967606058353)
                ·
                  refine ⟨12087091787543225704543765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16116122383390967606058353 12087091787543225704543765)
                  ·
                    refine ⟨566582427541088704900489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12087091787543225704543765 566582427541088704900489)
                    ·
                      rfl

theorem cell22_1655123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_1655123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655123 prefixEnd_1655123 := by exact prefixLift 1655123
  have htrace : WordTrace (prefixWord ++ tailWord_1655123) baseStart_1655123 baseEnd_1655123 := by
    simpa [prefixWord, tailWord_1655123, baseEnd_1655123] using wordTrace_append hprefix tailTrace_1655123
  have hstable : (prefixWord ++ tailWord_1655123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655123).length < 2 ^ (prefixWord ++ tailWord_1655123).sum := by decide
  have hdescent : baseEnd_1655123 < baseStart_1655123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655176 : List Nat := [2, 1, 3, 3, 1, 1, 5, 2, 1, 3]
def baseStart_1655176 : Nat := 118140960795 + 1655176 * 2 ^ 59
def prefixEnd_1655176 : Nat := 4983230072969 + 3 ^ 40 * 1655176 * 2
def baseEnd_1655176 : Nat := 566600570524214233325327

theorem tailTrace_1655176 : CollatzResearch.WordTrace tailWord_1655176 prefixEnd_1655176 566600570524214233325327 := by
  unfold tailWord_1655176
  simp only [CollatzResearch.WordTrace]
  refine ⟨30184614125793754200240691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40246152167725005600320921 30184614125793754200240691)
  ·
    refine ⟨45276921188690631300361037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30184614125793754200240691 45276921188690631300361037)
    ·
      refine ⟨16978845445758986737635389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45276921188690631300361037 16978845445758986737635389)
      ·
        refine ⟨6367067042159620026613271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16978845445758986737635389 6367067042159620026613271)
        ·
          refine ⟨9550600563239430039919907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367067042159620026613271 9550600563239430039919907)
          ·
            refine ⟨14325900844859145059879861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9550600563239430039919907 14325900844859145059879861)
            ·
              refine ⟨1343053204205544849363737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14325900844859145059879861 1343053204205544849363737)
              ·
                refine ⟨1007289903154158637022803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1343053204205544849363737 1007289903154158637022803)
                ·
                  refine ⟨1510934854731237955534205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007289903154158637022803 1510934854731237955534205)
                  ·
                    refine ⟨566600570524214233325327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1510934854731237955534205 566600570524214233325327)
                    ·
                      rfl

theorem cell22_1655176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_1655176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655176 prefixEnd_1655176 := by exact prefixLift 1655176
  have htrace : WordTrace (prefixWord ++ tailWord_1655176) baseStart_1655176 baseEnd_1655176 := by
    simpa [prefixWord, tailWord_1655176, baseEnd_1655176] using wordTrace_append hprefix tailTrace_1655176
  have hstable : (prefixWord ++ tailWord_1655176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655176).length < 2 ^ (prefixWord ++ tailWord_1655176).sum := by decide
  have hdescent : baseEnd_1655176 < baseStart_1655176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655202 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1655202 : Nat := 118140960795 + 1655202 * 2 ^ 59
def prefixEnd_1655202 : Nat := 4983230072969 + 3 ^ 40 * 1655202 * 2
def baseEnd_1655202 : Nat := 566609470855558832175247

theorem tailTrace_1655202 : CollatzResearch.WordTrace tailWord_1655202 prefixEnd_1655202 566609470855558832175247 := by
  unfold tailWord_1655202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092544137373328710231965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40246784366328876560618573 15092544137373328710231965)
  ·
    refine ⟨5659704051514998266336987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15092544137373328710231965 5659704051514998266336987)
    ·
      refine ⟨8489556077272497399505481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5659704051514998266336987 8489556077272497399505481)
      ·
        refine ⟨6367167057954373049629111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8489556077272497399505481 6367167057954373049629111)
        ·
          refine ⟨9550750586931559574443667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367167057954373049629111 9550750586931559574443667)
          ·
            refine ⟨14326125880397339361665501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9550750586931559574443667 14326125880397339361665501)
            ·
              refine ⟨5372297205149002260624563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14326125880397339361665501 5372297205149002260624563)
              ·
                refine ⟨8058445807723503390936845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5372297205149002260624563 8058445807723503390936845)
                ·
                  refine ⟨3021917177896313771601317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8058445807723503390936845 3021917177896313771601317)
                  ·
                    refine ⟨566609470855558832175247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3021917177896313771601317 566609470855558832175247)
                    ·
                      rfl

theorem cell22_1655202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1655202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655202 prefixEnd_1655202 := by exact prefixLift 1655202
  have htrace : WordTrace (prefixWord ++ tailWord_1655202) baseStart_1655202 baseEnd_1655202 := by
    simpa [prefixWord, tailWord_1655202, baseEnd_1655202] using wordTrace_append hprefix tailTrace_1655202
  have hstable : (prefixWord ++ tailWord_1655202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655202).length < 2 ^ (prefixWord ++ tailWord_1655202).sum := by decide
  have hdescent : baseEnd_1655202 < baseStart_1655202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655305 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_1655305 : Nat := 118140960795 + 1655305 * 2 ^ 59
def prefixEnd_1655305 : Nat := 4983230072969 + 3 ^ 40 * 1655305 * 2
def baseEnd_1655305 : Nat := 566644729860500896849931

theorem tailTrace_1655305 : CollatzResearch.WordTrace tailWord_1655305 prefixEnd_1655305 566644729860500896849931 := by
  unfold tailWord_1655305
  simp only [CollatzResearch.WordTrace]
  refine ⟨60373933268120163431927369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40249288845413442287951579 60373933268120163431927369)
  ·
    refine ⟨45280449951090122573945527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60373933268120163431927369 45280449951090122573945527)
    ·
      refine ⟨67920674926635183860918291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45280449951090122573945527 67920674926635183860918291)
      ·
        refine ⟨101881012389952775791377437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67920674926635183860918291 101881012389952775791377437)
        ·
          refine ⟨38205379646232290921766539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101881012389952775791377437 38205379646232290921766539)
          ·
            refine ⟨57308069469348436382649809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38205379646232290921766539 57308069469348436382649809)
            ·
              refine ⟨42981052102011327286987357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57308069469348436382649809 42981052102011327286987357)
              ·
                refine ⟨16117894538254247732620259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42981052102011327286987357 16117894538254247732620259)
                ·
                  refine ⟨24176841807381371598930389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16117894538254247732620259 24176841807381371598930389)
                  ·
                    refine ⟨566644729860500896849931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24176841807381371598930389 566644729860500896849931)
                    ·
                      rfl

theorem cell22_1655305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_1655305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655305 prefixEnd_1655305 := by exact prefixLift 1655305
  have htrace : WordTrace (prefixWord ++ tailWord_1655305) baseStart_1655305 baseEnd_1655305 := by
    simpa [prefixWord, tailWord_1655305, baseEnd_1655305] using wordTrace_append hprefix tailTrace_1655305
  have hstable : (prefixWord ++ tailWord_1655305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655305).length < 2 ^ (prefixWord ++ tailWord_1655305).sum := by decide
  have hdescent : baseEnd_1655305 < baseStart_1655305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655388 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1655388 : Nat := 118140960795 + 1655388 * 2 ^ 59
def prefixEnd_1655388 : Nat := 4983230072969 + 3 ^ 40 * 1655388 * 2
def baseEnd_1655388 : Nat := 566673142456716347024677

theorem tailTrace_1655388 : CollatzResearch.WordTrace tailWord_1655388 prefixEnd_1655388 566673142456716347024677 := by
  unfold tailWord_1655388
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188480263409734303599409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40251307017879645738132545 30188480263409734303599409)
  ·
    refine ⟨22641360197557300727699557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30188480263409734303599409 22641360197557300727699557)
    ·
      refine ⟨4245255037041993886443667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22641360197557300727699557 4245255037041993886443667)
      ·
        refine ⟨6367882555562990829665501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4245255037041993886443667 6367882555562990829665501)
        ·
          refine ⟨2387955958336121561124563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6367882555562990829665501 2387955958336121561124563)
          ·
            refine ⟨3581933937504182341686845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387955958336121561124563 3581933937504182341686845)
            ·
              refine ⟨1343225226564068378132567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3581933937504182341686845 1343225226564068378132567)
              ·
                refine ⟨2014837839846102567198851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343225226564068378132567 2014837839846102567198851)
                ·
                  refine ⟨3022256759769153850798277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014837839846102567198851 3022256759769153850798277)
                  ·
                    refine ⟨566673142456716347024677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3022256759769153850798277 566673142456716347024677)
                    ·
                      rfl

theorem cell22_1655388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1655388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655388 prefixEnd_1655388 := by exact prefixLift 1655388
  have htrace : WordTrace (prefixWord ++ tailWord_1655388) baseStart_1655388 baseEnd_1655388 := by
    simpa [prefixWord, tailWord_1655388, baseEnd_1655388] using wordTrace_append hprefix tailTrace_1655388
  have hstable : (prefixWord ++ tailWord_1655388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655388).length < 2 ^ (prefixWord ++ tailWord_1655388).sum := by decide
  have hdescent : baseEnd_1655388 < baseStart_1655388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655397 : List Nat := [1, 3, 1, 3, 4, 10]
def baseStart_1655397 : Nat := 118140960795 + 1655397 * 2 ^ 59
def prefixEnd_1655397 : Nat := 4983230072969 + 3 ^ 40 * 1655397 * 2
def baseEnd_1655397 : Nat := 6996002757291892883329

theorem tailTrace_1655397 : CollatzResearch.WordTrace tailWord_1655397 prefixEnd_1655397 6996002757291892883329 := by
  unfold tailWord_1655397
  simp only [CollatzResearch.WordTrace]
  refine ⟨60377288783786863144276445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40251525855857908762850963 60377288783786863144276445)
  ·
    refine ⟨22641483293920073679103667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60377288783786863144276445 22641483293920073679103667)
    ·
      refine ⟨33962224940880110518655501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22641483293920073679103667 33962224940880110518655501)
      ·
        refine ⟨12735834352830041444495813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33962224940880110518655501 12735834352830041444495813)
        ·
          refine ⟨2387968941155632770842965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12735834352830041444495813 2387968941155632770842965)
          ·
            refine ⟨6996002757291892883329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2387968941155632770842965 6996002757291892883329)
            ·
              rfl

theorem cell22_1655397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 10].length) (baseStart_1655397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655397 prefixEnd_1655397 := by exact prefixLift 1655397
  have htrace : WordTrace (prefixWord ++ tailWord_1655397) baseStart_1655397 baseEnd_1655397 := by
    simpa [prefixWord, tailWord_1655397, baseEnd_1655397] using wordTrace_append hprefix tailTrace_1655397
  have hstable : (prefixWord ++ tailWord_1655397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655397).length < 2 ^ (prefixWord ++ tailWord_1655397).sum := by decide
  have hdescent : baseEnd_1655397 < baseStart_1655397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655429 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_1655429 : Nat := 118140960795 + 1655429 * 2 ^ 59
def prefixEnd_1655429 : Nat := 4983230072969 + 3 ^ 40 * 1655429 * 2
def baseEnd_1655429 : Nat := 566687177594605906749551

theorem tailTrace_1655429 : CollatzResearch.WordTrace tailWord_1655429 prefixEnd_1655429 566687177594605906749551 := by
  unfold tailWord_1655429
  simp only [CollatzResearch.WordTrace]
  refine ⟨60378455919670932609441341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40252303946447288406294227 60378455919670932609441341)
  ·
    refine ⟨22641920969876599728540503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60378455919670932609441341 22641920969876599728540503)
    ·
      refine ⟨33962881454814899592810755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22641920969876599728540503 33962881454814899592810755)
      ·
        refine ⟨50944322182222349389216133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33962881454814899592810755 50944322182222349389216133)
        ·
          refine ⟨9552060409166690510478025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50944322182222349389216133 9552060409166690510478025)
          ·
            refine ⟨7164045306875017882858519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9552060409166690510478025 7164045306875017882858519)
            ·
              refine ⟨10746067960312526824287779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164045306875017882858519 10746067960312526824287779)
              ·
                refine ⟨16119101940468790236431669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746067960312526824287779 16119101940468790236431669)
                ·
                  refine ⟨1511165806918949084665469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16119101940468790236431669 1511165806918949084665469)
                  ·
                    refine ⟨566687177594605906749551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1511165806918949084665469 566687177594605906749551)
                    ·
                      rfl

theorem cell22_1655429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_1655429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655429 prefixEnd_1655429 := by exact prefixLift 1655429
  have htrace : WordTrace (prefixWord ++ tailWord_1655429) baseStart_1655429 baseEnd_1655429 := by
    simpa [prefixWord, tailWord_1655429, baseEnd_1655429] using wordTrace_append hprefix tailTrace_1655429
  have hstable : (prefixWord ++ tailWord_1655429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655429).length < 2 ^ (prefixWord ++ tailWord_1655429).sum := by decide
  have hdescent : baseEnd_1655429 < baseStart_1655429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655521 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 6]
def baseStart_1655521 : Nat := 118140960795 + 1655521 * 2 ^ 59
def prefixEnd_1655521 : Nat := 4983230072969 + 3 ^ 40 * 1655521 * 2
def baseEnd_1655521 : Nat := 188906223691582777816423

theorem tailTrace_1655521 : CollatzResearch.WordTrace tailWord_1655521 prefixEnd_1655521 188906223691582777816423 := by
  unfold tailWord_1655521
  simp only [CollatzResearch.WordTrace]
  refine ⟨60381811435337632321790417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40254540956891754881193611 60381811435337632321790417)
  ·
    refine ⟨45286358576503224241342813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60381811435337632321790417 45286358576503224241342813)
    ·
      refine ⟨16982384466188709090503555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45286358576503224241342813 16982384466188709090503555)
      ·
        refine ⟨25473576699283063635755333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16982384466188709090503555 25473576699283063635755333)
        ·
          refine ⟨4776295631115574431704125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25473576699283063635755333 4776295631115574431704125)
          ·
            refine ⟨1791110861668340411889047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4776295631115574431704125 1791110861668340411889047)
            ·
              refine ⟨2686666292502510617833571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791110861668340411889047 2686666292502510617833571)
              ·
                refine ⟨4029999438753765926750357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686666292502510617833571 4029999438753765926750357)
                ·
                  refine ⟨188906223691582777816423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4029999438753765926750357 188906223691582777816423)
                  ·
                    rfl

theorem cell22_1655521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_1655521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655521 prefixEnd_1655521 := by exact prefixLift 1655521
  have htrace : WordTrace (prefixWord ++ tailWord_1655521) baseStart_1655521 baseEnd_1655521 := by
    simpa [prefixWord, tailWord_1655521, baseEnd_1655521] using wordTrace_append hprefix tailTrace_1655521
  have hstable : (prefixWord ++ tailWord_1655521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655521).length < 2 ^ (prefixWord ++ tailWord_1655521).sum := by decide
  have hdescent : baseEnd_1655521 < baseStart_1655521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655536 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 2, 3]
def baseStart_1655536 : Nat := 118140960795 + 1655536 * 2 ^ 59
def prefixEnd_1655536 : Nat := 4983230072969 + 3 ^ 40 * 1655536 * 2
def baseEnd_1655536 : Nat := 566723805881293294324223

theorem tailTrace_1655536 : CollatzResearch.WordTrace tailWord_1655536 prefixEnd_1655536 566723805881293294324223 := by
  unfold tailWord_1655536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30191179265141644941793231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40254905686855526589057641 30191179265141644941793231)
  ·
    refine ⟨45286768897712467412689847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30191179265141644941793231 45286768897712467412689847)
    ·
      refine ⟨67930153346568701119034771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45286768897712467412689847 67930153346568701119034771)
      ·
        refine ⟨101895230019853051678552157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67930153346568701119034771 101895230019853051678552157)
        ·
          refine ⟨38210711257444894379457059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101895230019853051678552157 38210711257444894379457059)
          ·
            refine ⟨57316066886167341569185589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38210711257444894379457059 57316066886167341569185589)
            ·
              refine ⟨5373381270578188272111149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57316066886167341569185589 5373381270578188272111149)
              ·
                refine ⟨2015017976466820602041681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5373381270578188272111149 2015017976466820602041681)
                ·
                  refine ⟨1511263482350115451531261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2015017976466820602041681 1511263482350115451531261)
                  ·
                    refine ⟨566723805881293294324223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1511263482350115451531261 566723805881293294324223)
                    ·
                      rfl

theorem cell22_1655536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_1655536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655536 prefixEnd_1655536 := by exact prefixLift 1655536
  have htrace : WordTrace (prefixWord ++ tailWord_1655536) baseStart_1655536 baseEnd_1655536 := by
    simpa [prefixWord, tailWord_1655536, baseEnd_1655536] using wordTrace_append hprefix tailTrace_1655536
  have hstable : (prefixWord ++ tailWord_1655536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655536).length < 2 ^ (prefixWord ++ tailWord_1655536).sum := by decide
  have hdescent : baseEnd_1655536 < baseStart_1655536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655540 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1655540 : Nat := 118140960795 + 1655540 * 2 ^ 59
def prefixEnd_1655540 : Nat := 4983230072969 + 3 ^ 40 * 1655540 * 2
def baseEnd_1655540 : Nat := 566725175163038617224211

theorem tailTrace_1655540 : CollatzResearch.WordTrace tailWord_1655540 prefixEnd_1655540 566725175163038617224211 := by
  unfold tailWord_1655540
  simp only [CollatzResearch.WordTrace]
  refine ⟨30191252211134399283366037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40255002948179199044488049 30191252211134399283366037)
  ·
    refine ⟨1415214947396924966407783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30191252211134399283366037 1415214947396924966407783)
    ·
      refine ⟨2122822421095387449611675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415214947396924966407783 2122822421095387449611675)
      ·
        refine ⟨3184233631643081174417513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122822421095387449611675 3184233631643081174417513)
        ·
          refine ⟨2388175223732310880813135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3184233631643081174417513 2388175223732310880813135)
          ·
            refine ⟨3582262835598466321219703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388175223732310880813135 3582262835598466321219703)
            ·
              refine ⟨5373394253397699481829555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582262835598466321219703 5373394253397699481829555)
              ·
                refine ⟨8060091380096549222744333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373394253397699481829555 8060091380096549222744333)
                ·
                  refine ⟨3022534267536205958529125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8060091380096549222744333 3022534267536205958529125)
                  ·
                    refine ⟨566725175163038617224211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3022534267536205958529125 566725175163038617224211)
                    ·
                      rfl

theorem cell22_1655540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1655540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655540 prefixEnd_1655540 := by exact prefixLift 1655540
  have htrace : WordTrace (prefixWord ++ tailWord_1655540) baseStart_1655540 baseEnd_1655540 := by
    simpa [prefixWord, tailWord_1655540, baseEnd_1655540] using wordTrace_append hprefix tailTrace_1655540
  have hstable : (prefixWord ++ tailWord_1655540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655540).length < 2 ^ (prefixWord ++ tailWord_1655540).sum := by decide
  have hdescent : baseEnd_1655540 < baseStart_1655540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655598 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1655598 : Nat := 118140960795 + 1655598 * 2 ^ 59
def prefixEnd_1655598 : Nat := 4983230072969 + 3 ^ 40 * 1655598 * 2
def baseEnd_1655598 : Nat := 566745029748345799274033

theorem tailTrace_1655598 : CollatzResearch.WordTrace tailWord_1655598 prefixEnd_1655598 566745029748345799274033 := by
  unfold tailWord_1655598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7548077482007334309042931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40256413237372449648228965 7548077482007334309042931)
  ·
    refine ⟨11322116223011001463564397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7548077482007334309042931 11322116223011001463564397)
    ·
      refine ⟨4245793583629125548836649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11322116223011001463564397 4245793583629125548836649)
      ·
        refine ⟨3184345187721844161627487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4245793583629125548836649 3184345187721844161627487)
        ·
          refine ⟨4776517781582766242441231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184345187721844161627487 4776517781582766242441231)
          ·
            refine ⟨7164776672374149363661847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776517781582766242441231 7164776672374149363661847)
            ·
              refine ⟨10747165008561224045492771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164776672374149363661847 10747165008561224045492771)
              ·
                refine ⟨16120747512841836068239157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10747165008561224045492771 16120747512841836068239157)
                ·
                  refine ⟨1511320079328922131397421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16120747512841836068239157 1511320079328922131397421)
                  ·
                    refine ⟨566745029748345799274033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1511320079328922131397421 566745029748345799274033)
                    ·
                      rfl

theorem cell22_1655598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1655598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655598 prefixEnd_1655598 := by exact prefixLift 1655598
  have htrace : WordTrace (prefixWord ++ tailWord_1655598) baseStart_1655598 baseEnd_1655598 := by
    simpa [prefixWord, tailWord_1655598, baseEnd_1655598] using wordTrace_append hprefix tailTrace_1655598
  have hstable : (prefixWord ++ tailWord_1655598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655598).length < 2 ^ (prefixWord ++ tailWord_1655598).sum := by decide
  have hdescent : baseEnd_1655598 < baseStart_1655598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655615 : List Nat := [1, 1, 2, 2, 5, 2, 2, 3, 1, 3]
def baseStart_1655615 : Nat := 118140960795 + 1655615 * 2 ^ 59
def prefixEnd_1655615 : Nat := 4983230072969 + 3 ^ 40 * 1655615 * 2
def baseEnd_1655615 : Nat := 566750849195763421598981

theorem tailTrace_1655615 : CollatzResearch.WordTrace tailWord_1655615 prefixEnd_1655615 566750849195763421598981 := by
  unfold tailWord_1655615
  simp only [CollatzResearch.WordTrace]
  refine ⟨60385239896997086375712299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40256826597998057583808199 60385239896997086375712299)
  ·
    refine ⟨90577859845495629563568449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60385239896997086375712299 90577859845495629563568449)
    ·
      refine ⟨67933394884121722172676337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90577859845495629563568449 67933394884121722172676337)
      ·
        refine ⟨50950046163091291629507253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67933394884121722172676337 50950046163091291629507253)
        ·
          refine ⟨4776566827789808590266305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50950046163091291629507253 4776566827789808590266305)
          ·
            refine ⟨3582425120842356442699729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4776566827789808590266305 3582425120842356442699729)
            ·
              refine ⟨2686818840631767332024797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3582425120842356442699729 2686818840631767332024797)
              ·
                refine ⟨1007557065236912749509299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686818840631767332024797 1007557065236912749509299)
                ·
                  refine ⟨1511335597855369124263949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007557065236912749509299 1511335597855369124263949)
                  ·
                    refine ⟨566750849195763421598981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1511335597855369124263949 566750849195763421598981)
                    ·
                      rfl

theorem cell22_1655615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 1, 3].length) (baseStart_1655615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655615 prefixEnd_1655615 := by exact prefixLift 1655615
  have htrace : WordTrace (prefixWord ++ tailWord_1655615) baseStart_1655615 baseEnd_1655615 := by
    simpa [prefixWord, tailWord_1655615, baseEnd_1655615] using wordTrace_append hprefix tailTrace_1655615
  have hstable : (prefixWord ++ tailWord_1655615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655615).length < 2 ^ (prefixWord ++ tailWord_1655615).sum := by decide
  have hdescent : baseEnd_1655615 < baseStart_1655615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655628 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 5]
def baseStart_1655628 : Nat := 118140960795 + 1655628 * 2 ^ 59
def prefixEnd_1655628 : Nat := 4983230072969 + 3 ^ 40 * 1655628 * 2
def baseEnd_1655628 : Nat := 188918433120478573674647

theorem tailTrace_1655628 : CollatzResearch.WordTrace tailWord_1655628 prefixEnd_1655628 188918433120478573674647 := by
  unfold tailWord_1655628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30192857022974994797967769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40257142697299993063957025 30192857022974994797967769)
  ·
    refine ⟨22644642767231246098475827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30192857022974994797967769 22644642767231246098475827)
    ·
      refine ⟨33966964150846869147713741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22644642767231246098475827 33966964150846869147713741)
      ·
        refine ⟨12737611556567575930392653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33966964150846869147713741 12737611556567575930392653)
        ·
          refine ⟨4776604333712840973897245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12737611556567575930392653 4776604333712840973897245)
          ·
            refine ⟨1791226625142315365211467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4776604333712840973897245 1791226625142315365211467)
            ·
              refine ⟨2686839937713473047817201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791226625142315365211467 2686839937713473047817201)
              ·
                refine ⟨2015129953285104785862901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686839937713473047817201 2015129953285104785862901)
                ·
                  refine ⟨188918433120478573674647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2015129953285104785862901 188918433120478573674647)
                  ·
                    rfl

theorem cell22_1655628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_1655628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655628 prefixEnd_1655628 := by exact prefixLift 1655628
  have htrace : WordTrace (prefixWord ++ tailWord_1655628) baseStart_1655628 baseEnd_1655628 := by
    simpa [prefixWord, tailWord_1655628, baseEnd_1655628] using wordTrace_append hprefix tailTrace_1655628
  have hstable : (prefixWord ++ tailWord_1655628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655628).length < 2 ^ (prefixWord ++ tailWord_1655628).sum := by decide
  have hdescent : baseEnd_1655628 < baseStart_1655628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655656 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 6]
def baseStart_1655656 : Nat := 118140960795 + 1655656 * 2 ^ 59
def prefixEnd_1655656 : Nat := 4983230072969 + 3 ^ 40 * 1655656 * 2
def baseEnd_1655656 : Nat := 188921628111217660441285

theorem tailTrace_1655656 : CollatzResearch.WordTrace tailWord_1655656 prefixEnd_1655656 188921628111217660441285 := by
  unfold tailWord_1655656
  simp only [CollatzResearch.WordTrace]
  refine ⟨30193367644924275188977411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40257823526565700251969881 30193367644924275188977411)
  ·
    refine ⟨45290051467386412783466117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30193367644924275188977411 45290051467386412783466117)
    ·
      refine ⟨8491884650134952396899897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45290051467386412783466117 8491884650134952396899897)
      ·
        refine ⟨6368913487601214297674923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8491884650134952396899897 6368913487601214297674923)
        ·
          refine ⟨9553370231401821446512385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6368913487601214297674923 9553370231401821446512385)
          ·
            refine ⟨7165027673551366084884289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9553370231401821446512385 7165027673551366084884289)
            ·
              refine ⟨5373770755163524563663217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7165027673551366084884289 5373770755163524563663217)
              ·
                refine ⟨4030328066372643422747413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5373770755163524563663217 4030328066372643422747413)
                ·
                  refine ⟨188921628111217660441285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4030328066372643422747413 188921628111217660441285)
                  ·
                    rfl

theorem cell22_1655656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_1655656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655656 prefixEnd_1655656 := by exact prefixLift 1655656
  have htrace : WordTrace (prefixWord ++ tailWord_1655656) baseStart_1655656 baseEnd_1655656 := by
    simpa [prefixWord, tailWord_1655656, baseEnd_1655656] using wordTrace_append hprefix tailTrace_1655656
  have hstable : (prefixWord ++ tailWord_1655656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655656).length < 2 ^ (prefixWord ++ tailWord_1655656).sum := by decide
  have hdescent : baseEnd_1655656 < baseStart_1655656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655673 : List Nat := [1, 2, 1, 3, 2, 3, 3, 3, 4]
def baseStart_1655673 : Nat := 118140960795 + 1655673 * 2 ^ 59
def prefixEnd_1655673 : Nat := 4983230072969 + 3 ^ 40 * 1655673 * 2
def baseEnd_1655673 : Nat := 188923567927023534549601

theorem tailTrace_1655673 : CollatzResearch.WordTrace tailWord_1655673 prefixEnd_1655673 188923567927023534549601 := by
  unfold tailWord_1655673
  simp only [CollatzResearch.WordTrace]
  refine ⟨60387355330786962281323673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40258236887191308187549115 60387355330786962281323673)
  ·
    refine ⟨45290516498090221710992755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60387355330786962281323673 45290516498090221710992755)
    ·
      refine ⟨67935774747135332566489133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45290516498090221710992755 67935774747135332566489133)
      ·
        refine ⟨25475915530175749712433425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67935774747135332566489133 25475915530175749712433425)
        ·
          refine ⟨19106936647631812284325069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25475915530175749712433425 19106936647631812284325069)
          ·
            refine ⟨7165101242861929606621901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19106936647631812284325069 7165101242861929606621901)
            ·
              refine ⟨2686912966073223602483213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7165101242861929606621901 2686912966073223602483213)
              ·
                refine ⟨1007592362277458850931205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686912966073223602483213 1007592362277458850931205)
                ·
                  refine ⟨188923567927023534549601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007592362277458850931205 188923567927023534549601)
                  ·
                    rfl

theorem cell22_1655673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 4].length) (baseStart_1655673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655673 prefixEnd_1655673 := by exact prefixLift 1655673
  have htrace : WordTrace (prefixWord ++ tailWord_1655673) baseStart_1655673 baseEnd_1655673 := by
    simpa [prefixWord, tailWord_1655673, baseEnd_1655673] using wordTrace_append hprefix tailTrace_1655673
  have hstable : (prefixWord ++ tailWord_1655673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655673).length < 2 ^ (prefixWord ++ tailWord_1655673).sum := by decide
  have hdescent : baseEnd_1655673 < baseStart_1655673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655688 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 4, 3]
def baseStart_1655688 : Nat := 118140960795 + 1655688 * 2 ^ 59
def prefixEnd_1655688 : Nat := 4983230072969 + 3 ^ 40 * 1655688 * 2
def baseEnd_1655688 : Nat := 566775838587615564523757

theorem tailTrace_1655688 : CollatzResearch.WordTrace tailWord_1655688 prefixEnd_1655688 566775838587615564523757 := by
  unfold tailWord_1655688
  simp only [CollatzResearch.WordTrace]
  refine ⟨30193951212866309921559859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40258601617155079895413145 30193951212866309921559859)
  ·
    refine ⟨45290926819299464882339789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30193951212866309921559859 45290926819299464882339789)
    ·
      refine ⟨16984097557237299330877421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45290926819299464882339789 16984097557237299330877421)
      ·
        refine ⟨6369036583963987249079033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16984097557237299330877421 6369036583963987249079033)
        ·
          refine ⟨4776777437972990436809275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6369036583963987249079033 4776777437972990436809275)
          ·
            refine ⟨7165166156959485655213913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776777437972990436809275 7165166156959485655213913)
            ·
              refine ⟨5373874617719614241410435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7165166156959485655213913 5373874617719614241410435)
              ·
                refine ⟨8060811926579421362115653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373874617719614241410435 8060811926579421362115653)
                ·
                  refine ⟨1511402236233641505396685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8060811926579421362115653 1511402236233641505396685)
                  ·
                    refine ⟨566775838587615564523757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1511402236233641505396685 566775838587615564523757)
                    ·
                      rfl

theorem cell22_1655688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_1655688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655688 prefixEnd_1655688 := by exact prefixLift 1655688
  have htrace : WordTrace (prefixWord ++ tailWord_1655688) baseStart_1655688 baseEnd_1655688 := by
    simpa [prefixWord, tailWord_1655688, baseEnd_1655688] using wordTrace_append hprefix tailTrace_1655688
  have hstable : (prefixWord ++ tailWord_1655688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655688).length < 2 ^ (prefixWord ++ tailWord_1655688).sum := by decide
  have hdescent : baseEnd_1655688 < baseStart_1655688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655699 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 2, 7]
def baseStart_1655699 : Nat := 118140960795 + 1655699 * 2 ^ 59
def prefixEnd_1655699 : Nat := 4983230072969 + 3 ^ 40 * 1655699 * 2
def baseEnd_1655699 : Nat := 566779604112415202498723

theorem tailTrace_1655699 : CollatzResearch.WordTrace tailWord_1655699 prefixEnd_1655699 566779604112415202498723 := by
  unfold tailWord_1655699
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388303628692768721770151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40258869085795179147846767 60388303628692768721770151)
  ·
    refine ⟨90582455443039153082655227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60388303628692768721770151 90582455443039153082655227)
    ·
      refine ⟨135873683164558729623982841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90582455443039153082655227 135873683164558729623982841)
      ·
        refine ⟨101905262373419047217987131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135873683164558729623982841 101905262373419047217987131)
        ·
          refine ⟨152857893560128570826980697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101905262373419047217987131 152857893560128570826980697)
          ·
            refine ⟨114643420170096428120235523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152857893560128570826980697 114643420170096428120235523)
            ·
              refine ⟨171965130255144642180353285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114643420170096428120235523 171965130255144642180353285)
              ·
                refine ⟨32243461922839620408816241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171965130255144642180353285 32243461922839620408816241)
                ·
                  refine ⟨24182596442129715306612181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32243461922839620408816241 24182596442129715306612181)
                  ·
                    refine ⟨566779604112415202498723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24182596442129715306612181 566779604112415202498723)
                    ·
                      rfl

theorem cell22_1655699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_1655699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655699 prefixEnd_1655699 := by exact prefixLift 1655699
  have htrace : WordTrace (prefixWord ++ tailWord_1655699) baseStart_1655699 baseEnd_1655699 := by
    simpa [prefixWord, tailWord_1655699, baseEnd_1655699] using wordTrace_append hprefix tailTrace_1655699
  have hstable : (prefixWord ++ tailWord_1655699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655699).length < 2 ^ (prefixWord ++ tailWord_1655699).sum := by decide
  have hdescent : baseEnd_1655699 < baseStart_1655699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655701 : List Nat := [1, 3, 2, 1, 1, 5, 2, 7]
def baseStart_1655701 : Nat := 118140960795 + 1655701 * 2 ^ 59
def prefixEnd_1655701 : Nat := 4983230072969 + 3 ^ 40 * 1655701 * 2
def baseEnd_1655701 : Nat := 62975587639254207105413

theorem tailTrace_1655701 : CollatzResearch.WordTrace tailWord_1655701 prefixEnd_1655701 62975587639254207105413 := by
  unfold tailWord_1655701
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388376574685523063342957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40258917716457015375561971 60388376574685523063342957)
  ·
    refine ⟨22645641215507071148753609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60388376574685523063342957 22645641215507071148753609)
    ·
      refine ⟨16984230911630303361565207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22645641215507071148753609 16984230911630303361565207)
      ·
        refine ⟨25476346367445455042347811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16984230911630303361565207 25476346367445455042347811)
        ·
          refine ⟨38214519551168182563521717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25476346367445455042347811 38214519551168182563521717)
          ·
            refine ⟨3582611207922017115330161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38214519551168182563521717 3582611207922017115330161)
            ·
              refine ⟨2686958405941512836497621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3582611207922017115330161 2686958405941512836497621)
              ·
                refine ⟨62975587639254207105413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2686958405941512836497621 62975587639254207105413)
                ·
                  rfl

theorem cell22_1655701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 7].length) (baseStart_1655701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655701 prefixEnd_1655701 := by exact prefixLift 1655701
  have htrace : WordTrace (prefixWord ++ tailWord_1655701) baseStart_1655701 baseEnd_1655701 := by
    simpa [prefixWord, tailWord_1655701, baseEnd_1655701] using wordTrace_append hprefix tailTrace_1655701
  have hstable : (prefixWord ++ tailWord_1655701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655701).length < 2 ^ (prefixWord ++ tailWord_1655701).sum := by decide
  have hdescent : baseEnd_1655701 < baseStart_1655701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655761 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1655761 : Nat := 118140960795 + 1655761 * 2 ^ 59
def prefixEnd_1655761 : Nat := 4983230072969 + 3 ^ 40 * 1655761 * 2
def baseEnd_1655761 : Nat := 566800827979467707448533

theorem tailTrace_1655761 : CollatzResearch.WordTrace tailWord_1655761 prefixEnd_1655761 566800827979467707448533 := by
  unfold tailWord_1655761
  simp only [CollatzResearch.WordTrace]
  refine ⟨60390564954468153310527137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40260376636312102207018091 60390564954468153310527137)
  ·
    refine ⟨45292923715851114982895353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60390564954468153310527137 45292923715851114982895353)
    ·
      refine ⟨33969692786888336237171515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45292923715851114982895353 33969692786888336237171515)
      ·
        refine ⟨50954539180332504355757273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33969692786888336237171515 50954539180332504355757273)
        ·
          refine ⟨38215904385249378266817955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50954539180332504355757273 38215904385249378266817955)
          ·
            refine ⟨57323856577874067400226933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38215904385249378266817955 57323856577874067400226933)
            ·
              refine ⟨5374111554175693818771275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57323856577874067400226933 5374111554175693818771275)
              ·
                refine ⟨8061167331263540728156913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5374111554175693818771275 8061167331263540728156913)
                ·
                  refine ⟨6045875498447655546117685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8061167331263540728156913 6045875498447655546117685)
                  ·
                    refine ⟨566800827979467707448533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6045875498447655546117685 566800827979467707448533)
                    ·
                      rfl

theorem cell22_1655761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1655761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655761 prefixEnd_1655761 := by exact prefixLift 1655761
  have htrace : WordTrace (prefixWord ++ tailWord_1655761) baseStart_1655761 baseEnd_1655761 := by
    simpa [prefixWord, tailWord_1655761, baseEnd_1655761] using wordTrace_append hprefix tailTrace_1655761
  have hstable : (prefixWord ++ tailWord_1655761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655761).length < 2 ^ (prefixWord ++ tailWord_1655761).sum := by decide
  have hdescent : baseEnd_1655761 < baseStart_1655761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655842 : List Nat := [3, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1655842 : Nat := 118140960795 + 1655842 * 2 ^ 59
def prefixEnd_1655842 : Nat := 4983230072969 + 3 ^ 40 * 1655842 * 2
def baseEnd_1655842 : Nat := 188942851978270165391095

theorem tailTrace_1655842 : CollatzResearch.WordTrace tailWord_1655842 prefixEnd_1655842 188942851978270165391095 := by
  unfold tailWord_1655842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098379816793676036056445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40262346178116469429483853 15098379816793676036056445)
  ·
    refine ⟨5661892431297628513521167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15098379816793676036056445 5661892431297628513521167)
    ·
      refine ⟨8492838646946442770281751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661892431297628513521167 8492838646946442770281751)
      ·
        refine ⟨12739257970419664155422627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8492838646946442770281751 12739257970419664155422627)
        ·
          refine ⟨19108886955629496233133941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12739257970419664155422627 19108886955629496233133941)
          ·
            refine ⟨1791458152090265271856307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19108886955629496233133941 1791458152090265271856307)
            ·
              refine ⟨2687187228135397907784461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791458152090265271856307 2687187228135397907784461)
              ·
                refine ⟨1007695210550774215419173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2687187228135397907784461 1007695210550774215419173)
                ·
                  refine ⟨188942851978270165391095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007695210550774215419173 188942851978270165391095)
                  ·
                    rfl

theorem cell22_1655842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1655842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655842 prefixEnd_1655842 := by exact prefixLift 1655842
  have htrace : WordTrace (prefixWord ++ tailWord_1655842) baseStart_1655842 baseEnd_1655842 := by
    simpa [prefixWord, tailWord_1655842, baseEnd_1655842] using wordTrace_append hprefix tailTrace_1655842
  have hstable : (prefixWord ++ tailWord_1655842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655842).length < 2 ^ (prefixWord ++ tailWord_1655842).sum := by decide
  have hdescent : baseEnd_1655842 < baseStart_1655842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655870 : List Nat := [4, 2, 1, 3, 1, 2, 2, 7]
def baseStart_1655870 : Nat := 118140960795 + 1655870 * 2 ^ 59
def prefixEnd_1655870 : Nat := 4983230072969 + 3 ^ 40 * 1655870 * 2
def baseEnd_1655870 : Nat := 62982015656336417385911

theorem tailTrace_1655870 : CollatzResearch.WordTrace tailWord_1655870 prefixEnd_1655870 62982015656336417385911 := by
  unfold tailWord_1655870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549317563884158115780633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40263027007382176617496709 7549317563884158115780633)
  ·
    refine ⟨5661988172913118586835475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7549317563884158115780633 5661988172913118586835475)
    ·
      refine ⟨8492982259369677880253213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661988172913118586835475 8492982259369677880253213)
      ·
        refine ⟨3184868347263629205094955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8492982259369677880253213 3184868347263629205094955)
        ·
          refine ⟨4777302520895443807642433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184868347263629205094955 4777302520895443807642433)
          ·
            refine ⟨3582976890671582855731825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777302520895443807642433 3582976890671582855731825)
            ·
              refine ⟨2687232668003687141798869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3582976890671582855731825 2687232668003687141798869)
              ·
                refine ⟨62982015656336417385911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2687232668003687141798869 62982015656336417385911)
                ·
                  rfl

theorem cell22_1655870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_1655870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655870 prefixEnd_1655870 := by exact prefixLift 1655870
  have htrace : WordTrace (prefixWord ++ tailWord_1655870) baseStart_1655870 baseEnd_1655870 := by
    simpa [prefixWord, tailWord_1655870, baseEnd_1655870] using wordTrace_append hprefix tailTrace_1655870
  have hstable : (prefixWord ++ tailWord_1655870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655870).length < 2 ^ (prefixWord ++ tailWord_1655870).sum := by decide
  have hdescent : baseEnd_1655870 < baseStart_1655870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655881 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 9]
def baseStart_1655881 : Nat := 118140960795 + 1655881 * 2 ^ 59
def prefixEnd_1655881 : Nat := 4983230072969 + 3 ^ 40 * 1655881 * 2
def baseEnd_1655881 : Nat := 188947302143942464816055

theorem tailTrace_1655881 : CollatzResearch.WordTrace tailWord_1655881 prefixEnd_1655881 188947302143942464816055 := by
  unfold tailWord_1655881
  simp only [CollatzResearch.WordTrace]
  refine ⟨60394941714033413804895497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40263294476022275869930331 60394941714033413804895497)
  ·
    refine ⟨45296206285525060353671623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60394941714033413804895497 45296206285525060353671623)
    ·
      refine ⟨67944309428287590530507435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45296206285525060353671623 67944309428287590530507435)
      ·
        refine ⟨101916464142431385795761153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67944309428287590530507435 101916464142431385795761153)
        ·
          refine ⟨76437348106823539346820865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101916464142431385795761153 76437348106823539346820865)
          ·
            refine ⟨57328011080117654510115649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76437348106823539346820865 57328011080117654510115649)
            ·
              refine ⟨42996008310088240882586737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57328011080117654510115649 42996008310088240882586737)
              ·
                refine ⟨32247006232566180661940053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42996008310088240882586737 32247006232566180661940053)
                ·
                  refine ⟨188947302143942464816055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32247006232566180661940053 188947302143942464816055)
                  ·
                    rfl

theorem cell22_1655881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_1655881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655881 prefixEnd_1655881 := by exact prefixLift 1655881
  have htrace : WordTrace (prefixWord ++ tailWord_1655881) baseStart_1655881 baseEnd_1655881 := by
    simpa [prefixWord, tailWord_1655881, baseEnd_1655881] using wordTrace_append hprefix tailTrace_1655881
  have hstable : (prefixWord ++ tailWord_1655881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655881).length < 2 ^ (prefixWord ++ tailWord_1655881).sum := by decide
  have hdescent : baseEnd_1655881 < baseStart_1655881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655928 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_1655928 : Nat := 118140960795 + 1655928 * 2 ^ 59
def prefixEnd_1655928 : Nat := 4983230072969 + 3 ^ 40 * 1655928 * 2
def baseEnd_1655928 : Nat := 566857995492334938523021

theorem tailTrace_1655928 : CollatzResearch.WordTrace tailWord_1655928 prefixEnd_1655928 566857995492334938523021 := by
  unfold tailWord_1655928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30198327972431570415928219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40264437296575427221237625 30198327972431570415928219)
  ·
    refine ⟨45297491958647355623892329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30198327972431570415928219 45297491958647355623892329)
    ·
      refine ⟨33973118968985516717919247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45297491958647355623892329 33973118968985516717919247)
      ·
        refine ⟨50959678453478275076878871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33973118968985516717919247 50959678453478275076878871)
        ·
          refine ⟨76439517680217412615318307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50959678453478275076878871 76439517680217412615318307)
          ·
            refine ⟨114659276520326118922977461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76439517680217412615318307 114659276520326118922977461)
            ·
              refine ⟨10749307173780573649029137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114659276520326118922977461 10749307173780573649029137)
              ·
                refine ⟨8061980380335430236771853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10749307173780573649029137 8061980380335430236771853)
                ·
                  refine ⟨3023242642625786338789445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8061980380335430236771853 3023242642625786338789445)
                  ·
                    refine ⟨566857995492334938523021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3023242642625786338789445 566857995492334938523021)
                    ·
                      rfl

theorem cell22_1655928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_1655928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655928 prefixEnd_1655928 := by exact prefixLift 1655928
  have htrace : WordTrace (prefixWord ++ tailWord_1655928) baseStart_1655928 baseEnd_1655928 := by
    simpa [prefixWord, tailWord_1655928, baseEnd_1655928] using wordTrace_append hprefix tailTrace_1655928
  have hstable : (prefixWord ++ tailWord_1655928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655928).length < 2 ^ (prefixWord ++ tailWord_1655928).sum := by decide
  have hdescent : baseEnd_1655928 < baseStart_1655928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655962 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_1655962 : Nat := 118140960795 + 1655962 * 2 ^ 59
def prefixEnd_1655962 : Nat := 4983230072969 + 3 ^ 40 * 1655962 * 2
def baseEnd_1655962 : Nat := 566869634387170183172917

theorem tailTrace_1655962 : CollatzResearch.WordTrace tailWord_1655962 prefixEnd_1655962 566869634387170183172917 := by
  unfold tailWord_1655962
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099474006684991159648535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40265264017826643092396093 15099474006684991159648535)
  ·
    refine ⟨22649211010027486739472803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15099474006684991159648535 22649211010027486739472803)
    ·
      refine ⟨33973816515041230109209205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22649211010027486739472803 33973816515041230109209205)
      ·
        refine ⟨3185045298285115322738363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33973816515041230109209205 3185045298285115322738363)
        ·
          refine ⟨4777567947427672984107545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185045298285115322738363 4777567947427672984107545)
          ·
            refine ⟨3583175960570754738080659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777567947427672984107545 3583175960570754738080659)
            ·
              refine ⟨5374763940856132107120989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583175960570754738080659 5374763940856132107120989)
              ·
                refine ⟨2015536477821049540170371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5374763940856132107120989 2015536477821049540170371)
                ·
                  refine ⟨3023304716731574310255557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015536477821049540170371 3023304716731574310255557)
                  ·
                    refine ⟨566869634387170183172917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3023304716731574310255557 566869634387170183172917)
                    ·
                      rfl

theorem cell22_1655962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_1655962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1655962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1655962 prefixEnd_1655962 := by exact prefixLift 1655962
  have htrace : WordTrace (prefixWord ++ tailWord_1655962) baseStart_1655962 baseEnd_1655962 := by
    simpa [prefixWord, tailWord_1655962, baseEnd_1655962] using wordTrace_append hprefix tailTrace_1655962
  have hstable : (prefixWord ++ tailWord_1655962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655962).length < 2 ^ (prefixWord ++ tailWord_1655962).sum := by decide
  have hdescent : baseEnd_1655962 < baseStart_1655962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656129 : List Nat := [1, 2, 5, 2, 1, 1, 1, 5, 4]
def baseStart_1656129 : Nat := 118140960795 + 1656129 * 2 ^ 59
def prefixEnd_1656129 : Nat := 4983230072969 + 3 ^ 40 * 1656129 * 2
def baseEnd_1656129 : Nat := 188975600633345804749135

theorem tailTrace_1656129 : CollatzResearch.WordTrace tailWord_1656129 prefixEnd_1656129 188975600633345804749135 := by
  unfold tailWord_1656129
  simp only [CollatzResearch.WordTrace]
  refine ⟨60403987017134952159923441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40269324678089968106615627 60403987017134952159923441)
  ·
    refine ⟨45302990262851214119942581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60403987017134952159923441 45302990262851214119942581)
    ·
      refine ⟨4247155337142301323744617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45302990262851214119942581 4247155337142301323744617)
      ·
        refine ⟨3185366502856725992808463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4247155337142301323744617 3185366502856725992808463)
        ·
          refine ⟨4778049754285088989212695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185366502856725992808463 4778049754285088989212695)
          ·
            refine ⟨7167074631427633483819043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778049754285088989212695 7167074631427633483819043)
            ·
              refine ⟨10750611947141450225728565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167074631427633483819043 10750611947141450225728565)
              ·
                refine ⟨1007869870044510958662053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10750611947141450225728565 1007869870044510958662053)
                ·
                  refine ⟨188975600633345804749135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007869870044510958662053 188975600633345804749135)
                  ·
                    rfl

theorem cell22_1656129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 4].length) (baseStart_1656129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656129 prefixEnd_1656129 := by exact prefixLift 1656129
  have htrace : WordTrace (prefixWord ++ tailWord_1656129) baseStart_1656129 baseEnd_1656129 := by
    simpa [prefixWord, tailWord_1656129, baseEnd_1656129] using wordTrace_append hprefix tailTrace_1656129
  have hstable : (prefixWord ++ tailWord_1656129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656129).length < 2 ^ (prefixWord ++ tailWord_1656129).sum := by decide
  have hdescent : baseEnd_1656129 < baseStart_1656129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656140 : List Nat := [2, 2, 1, 3, 2, 3, 9]
def baseStart_1656140 : Nat := 118140960795 + 1656140 * 2 ^ 59
def prefixEnd_1656140 : Nat := 4983230072969 + 3 ^ 40 * 1656140 * 2
def baseEnd_1656140 : Nat := 20997428423142113045273

theorem tailTrace_1656140 : CollatzResearch.WordTrace tailWord_1656140 prefixEnd_1656140 20997428423142113045273 := by
  unfold tailWord_1656140
  simp only [CollatzResearch.WordTrace]
  refine ⟨30202194110047550519286937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40269592146730067359049249 30202194110047550519286937)
  ·
    refine ⟨22651645582535662889465203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30202194110047550519286937 22651645582535662889465203)
    ·
      refine ⟨33977468373803494334197805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22651645582535662889465203 33977468373803494334197805)
      ·
        refine ⟨12741550640176310375324177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33977468373803494334197805 12741550640176310375324177)
        ·
          refine ⟨9556162980132232781493133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12741550640176310375324177 9556162980132232781493133)
          ·
            refine ⟨3583561117549587293059925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9556162980132232781493133 3583561117549587293059925)
            ·
              refine ⟨20997428423142113045273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3583561117549587293059925 20997428423142113045273)
              ·
                rfl

theorem cell22_1656140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 9].length) (baseStart_1656140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656140 prefixEnd_1656140 := by exact prefixLift 1656140
  have htrace : WordTrace (prefixWord ++ tailWord_1656140) baseStart_1656140 baseEnd_1656140 := by
    simpa [prefixWord, tailWord_1656140, baseEnd_1656140] using wordTrace_append hprefix tailTrace_1656140
  have hstable : (prefixWord ++ tailWord_1656140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656140).length < 2 ^ (prefixWord ++ tailWord_1656140).sum := by decide
  have hdescent : baseEnd_1656140 < baseStart_1656140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656174 : List Nat := [4, 1, 2, 4, 1, 1, 1, 8]
def baseStart_1656174 : Nat := 118140960795 + 1656174 * 2 ^ 59
def prefixEnd_1656174 : Nat := 4983230072969 + 3 ^ 40 * 1656174 * 2
def baseEnd_1656174 : Nat := 62993578479963588541363

theorem tailTrace_1656174 : CollatzResearch.WordTrace tailWord_1656174 prefixEnd_1656174 62993578479963588541363 := by
  unfold tailWord_1656174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550703537746490605663947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40270418867981283230207717 7550703537746490605663947)
  ·
    refine ⟨11326055306619735908495921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7550703537746490605663947 11326055306619735908495921)
    ·
      refine ⟨8494541479964801931371941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11326055306619735908495921 8494541479964801931371941)
      ·
        refine ⟨1592726527493400362132239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8494541479964801931371941 1592726527493400362132239)
        ·
          refine ⟨2389089791240100543198359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592726527493400362132239 2389089791240100543198359)
          ·
            refine ⟨3583634686860150814797539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389089791240100543198359 3583634686860150814797539)
            ·
              refine ⟨5375452030290226222196309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583634686860150814797539 5375452030290226222196309)
              ·
                refine ⟨62993578479963588541363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5375452030290226222196309 62993578479963588541363)
                ·
                  rfl

theorem cell22_1656174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_1656174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656174 prefixEnd_1656174 := by exact prefixLift 1656174
  have htrace : WordTrace (prefixWord ++ tailWord_1656174) baseStart_1656174 baseEnd_1656174 := by
    simpa [prefixWord, tailWord_1656174, baseEnd_1656174] using wordTrace_append hprefix tailTrace_1656174
  have hstable : (prefixWord ++ tailWord_1656174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656174).length < 2 ^ (prefixWord ++ tailWord_1656174).sum := by decide
  have hdescent : baseEnd_1656174 < baseStart_1656174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656185 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 7]
def baseStart_1656185 : Nat := 118140960795 + 1656185 * 2 ^ 59
def prefixEnd_1656185 : Nat := 4983230072969 + 3 ^ 40 * 1656185 * 2
def baseEnd_1656185 : Nat := 188981990614823978282411

theorem tailTrace_1656185 : CollatzResearch.WordTrace tailWord_1656185 prefixEnd_1656185 188981990614823978282411 := by
  unfold tailWord_1656185
  simp only [CollatzResearch.WordTrace]
  refine ⟨60406029504932073723962009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40270686336621382482641339 60406029504932073723962009)
  ·
    refine ⟨45304522128699055292971507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60406029504932073723962009 45304522128699055292971507)
    ·
      refine ⟨67956783193048582939457261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45304522128699055292971507 67956783193048582939457261)
      ·
        refine ⟨25483793697393218602296473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67956783193048582939457261 25483793697393218602296473)
        ·
          refine ⟨19112845273044913951722355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25483793697393218602296473 19112845273044913951722355)
          ·
            refine ⟨28669267909567370927583533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19112845273044913951722355 28669267909567370927583533)
            ·
              refine ⟨10750975466087764097843825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28669267909567370927583533 10750975466087764097843825)
              ·
                refine ⟨8063231599565823073382869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10750975466087764097843825 8063231599565823073382869)
                ·
                  refine ⟨188981990614823978282411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8063231599565823073382869 188981990614823978282411)
                  ·
                    rfl

theorem cell22_1656185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_1656185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656185 prefixEnd_1656185 := by exact prefixLift 1656185
  have htrace : WordTrace (prefixWord ++ tailWord_1656185) baseStart_1656185 baseEnd_1656185 := by
    simpa [prefixWord, tailWord_1656185, baseEnd_1656185] using wordTrace_append hprefix tailTrace_1656185
  have hstable : (prefixWord ++ tailWord_1656185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656185).length < 2 ^ (prefixWord ++ tailWord_1656185).sum := by decide
  have hdescent : baseEnd_1656185 < baseStart_1656185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656215 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1656215 : Nat := 118140960795 + 1656215 * 2 ^ 59
def prefixEnd_1656215 : Nat := 4983230072969 + 3 ^ 40 * 1656215 * 2
def baseEnd_1656215 : Nat := 566956241457561856597141

theorem tailTrace_1656215 : CollatzResearch.WordTrace tailWord_1656215 prefixEnd_1656215 566956241457561856597141 := by
  unfold tailWord_1656215
  simp only [CollatzResearch.WordTrace]
  refine ⟨60407123694823388847554099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40271415796548925898369399 60407123694823388847554099)
  ·
    refine ⟨90610685542235083271331149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60407123694823388847554099 90610685542235083271331149)
    ·
      refine ⟨33979007078338156226749181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90610685542235083271331149 33979007078338156226749181)
      ·
        refine ⟨12742127654376808585030943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33979007078338156226749181 12742127654376808585030943)
        ·
          refine ⟨19113191481565212877546415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12742127654376808585030943 19113191481565212877546415)
          ·
            refine ⟨28669787222347819316319623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19113191481565212877546415 28669787222347819316319623)
            ·
              refine ⟨43004680833521728974479435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28669787222347819316319623 43004680833521728974479435)
              ·
                refine ⟨64507021250282593461719153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43004680833521728974479435 64507021250282593461719153)
                ·
                  refine ⟨48380265937711945096289365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64507021250282593461719153 48380265937711945096289365)
                  ·
                    refine ⟨566956241457561856597141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48380265937711945096289365 566956241457561856597141)
                    ·
                      rfl

theorem cell22_1656215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1656215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656215 prefixEnd_1656215 := by exact prefixLift 1656215
  have htrace : WordTrace (prefixWord ++ tailWord_1656215) baseStart_1656215 baseEnd_1656215 := by
    simpa [prefixWord, tailWord_1656215, baseEnd_1656215] using wordTrace_append hprefix tailTrace_1656215
  have hstable : (prefixWord ++ tailWord_1656215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656215).length < 2 ^ (prefixWord ++ tailWord_1656215).sum := by decide
  have hdescent : baseEnd_1656215 < baseStart_1656215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656264 : List Nat := [2, 1, 3, 1, 3, 1, 3, 4, 4]
def baseStart_1656264 : Nat := 118140960795 + 1656264 * 2 ^ 59
def prefixEnd_1656264 : Nat := 4983230072969 + 3 ^ 40 * 1656264 * 2
def baseEnd_1656264 : Nat := 188991005052980687373997

theorem tailTrace_1656264 : CollatzResearch.WordTrace tailWord_1656264 prefixEnd_1656264 188991005052980687373997 := by
  unfold tailWord_1656264
  simp only [CollatzResearch.WordTrace]
  refine ⟨30204455435822935108043923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40272607247763913477391897 30204455435822935108043923)
  ·
    refine ⟨45306683153734402662065885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30204455435822935108043923 45306683153734402662065885)
    ·
      refine ⟨16990006182650400998274707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45306683153734402662065885 16990006182650400998274707)
      ·
        refine ⟨25485009273975601497412061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16990006182650400998274707 25485009273975601497412061)
        ·
          refine ⟨9556878477740850561529523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25485009273975601497412061 9556878477740850561529523)
          ·
            refine ⟨14335317716611275842294285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9556878477740850561529523 14335317716611275842294285)
            ·
              refine ⟨5375744143729228440860357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14335317716611275842294285 5375744143729228440860357)
              ·
                refine ⟨1007952026949230332661317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5375744143729228440860357 1007952026949230332661317)
                ·
                  refine ⟨188991005052980687373997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007952026949230332661317 188991005052980687373997)
                  ·
                    rfl

theorem cell22_1656264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 4].length) (baseStart_1656264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656264 prefixEnd_1656264 := by exact prefixLift 1656264
  have htrace : WordTrace (prefixWord ++ tailWord_1656264) baseStart_1656264 baseEnd_1656264 := by
    simpa [prefixWord, tailWord_1656264, baseEnd_1656264] using wordTrace_append hprefix tailTrace_1656264
  have hstable : (prefixWord ++ tailWord_1656264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656264).length < 2 ^ (prefixWord ++ tailWord_1656264).sum := by decide
  have hdescent : baseEnd_1656264 < baseStart_1656264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656277 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1656277 : Nat := 118140960795 + 1656277 * 2 ^ 59
def prefixEnd_1656277 : Nat := 4983230072969 + 3 ^ 40 * 1656277 * 2
def baseEnd_1656277 : Nat := 566977465324614361546951

theorem tailTrace_1656277 : CollatzResearch.WordTrace tailWord_1656277 prefixEnd_1656277 566977465324614361546951 := by
  unfold tailWord_1656277
  simp only [CollatzResearch.WordTrace]
  refine ⟨60409385020598773436311085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40272923347065848957540723 60409385020598773436311085)
  ·
    refine ⟨22653519382724540038616657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60409385020598773436311085 22653519382724540038616657)
    ·
      refine ⟨16990139537043405028962493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22653519382724540038616657 16990139537043405028962493)
      ·
        refine ⟨6371302326391276885860935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16990139537043405028962493 6371302326391276885860935)
        ·
          refine ⟨9556953489586915328791403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6371302326391276885860935 9556953489586915328791403)
          ·
            refine ⟨14335430234380372993187105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9556953489586915328791403 14335430234380372993187105)
            ·
              refine ⟨10751572675785279744890329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14335430234380372993187105 10751572675785279744890329)
              ·
                refine ⟨8063679506838959808667747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10751572675785279744890329 8063679506838959808667747)
                ·
                  refine ⟨12095519260258439713001621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8063679506838959808667747 12095519260258439713001621)
                  ·
                    refine ⟨566977465324614361546951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12095519260258439713001621 566977465324614361546951)
                    ·
                      rfl

theorem cell22_1656277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1656277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656277 prefixEnd_1656277 := by exact prefixLift 1656277
  have htrace : WordTrace (prefixWord ++ tailWord_1656277) baseStart_1656277 baseEnd_1656277 := by
    simpa [prefixWord, tailWord_1656277, baseEnd_1656277] using wordTrace_append hprefix tailTrace_1656277
  have hstable : (prefixWord ++ tailWord_1656277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656277).length < 2 ^ (prefixWord ++ tailWord_1656277).sum := by decide
  have hdescent : baseEnd_1656277 < baseStart_1656277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656309 : List Nat := [1, 3, 5, 1, 1, 2, 9]
def baseStart_1656309 : Nat := 118140960795 + 1656309 * 2 ^ 59
def prefixEnd_1656309 : Nat := 4983230072969 + 3 ^ 40 * 1656309 * 2
def baseEnd_1656309 : Nat := 20999571095502849805439

theorem tailTrace_1656309 : CollatzResearch.WordTrace tailWord_1656309 prefixEnd_1656309 20999571095502849805439 := by
  unfold tailWord_1656309
  simp only [CollatzResearch.WordTrace]
  refine ⟨60410552156482842901475981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40273701437655228600983987 60410552156482842901475981)
  ·
    refine ⟨22653957058681066088053493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60410552156482842901475981 22653957058681066088053493)
    ·
      refine ⟨2123808474251349945755015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22653957058681066088053493 2123808474251349945755015)
      ·
        refine ⟨3185712711377024918632523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123808474251349945755015 3185712711377024918632523)
        ·
          refine ⟨4778569067065537377948785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185712711377024918632523 4778569067065537377948785)
          ·
            refine ⟨3583926800299153033461589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4778569067065537377948785 3583926800299153033461589)
            ·
              refine ⟨20999571095502849805439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3583926800299153033461589 20999571095502849805439)
              ·
                rfl

theorem cell22_1656309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 9].length) (baseStart_1656309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656309 prefixEnd_1656309 := by exact prefixLift 1656309
  have htrace : WordTrace (prefixWord ++ tailWord_1656309) baseStart_1656309 baseEnd_1656309 := by
    simpa [prefixWord, tailWord_1656309, baseEnd_1656309] using wordTrace_append hprefix tailTrace_1656309
  have hstable : (prefixWord ++ tailWord_1656309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656309).length < 2 ^ (prefixWord ++ tailWord_1656309).sum := by decide
  have hdescent : baseEnd_1656309 < baseStart_1656309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656482 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1656482 : Nat := 118140960795 + 1656482 * 2 ^ 59
def prefixEnd_1656482 : Nat := 4983230072969 + 3 ^ 40 * 1656482 * 2
def baseEnd_1656482 : Nat := 567047641014062160171323

theorem tailTrace_1656482 : CollatzResearch.WordTrace tailWord_1656482 prefixEnd_1656482 567047641014062160171323 := by
  unfold tailWord_1656482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15104215496214023361880925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40277907989904062298349133 15104215496214023361880925)
  ·
    refine ⟨5664080811080258760705347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15104215496214023361880925 5664080811080258760705347)
    ·
      refine ⟨8496121216620388141058021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5664080811080258760705347 8496121216620388141058021)
      ·
        refine ⟨1593022728116322776448379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8496121216620388141058021 1593022728116322776448379)
        ·
          refine ⟨2389534092174484164672569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593022728116322776448379 2389534092174484164672569)
          ·
            refine ⟨1792150569130863123504427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2389534092174484164672569 1792150569130863123504427)
            ·
              refine ⟨2688225853696294685256641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792150569130863123504427 2688225853696294685256641)
              ·
                refine ⟨2016169390272221013942481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2688225853696294685256641 2016169390272221013942481)
                ·
                  refine ⟨1512127042704165760456861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2016169390272221013942481 1512127042704165760456861)
                  ·
                    refine ⟨567047641014062160171323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1512127042704165760456861 567047641014062160171323)
                    ·
                      rfl

theorem cell22_1656482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1656482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656482 prefixEnd_1656482 := by exact prefixLift 1656482
  have htrace : WordTrace (prefixWord ++ tailWord_1656482) baseStart_1656482 baseEnd_1656482 := by
    simpa [prefixWord, tailWord_1656482, baseEnd_1656482] using wordTrace_append hprefix tailTrace_1656482
  have hstable : (prefixWord ++ tailWord_1656482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656482).length < 2 ^ (prefixWord ++ tailWord_1656482).sum := by decide
  have hdescent : baseEnd_1656482 < baseStart_1656482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656493 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1656493 : Nat := 118140960795 + 1656493 * 2 ^ 59
def prefixEnd_1656493 : Nat := 4983230072969 + 3 ^ 40 * 1656493 * 2
def baseEnd_1656493 : Nat := 567051406538861798146289

theorem tailTrace_1656493 : CollatzResearch.WordTrace tailWord_1656493 prefixEnd_1656493 567051406538861798146289 := by
  unfold tailWord_1656493
  simp only [CollatzResearch.WordTrace]
  refine ⟨60417263187816242326174133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40278175458544161550782755 60417263187816242326174133)
  ·
    refine ⟨5664118423857772718078825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60417263187816242326174133 5664118423857772718078825)
    ·
      refine ⟨4248088817893329538559119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5664118423857772718078825 4248088817893329538559119)
      ·
        refine ⟨6372133226839994307838679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248088817893329538559119 6372133226839994307838679)
        ·
          refine ⟨9558199840259991461758019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372133226839994307838679 9558199840259991461758019)
          ·
            refine ⟨14337299760389987192637029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9558199840259991461758019 14337299760389987192637029)
            ·
              refine ⟨2688243705073122598619443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14337299760389987192637029 2688243705073122598619443)
              ·
                refine ⟨4032365557609683897929165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688243705073122598619443 4032365557609683897929165)
                ·
                  refine ⟨1512137084103631461723437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4032365557609683897929165 1512137084103631461723437)
                  ·
                    refine ⟨567051406538861798146289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1512137084103631461723437 567051406538861798146289)
                    ·
                      rfl

theorem cell22_1656493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1656493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656493 prefixEnd_1656493 := by exact prefixLift 1656493
  have htrace : WordTrace (prefixWord ++ tailWord_1656493) baseStart_1656493 baseEnd_1656493 := by
    simpa [prefixWord, tailWord_1656493, baseEnd_1656493] using wordTrace_append hprefix tailTrace_1656493
  have hstable : (prefixWord ++ tailWord_1656493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656493).length < 2 ^ (prefixWord ++ tailWord_1656493).sum := by decide
  have hdescent : baseEnd_1656493 < baseStart_1656493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656536 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_1656536 : Nat := 118140960795 + 1656536 * 2 ^ 59
def prefixEnd_1656536 : Nat := 4983230072969 + 3 ^ 40 * 1656536 * 2
def baseEnd_1656536 : Nat := 567066126317624019321157

theorem tailTrace_1656536 : CollatzResearch.WordTrace tailWord_1656536 prefixEnd_1656536 567066126317624019321157 := by
  unfold tailWord_1656536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30209415763330230334994731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40279221017773640446659641 30209415763330230334994731)
  ·
    refine ⟨45314123644995345502492097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30209415763330230334994731 45314123644995345502492097)
    ·
      refine ⟨33985592733746509126869073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45314123644995345502492097 33985592733746509126869073)
      ·
        refine ⟨25489194550309881845151805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33985592733746509126869073 25489194550309881845151805)
        ·
          refine ⟨9558447956366205691931927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25489194550309881845151805 9558447956366205691931927)
          ·
            refine ⟨14337671934549308537897891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9558447956366205691931927 14337671934549308537897891)
            ·
              refine ⟨21506507901823962806846837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14337671934549308537897891 21506507901823962806846837)
              ·
                refine ⟨2016235115795996513141891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21506507901823962806846837 2016235115795996513141891)
                ·
                  refine ⟨3024352673693994769712837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016235115795996513141891 3024352673693994769712837)
                  ·
                    refine ⟨567066126317624019321157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3024352673693994769712837 567066126317624019321157)
                    ·
                      rfl

theorem cell22_1656536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_1656536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656536 prefixEnd_1656536 := by exact prefixLift 1656536
  have htrace : WordTrace (prefixWord ++ tailWord_1656536) baseStart_1656536 baseEnd_1656536 := by
    simpa [prefixWord, tailWord_1656536, baseEnd_1656536] using wordTrace_append hprefix tailTrace_1656536
  have hstable : (prefixWord ++ tailWord_1656536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656536).length < 2 ^ (prefixWord ++ tailWord_1656536).sum := by decide
  have hdescent : baseEnd_1656536 < baseStart_1656536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656579 : List Nat := [1, 1, 1, 3, 2, 2, 4, 8]
def baseStart_1656579 : Nat := 118140960795 + 1656579 * 2 ^ 59
def prefixEnd_1656579 : Nat := 4983230072969 + 3 ^ 40 * 1656579 * 2
def baseEnd_1656579 : Nat := 63008982899598471166225

theorem tailTrace_1656579 : CollatzResearch.WordTrace tailWord_1656579 prefixEnd_1656579 63008982899598471166225 := by
  unfold tailWord_1656579
  simp only [CollatzResearch.WordTrace]
  refine ⟨60420399865504679013804791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40280266577003119342536527 60420399865504679013804791)
  ·
    refine ⟨90630599798257018520707187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60420399865504679013804791 90630599798257018520707187)
    ·
      refine ⟨135945899697385527781060781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90630599798257018520707187 135945899697385527781060781)
      ·
        refine ⟨50979712386519572917897793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135945899697385527781060781 50979712386519572917897793)
        ·
          refine ⟨38234784289889679688423345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50979712386519572917897793 38234784289889679688423345)
          ·
            refine ⟨28676088217417259766317509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38234784289889679688423345 28676088217417259766317509)
            ·
              refine ⟨5376766540765736206184533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28676088217417259766317509 5376766540765736206184533)
              ·
                refine ⟨63008982899598471166225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5376766540765736206184533 63008982899598471166225)
                ·
                  rfl

theorem cell22_1656579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 8].length) (baseStart_1656579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656579 prefixEnd_1656579 := by exact prefixLift 1656579
  have htrace : WordTrace (prefixWord ++ tailWord_1656579) baseStart_1656579 baseEnd_1656579 := by
    simpa [prefixWord, tailWord_1656579, baseEnd_1656579] using wordTrace_append hprefix tailTrace_1656579
  have hstable : (prefixWord ++ tailWord_1656579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656579).length < 2 ^ (prefixWord ++ tailWord_1656579).sum := by decide
  have hdescent : baseEnd_1656579 < baseStart_1656579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656583 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1656583 : Nat := 118140960795 + 1656583 * 2 ^ 59
def prefixEnd_1656583 : Nat := 4983230072969 + 3 ^ 40 * 1656583 * 2
def baseEnd_1656583 : Nat := 567082215378131563396013

theorem tailTrace_1656583 : CollatzResearch.WordTrace tailWord_1656583 prefixEnd_1656583 567082215378131563396013 := by
  unfold tailWord_1656583
  simp only [CollatzResearch.WordTrace]
  refine ⟨60420545757490187696950403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40280363838326791797966935 60420545757490187696950403)
  ·
    refine ⟨90630818636235281545425605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60420545757490187696950403 90630818636235281545425605)
    ·
      refine ⟨16993278494294115289767301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90630818636235281545425605 16993278494294115289767301)
      ·
        refine ⟨3186239717680146616831369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16993278494294115289767301 3186239717680146616831369)
        ·
          refine ⟨2389679788260109962623527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3186239717680146616831369 2389679788260109962623527)
          ·
            refine ⟨3584519682390164943935291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389679788260109962623527 3584519682390164943935291)
            ·
              refine ⟨5376779523585247415902937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584519682390164943935291 5376779523585247415902937)
              ·
                refine ⟨4032584642688935561927203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5376779523585247415902937 4032584642688935561927203)
                ·
                  refine ⟨6048876964033403342890805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032584642688935561927203 6048876964033403342890805)
                  ·
                    refine ⟨567082215378131563396013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6048876964033403342890805 567082215378131563396013)
                    ·
                      rfl

theorem cell22_1656583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1656583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656583 prefixEnd_1656583 := by exact prefixLift 1656583
  have htrace : WordTrace (prefixWord ++ tailWord_1656583) baseStart_1656583 baseEnd_1656583 := by
    simpa [prefixWord, tailWord_1656583, baseEnd_1656583] using wordTrace_append hprefix tailTrace_1656583
  have hstable : (prefixWord ++ tailWord_1656583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656583).length < 2 ^ (prefixWord ++ tailWord_1656583).sum := by decide
  have hdescent : baseEnd_1656583 < baseStart_1656583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656624 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 11]
def baseStart_1656624 : Nat := 118140960795 + 1656624 * 2 ^ 59
def prefixEnd_1656624 : Nat := 4983230072969 + 3 ^ 40 * 1656624 * 2
def baseEnd_1656624 : Nat := 189032083505340374373629

theorem tailTrace_1656624 : CollatzResearch.WordTrace tailWord_1656624 prefixEnd_1656624 189032083505340374373629 := by
  unfold tailWord_1656624
  simp only [CollatzResearch.WordTrace]
  refine ⟨30211020575170825849596463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40281360766894434466128617 30211020575170825849596463)
  ·
    refine ⟨45316530862756238774394695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30211020575170825849596463 45316530862756238774394695)
    ·
      refine ⟨67974796294134358161592043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45316530862756238774394695 67974796294134358161592043)
      ·
        refine ⟨101962194441201537242388065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67974796294134358161592043 101962194441201537242388065)
        ·
          refine ⟨76471645830901152931791049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101962194441201537242388065 76471645830901152931791049)
          ·
            refine ⟨57353734373175864698843287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76471645830901152931791049 57353734373175864698843287)
            ·
              refine ⟨86030601559763797048264931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57353734373175864698843287 86030601559763797048264931)
              ·
                refine ⟨129045902339645695572397397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86030601559763797048264931 129045902339645695572397397)
                ·
                  refine ⟨189032083505340374373629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 129045902339645695572397397 189032083505340374373629)
                  ·
                    rfl

theorem cell22_1656624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_1656624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656624 prefixEnd_1656624 := by exact prefixLift 1656624
  have htrace : WordTrace (prefixWord ++ tailWord_1656624) baseStart_1656624 baseEnd_1656624 := by
    simpa [prefixWord, tailWord_1656624, baseEnd_1656624] using wordTrace_append hprefix tailTrace_1656624
  have hstable : (prefixWord ++ tailWord_1656624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656624).length < 2 ^ (prefixWord ++ tailWord_1656624).sum := by decide
  have hdescent : baseEnd_1656624 < baseStart_1656624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656630 : List Nat := [5, 1, 2, 2, 1, 2, 3, 6]
def baseStart_1656630 : Nat := 118140960795 + 1656630 * 2 ^ 59
def prefixEnd_1656630 : Nat := 4983230072969 + 3 ^ 40 * 1656630 * 2
def baseEnd_1656630 : Nat := 63010922715404345274541

theorem tailTrace_1656630 : CollatzResearch.WordTrace tailWord_1656630 prefixEnd_1656630 63010922715404345274541 := by
  unfold tailWord_1656630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776391249269994670244459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40281506658879943149274229 3776391249269994670244459)
  ·
    refine ⟨5664586873904992005366689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3776391249269994670244459 5664586873904992005366689)
    ·
      refine ⟨4248440155428744004025017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5664586873904992005366689 4248440155428744004025017)
      ·
        refine ⟨3186330116571558003018763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4248440155428744004025017 3186330116571558003018763)
        ·
          refine ⟨4779495174857337004528145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186330116571558003018763 4779495174857337004528145)
          ·
            refine ⟨3584621381143002753396109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4779495174857337004528145 3584621381143002753396109)
            ·
              refine ⟨1344233017928626032523541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3584621381143002753396109 1344233017928626032523541)
              ·
                refine ⟨63010922715404345274541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1344233017928626032523541 63010922715404345274541)
                ·
                  rfl

theorem cell22_1656630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_1656630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656630 prefixEnd_1656630 := by exact prefixLift 1656630
  have htrace : WordTrace (prefixWord ++ tailWord_1656630) baseStart_1656630 baseEnd_1656630 := by
    simpa [prefixWord, tailWord_1656630, baseEnd_1656630] using wordTrace_append hprefix tailTrace_1656630
  have hstable : (prefixWord ++ tailWord_1656630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656630).length < 2 ^ (prefixWord ++ tailWord_1656630).sum := by decide
  have hdescent : baseEnd_1656630 < baseStart_1656630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656645 : List Nat := [1, 3, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_1656645 : Nat := 118140960795 + 1656645 * 2 ^ 59
def prefixEnd_1656645 : Nat := 4983230072969 + 3 ^ 40 * 1656645 * 2
def baseEnd_1656645 : Nat := 567103439245184068345823

theorem tailTrace_1656645 : CollatzResearch.WordTrace tailWord_1656645 prefixEnd_1656645 567103439245184068345823 := by
  unfold tailWord_1656645
  simp only [CollatzResearch.WordTrace]
  refine ⟨60422807083265572285707389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40281871388843714857138259 60422807083265572285707389)
  ·
    refine ⟨22658552656224589607140271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60422807083265572285707389 22658552656224589607140271)
    ·
      refine ⟨33987828984336884410710407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22658552656224589607140271 33987828984336884410710407)
      ·
        refine ⟨50981743476505326616065611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33987828984336884410710407 50981743476505326616065611)
        ·
          refine ⟨76472615214757989924098417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50981743476505326616065611 76472615214757989924098417)
          ·
            refine ⟨57354461411068492443073813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76472615214757989924098417 57354461411068492443073813)
            ·
              refine ⟨2688490378643835583269085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57354461411068492443073813 2688490378643835583269085)
              ·
                refine ⟨1008183891991438343725907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2688490378643835583269085 1008183891991438343725907)
                ·
                  refine ⟨1512275837987157515588861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008183891991438343725907 1512275837987157515588861)
                  ·
                    refine ⟨567103439245184068345823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1512275837987157515588861 567103439245184068345823)
                    ·
                      rfl

theorem cell22_1656645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_1656645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656645 prefixEnd_1656645 := by exact prefixLift 1656645
  have htrace : WordTrace (prefixWord ++ tailWord_1656645) baseStart_1656645 baseEnd_1656645 := by
    simpa [prefixWord, tailWord_1656645, baseEnd_1656645] using wordTrace_append hprefix tailTrace_1656645
  have hstable : (prefixWord ++ tailWord_1656645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656645).length < 2 ^ (prefixWord ++ tailWord_1656645).sum := by decide
  have hdescent : baseEnd_1656645 < baseStart_1656645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656658 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_1656658 : Nat := 118140960795 + 1656658 * 2 ^ 59
def prefixEnd_1656658 : Nat := 4983230072969 + 3 ^ 40 * 1656658 * 2
def baseEnd_1656658 : Nat := 189035963136952122590261

theorem tailTrace_1656658 : CollatzResearch.WordTrace tailWord_1656658 prefixEnd_1656658 189035963136952122590261 := by
  unfold tailWord_1656658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15105820308054618876482657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40282187488145650337287085 15105820308054618876482657)
  ·
    refine ⟨11329365231040964157361993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15105820308054618876482657 11329365231040964157361993)
    ·
      refine ⟨8497023923280723118021495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11329365231040964157361993 8497023923280723118021495)
      ·
        refine ⟨12745535884921084677032243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8497023923280723118021495 12745535884921084677032243)
        ·
          refine ⟨19118303827381627015548365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12745535884921084677032243 19118303827381627015548365)
          ·
            refine ⟨7169363935268110130830637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19118303827381627015548365 7169363935268110130830637)
            ·
              refine ⟨2688511475725541299061489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7169363935268110130830637 2688511475725541299061489)
              ·
                refine ⟨2016383606794155974296117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2688511475725541299061489 2016383606794155974296117)
                ·
                  refine ⟨189035963136952122590261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016383606794155974296117 189035963136952122590261)
                  ·
                    rfl

theorem cell22_1656658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1656658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656658 prefixEnd_1656658 := by exact prefixLift 1656658
  have htrace : WordTrace (prefixWord ++ tailWord_1656658) baseStart_1656658 baseEnd_1656658 := by
    simpa [prefixWord, tailWord_1656658, baseEnd_1656658] using wordTrace_append hprefix tailTrace_1656658
  have hstable : (prefixWord ++ tailWord_1656658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656658).length < 2 ^ (prefixWord ++ tailWord_1656658).sum := by decide
  have hdescent : baseEnd_1656658 < baseStart_1656658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656675 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 5]
def baseStart_1656675 : Nat := 118140960795 + 1656675 * 2 ^ 59
def prefixEnd_1656675 : Nat := 4983230072969 + 3 ^ 40 * 1656675 * 2
def baseEnd_1656675 : Nat := 189037902952757996698577

theorem tailTrace_1656675 : CollatzResearch.WordTrace tailWord_1656675 prefixEnd_1656675 189037902952757996698577 := by
  unfold tailWord_1656675
  simp only [CollatzResearch.WordTrace]
  refine ⟨60423901273156887409299479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40282600848771258272866319 60423901273156887409299479)
  ·
    refine ⟨90635851909735331113949219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60423901273156887409299479 90635851909735331113949219)
    ·
      refine ⟨135953777864602996670923829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90635851909735331113949219 135953777864602996670923829)
      ·
        refine ⟨12745666674806530937899109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135953777864602996670923829 12745666674806530937899109)
        ·
          refine ⟨2389812501526224550856083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12745666674806530937899109 2389812501526224550856083)
          ·
            refine ⟨3584718752289336826284125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389812501526224550856083 3584718752289336826284125)
            ·
              refine ⟨1344269532108501309856547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3584718752289336826284125 1344269532108501309856547)
              ·
                refine ⟨2016404298162751964784821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344269532108501309856547 2016404298162751964784821)
                ·
                  refine ⟨189037902952757996698577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016404298162751964784821 189037902952757996698577)
                  ·
                    rfl

theorem cell22_1656675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 5].length) (baseStart_1656675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656675 prefixEnd_1656675 := by exact prefixLift 1656675
  have htrace : WordTrace (prefixWord ++ tailWord_1656675) baseStart_1656675 baseEnd_1656675 := by
    simpa [prefixWord, tailWord_1656675, baseEnd_1656675] using wordTrace_append hprefix tailTrace_1656675
  have hstable : (prefixWord ++ tailWord_1656675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656675).length < 2 ^ (prefixWord ++ tailWord_1656675).sum := by decide
  have hdescent : baseEnd_1656675 < baseStart_1656675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656701 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1656701 : Nat := 118140960795 + 1656701 * 2 ^ 59
def prefixEnd_1656701 : Nat := 4983230072969 + 3 ^ 40 * 1656701 * 2
def baseEnd_1656701 : Nat := 567122609189618588945651

theorem tailTrace_1656701 : CollatzResearch.WordTrace tailWord_1656701 prefixEnd_1656701 567122609189618588945651 := by
  unfold tailWord_1656701
  simp only [CollatzResearch.WordTrace]
  refine ⟨60424849571062693849745957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40283233047375129233163971 60424849571062693849745957)
  ·
    refine ⟨11329659294574255096827367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60424849571062693849745957 11329659294574255096827367)
    ·
      refine ⟨16994488941861382645241051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11329659294574255096827367 16994488941861382645241051)
      ·
        refine ⟨25491733412792073967861577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16994488941861382645241051 25491733412792073967861577)
        ·
          refine ⟨19118800059594055475896183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25491733412792073967861577 19118800059594055475896183)
          ·
            refine ⟨28678200089391083213844275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19118800059594055475896183 28678200089391083213844275)
            ·
              refine ⟨43017300134086624820766413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28678200089391083213844275 43017300134086624820766413)
              ·
                refine ⟨16131487550282484307787405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43017300134086624820766413 16131487550282484307787405)
                ·
                  refine ⟨6049307831355931615420277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16131487550282484307787405 6049307831355931615420277)
                  ·
                    refine ⟨567122609189618588945651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6049307831355931615420277 567122609189618588945651)
                    ·
                      rfl

theorem cell22_1656701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1656701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656701 prefixEnd_1656701 := by exact prefixLift 1656701
  have htrace : WordTrace (prefixWord ++ tailWord_1656701) baseStart_1656701 baseEnd_1656701 := by
    simpa [prefixWord, tailWord_1656701, baseEnd_1656701] using wordTrace_append hprefix tailTrace_1656701
  have hstable : (prefixWord ++ tailWord_1656701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656701).length < 2 ^ (prefixWord ++ tailWord_1656701).sum := by decide
  have hdescent : baseEnd_1656701 < baseStart_1656701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656726 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1656726 : Nat := 118140960795 + 1656726 * 2 ^ 59
def prefixEnd_1656726 : Nat := 4983230072969 + 3 ^ 40 * 1656726 * 2
def baseEnd_1656726 : Nat := 189043722400175619023525

theorem tailTrace_1656726 : CollatzResearch.WordTrace tailWord_1656726 prefixEnd_1656726 189043722400175619023525 := by
  unfold tailWord_1656726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776610087248257694962877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40283840930648082079604021 3776610087248257694962877)
  ·
    refine ⟨1416228782718096635611079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3776610087248257694962877 1416228782718096635611079)
    ·
      refine ⟨2124343174077144953416619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1416228782718096635611079 2124343174077144953416619)
      ·
        refine ⟨3186514761115717430124929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124343174077144953416619 3186514761115717430124929)
        ·
          refine ⟨2389886070836788072593697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3186514761115717430124929 2389886070836788072593697)
          ·
            refine ⟨1792414553127591054445273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2389886070836788072593697 1792414553127591054445273)
            ·
              refine ⟨1344310914845693290833955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792414553127591054445273 1344310914845693290833955)
              ·
                refine ⟨2016466372268539936250933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344310914845693290833955 2016466372268539936250933)
                ·
                  refine ⟨189043722400175619023525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016466372268539936250933 189043722400175619023525)
                  ·
                    rfl

theorem cell22_1656726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1656726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656726 prefixEnd_1656726 := by exact prefixLift 1656726
  have htrace : WordTrace (prefixWord ++ tailWord_1656726) baseStart_1656726 baseEnd_1656726 := by
    simpa [prefixWord, tailWord_1656726, baseEnd_1656726] using wordTrace_append hprefix tailTrace_1656726
  have hstable : (prefixWord ++ tailWord_1656726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656726).length < 2 ^ (prefixWord ++ tailWord_1656726).sum := by decide
  have hdescent : baseEnd_1656726 < baseStart_1656726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656797 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1656797 : Nat := 118140960795 + 1656797 * 2 ^ 59
def prefixEnd_1656797 : Nat := 4983230072969 + 3 ^ 40 * 1656797 * 2
def baseEnd_1656797 : Nat := 567155471951506338545357

theorem tailTrace_1656797 : CollatzResearch.WordTrace tailWord_1656797 prefixEnd_1656797 567155471951506338545357 := by
  unfold tailWord_1656797
  simp only [CollatzResearch.WordTrace]
  refine ⟨60428350978714902245240645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40285567319143268163493763 60428350978714902245240645)
  ·
    refine ⟨11330315808509044170982621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60428350978714902245240645 11330315808509044170982621)
    ·
      refine ⟨4248868428190891564118483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11330315808509044170982621 4248868428190891564118483)
      ·
        refine ⟨6373302642286337346177725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248868428190891564118483 6373302642286337346177725)
        ·
          refine ⟨2389988490857376504816647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6373302642286337346177725 2389988490857376504816647)
          ·
            refine ⟨3584982736286064757224971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389988490857376504816647 3584982736286064757224971)
            ·
              refine ⟨5377474104429097135837457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584982736286064757224971 5377474104429097135837457)
              ·
                refine ⟨4033105578321822851878093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5377474104429097135837457 4033105578321822851878093)
                ·
                  refine ⟨1512414591870683569454285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4033105578321822851878093 1512414591870683569454285)
                  ·
                    refine ⟨567155471951506338545357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1512414591870683569454285 567155471951506338545357)
                    ·
                      rfl

theorem cell22_1656797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1656797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656797 prefixEnd_1656797 := by exact prefixLift 1656797
  have htrace : WordTrace (prefixWord ++ tailWord_1656797) baseStart_1656797 baseEnd_1656797 := by
    simpa [prefixWord, tailWord_1656797, baseEnd_1656797] using wordTrace_append hprefix tailTrace_1656797
  have hstable : (prefixWord ++ tailWord_1656797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656797).length < 2 ^ (prefixWord ++ tailWord_1656797).sum := by decide
  have hdescent : baseEnd_1656797 < baseStart_1656797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656814 : List Nat := [4, 1, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1656814 : Nat := 118140960795 + 1656814 * 2 ^ 59
def prefixEnd_1656814 : Nat := 4983230072969 + 3 ^ 40 * 1656814 * 2
def baseEnd_1656814 : Nat := 567161291398923960870305

theorem tailTrace_1656814 : CollatzResearch.WordTrace tailWord_1656814 prefixEnd_1656814 567161291398923960870305 := by
  unfold tailWord_1656814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7553621377456664268576187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40285980679768876099072997 7553621377456664268576187)
  ·
    refine ⟨11330432066184996402864281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7553621377456664268576187 11330432066184996402864281)
    ·
      refine ⟨8497824049638747302148211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11330432066184996402864281 8497824049638747302148211)
      ·
        refine ⟨12746736074458120953222317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8497824049638747302148211 12746736074458120953222317)
        ·
          refine ⟨4780026027921795357458369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12746736074458120953222317 4780026027921795357458369)
          ·
            refine ⟨3585019520941346518093777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4780026027921795357458369 3585019520941346518093777)
            ·
              refine ⟨2688764640706009888570333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3585019520941346518093777 2688764640706009888570333)
              ·
                refine ⟨1008286740264753708213875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2688764640706009888570333 1008286740264753708213875)
                ·
                  refine ⟨1512430110397130562320813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008286740264753708213875 1512430110397130562320813)
                  ·
                    refine ⟨567161291398923960870305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1512430110397130562320813 567161291398923960870305)
                    ·
                      rfl

theorem cell22_1656814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1656814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656814 prefixEnd_1656814 := by exact prefixLift 1656814
  have htrace : WordTrace (prefixWord ++ tailWord_1656814) baseStart_1656814 baseEnd_1656814 := by
    simpa [prefixWord, tailWord_1656814, baseEnd_1656814] using wordTrace_append hprefix tailTrace_1656814
  have hstable : (prefixWord ++ tailWord_1656814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656814).length < 2 ^ (prefixWord ++ tailWord_1656814).sum := by decide
  have hdescent : baseEnd_1656814 < baseStart_1656814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656889 : List Nat := [1, 2, 1, 5, 3, 1, 3, 2, 4]
def baseStart_1656889 : Nat := 118140960795 + 1656889 * 2 ^ 59
def prefixEnd_1656889 : Nat := 4983230072969 + 3 ^ 40 * 1656889 * 2
def baseEnd_1656889 : Nat := 189062321810549588415025

theorem tailTrace_1656889 : CollatzResearch.WordTrace tailWord_1656889 prefixEnd_1656889 189062321810549588415025 := by
  unfold tailWord_1656889
  simp only [CollatzResearch.WordTrace]
  refine ⟨60431706494381601957589721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40287804329587734638393147 60431706494381601957589721)
  ·
    refine ⟨45323779870786201468192291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60431706494381601957589721 45323779870786201468192291)
    ·
      refine ⟨67985669806179302202288437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45323779870786201468192291 67985669806179302202288437)
      ·
        refine ⟨6373656544329309581464541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67985669806179302202288437 6373656544329309581464541)
        ·
          refine ⟨2390121204123491093049203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6373656544329309581464541 2390121204123491093049203)
          ·
            refine ⟨3585181806185236639573805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390121204123491093049203 3585181806185236639573805)
            ·
              refine ⟨1344443177319463739840177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3585181806185236639573805 1344443177319463739840177)
              ·
                refine ⟨1008332382989597804880133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344443177319463739840177 1008332382989597804880133)
                ·
                  refine ⟨189062321810549588415025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1008332382989597804880133 189062321810549588415025)
                  ·
                    rfl

theorem cell22_1656889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 4].length) (baseStart_1656889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656889 prefixEnd_1656889 := by exact prefixLift 1656889
  have htrace : WordTrace (prefixWord ++ tailWord_1656889) baseStart_1656889 baseEnd_1656889 := by
    simpa [prefixWord, tailWord_1656889, baseEnd_1656889] using wordTrace_append hprefix tailTrace_1656889
  have hstable : (prefixWord ++ tailWord_1656889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656889).length < 2 ^ (prefixWord ++ tailWord_1656889).sum := by decide
  have hdescent : baseEnd_1656889 < baseStart_1656889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656902 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1656902 : Nat := 118140960795 + 1656902 * 2 ^ 59
def prefixEnd_1656902 : Nat := 4983230072969 + 3 ^ 40 * 1656902 * 2
def baseEnd_1656902 : Nat := 567191415597321064670035

theorem tailTrace_1656902 : CollatzResearch.WordTrace tailWord_1656902 prefixEnd_1656902 567191415597321064670035 := by
  unfold tailWord_1656902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888505645104203286806655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40288120428889670118541973 1888505645104203286806655)
  ·
    refine ⟨2832758467656304930209983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888505645104203286806655 2832758467656304930209983)
    ·
      refine ⟨4249137701484457395314975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832758467656304930209983 4249137701484457395314975)
      ·
        refine ⟨6373706552226686092972463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4249137701484457395314975 6373706552226686092972463)
        ·
          refine ⟨9560559828340029139458695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373706552226686092972463 9560559828340029139458695)
          ·
            refine ⟨14340839742510043709188043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9560559828340029139458695 14340839742510043709188043)
            ·
              refine ⟨21511259613765065563782065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14340839742510043709188043 21511259613765065563782065)
              ·
                refine ⟨16133444710323799172836549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21511259613765065563782065 16133444710323799172836549)
                ·
                  refine ⟨3025020883185712344906853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16133444710323799172836549 3025020883185712344906853)
                  ·
                    refine ⟨567191415597321064670035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025020883185712344906853 567191415597321064670035)
                    ·
                      rfl

theorem cell22_1656902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1656902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656902 prefixEnd_1656902 := by exact prefixLift 1656902
  have htrace : WordTrace (prefixWord ++ tailWord_1656902) baseStart_1656902 baseEnd_1656902 := by
    simpa [prefixWord, tailWord_1656902, baseEnd_1656902] using wordTrace_append hprefix tailTrace_1656902
  have hstable : (prefixWord ++ tailWord_1656902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656902).length < 2 ^ (prefixWord ++ tailWord_1656902).sum := by decide
  have hdescent : baseEnd_1656902 < baseStart_1656902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656945 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 5]
def baseStart_1656945 : Nat := 118140960795 + 1656945 * 2 ^ 59
def prefixEnd_1656945 : Nat := 4983230072969 + 3 ^ 40 * 1656945 * 2
def baseEnd_1656945 : Nat := 189068711792027761948301

theorem tailTrace_1656945 : CollatzResearch.WordTrace tailWord_1656945 prefixEnd_1656945 189068711792027761948301 := by
  unfold tailWord_1656945
  simp only [CollatzResearch.WordTrace]
  refine ⟨60433748982178723521628289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40289165988119149014418859 60433748982178723521628289)
  ·
    refine ⟨45325311736634042641221217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60433748982178723521628289 45325311736634042641221217)
    ·
      refine ⟨33993983802475531980915913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45325311736634042641221217 33993983802475531980915913)
      ·
        refine ⟨25495487851856648985686935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33993983802475531980915913 25495487851856648985686935)
        ·
          refine ⟨38243231777784973478530403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25495487851856648985686935 38243231777784973478530403)
          ·
            refine ⟨57364847666677460217795605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38243231777784973478530403 57364847666677460217795605)
            ·
              refine ⟨2688977234375505947709169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57364847666677460217795605 2688977234375505947709169)
              ·
                refine ⟨2016732925781629460781877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2688977234375505947709169 2016732925781629460781877)
                ·
                  refine ⟨189068711792027761948301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016732925781629460781877 189068711792027761948301)
                  ·
                    rfl

theorem cell22_1656945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_1656945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656945 prefixEnd_1656945 := by exact prefixLift 1656945
  have htrace : WordTrace (prefixWord ++ tailWord_1656945) baseStart_1656945 baseEnd_1656945 := by
    simpa [prefixWord, tailWord_1656945, baseEnd_1656945] using wordTrace_append hprefix tailTrace_1656945
  have hstable : (prefixWord ++ tailWord_1656945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656945).length < 2 ^ (prefixWord ++ tailWord_1656945).sum := by decide
  have hdescent : baseEnd_1656945 < baseStart_1656945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1656992 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_1656992 : Nat := 118140960795 + 1656992 * 2 ^ 59
def prefixEnd_1656992 : Nat := 4983230072969 + 3 ^ 40 * 1656992 * 2
def baseEnd_1656992 : Nat := 567222224436590829919759

theorem tailTrace_1656992 : CollatzResearch.WordTrace tailWord_1656992 prefixEnd_1656992 567222224436590829919759 := by
  unfold tailWord_1656992
  simp only [CollatzResearch.WordTrace]
  refine ⟨30217731606504225274294615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40290308808672300365726153 30217731606504225274294615)
  ·
    refine ⟨45326597409756337911441923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30217731606504225274294615 45326597409756337911441923)
    ·
      refine ⟨67989896114634506867162885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45326597409756337911441923 67989896114634506867162885)
      ·
        refine ⟨12748105521493970037593041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67989896114634506867162885 12748105521493970037593041)
        ·
          refine ⟨9561079141120477528194781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12748105521493970037593041 9561079141120477528194781)
          ·
            refine ⟨3585404677920179073073043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9561079141120477528194781 3585404677920179073073043)
            ·
              refine ⟨5378107016880268609609565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585404677920179073073043 5378107016880268609609565)
              ·
                refine ⟨2016790131330100728603587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5378107016880268609609565 2016790131330100728603587)
                ·
                  refine ⟨3025185196995151092905381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016790131330100728603587 3025185196995151092905381)
                  ·
                    refine ⟨567222224436590829919759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025185196995151092905381 567222224436590829919759)
                    ·
                      rfl

theorem cell22_1656992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_1656992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1656992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1656992 prefixEnd_1656992 := by exact prefixLift 1656992
  have htrace : WordTrace (prefixWord ++ tailWord_1656992) baseStart_1656992 baseEnd_1656992 := by
    simpa [prefixWord, tailWord_1656992, baseEnd_1656992] using wordTrace_append hprefix tailTrace_1656992
  have hstable : (prefixWord ++ tailWord_1656992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1656992).length < 2 ^ (prefixWord ++ tailWord_1656992).sum := by decide
  have hdescent : baseEnd_1656992 < baseStart_1656992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1656992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657026 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1657026 : Nat := 118140960795 + 1657026 * 2 ^ 59
def prefixEnd_1657026 : Nat := 4983230072969 + 3 ^ 40 * 1657026 * 2
def baseEnd_1657026 : Nat := 567233863331426074569655

theorem tailTrace_1657026 : CollatzResearch.WordTrace tailWord_1657026 prefixEnd_1657026 567233863331426074569655 := by
  unfold tailWord_1657026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109175823721318588831733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40291135529923516236884621 15109175823721318588831733)
  ·
    refine ⟨1416485233473873617702975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15109175823721318588831733 1416485233473873617702975)
    ·
      refine ⟨2124727850210810426554463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1416485233473873617702975 2124727850210810426554463)
      ·
        refine ⟨3187091775316215639831695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124727850210810426554463 3187091775316215639831695)
        ·
          refine ⟨4780637662974323459747543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187091775316215639831695 4780637662974323459747543)
          ·
            refine ⟨7170956494461485189621315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4780637662974323459747543 7170956494461485189621315)
            ·
              refine ⟨10756434741692227784431973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7170956494461485189621315 10756434741692227784431973)
              ·
                refine ⟨2016831514067292709580995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10756434741692227784431973 2016831514067292709580995)
                ·
                  refine ⟨3025247271100939064371493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016831514067292709580995 3025247271100939064371493)
                  ·
                    refine ⟨567233863331426074569655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025247271100939064371493 567233863331426074569655)
                    ·
                      rfl

theorem cell22_1657026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1657026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657026 prefixEnd_1657026 := by exact prefixLift 1657026
  have htrace : WordTrace (prefixWord ++ tailWord_1657026) baseStart_1657026 baseEnd_1657026 := by
    simpa [prefixWord, tailWord_1657026, baseEnd_1657026] using wordTrace_append hprefix tailTrace_1657026
  have hstable : (prefixWord ++ tailWord_1657026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657026).length < 2 ^ (prefixWord ++ tailWord_1657026).sum := by decide
  have hdescent : baseEnd_1657026 < baseStart_1657026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657058 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1657058 : Nat := 118140960795 + 1657058 * 2 ^ 59
def prefixEnd_1657058 : Nat := 4983230072969 + 3 ^ 40 * 1657058 * 2
def baseEnd_1657058 : Nat := 189081605861796219256519

theorem tailTrace_1657058 : CollatzResearch.WordTrace tailWord_1657058 prefixEnd_1657058 189081605861796219256519 := by
  unfold tailWord_1657058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109467607692335955122957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40291913620512895880327885 15109467607692335955122957)
  ·
    refine ⟨5666050352884625983171109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15109467607692335955122957 5666050352884625983171109)
    ·
      refine ⟨1062384441165867371844583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5666050352884625983171109 1062384441165867371844583)
      ·
        refine ⟨1593576661748801057766875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062384441165867371844583 1593576661748801057766875)
        ·
          refine ⟨2390364992623201586650313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593576661748801057766875 2390364992623201586650313)
          ·
            refine ⟨1792773744467401189987735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2390364992623201586650313 1792773744467401189987735)
            ·
              refine ⟨2689160616701101784981603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792773744467401189987735 2689160616701101784981603)
              ·
                refine ⟨4033740925051652677472405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689160616701101784981603 4033740925051652677472405)
                ·
                  refine ⟨189081605861796219256519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4033740925051652677472405 189081605861796219256519)
                  ·
                    rfl

theorem cell22_1657058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1657058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657058 prefixEnd_1657058 := by exact prefixLift 1657058
  have htrace : WordTrace (prefixWord ++ tailWord_1657058) baseStart_1657058 baseEnd_1657058 := by
    simpa [prefixWord, tailWord_1657058, baseEnd_1657058] using wordTrace_append hprefix tailTrace_1657058
  have hstable : (prefixWord ++ tailWord_1657058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657058).length < 2 ^ (prefixWord ++ tailWord_1657058).sum := by decide
  have hdescent : baseEnd_1657058 < baseStart_1657058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657114 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_1657114 : Nat := 118140960795 + 1657114 * 2 ^ 59
def prefixEnd_1657114 : Nat := 4983230072969 + 3 ^ 40 * 1657114 * 2
def baseEnd_1657114 : Nat := 189087995843274392789795

theorem tailTrace_1657114 : CollatzResearch.WordTrace tailWord_1657114 prefixEnd_1657114 189087995843274392789795 := by
  unfold tailWord_1657114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109978229641616346132599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40293275279044310256353597 15109978229641616346132599)
  ·
    refine ⟨22664967344462424519198899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15109978229641616346132599 22664967344462424519198899)
    ·
      refine ⟨33997451016693636778798349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22664967344462424519198899 33997451016693636778798349)
      ·
        refine ⟨12749044131260113792049381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33997451016693636778798349 12749044131260113792049381)
        ·
          refine ⟨2390445774611271336009259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12749044131260113792049381 2390445774611271336009259)
          ·
            refine ⟨3585668661916907004013889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390445774611271336009259 3585668661916907004013889)
            ·
              refine ⟨2689251496437680253010417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3585668661916907004013889 2689251496437680253010417)
              ·
                refine ⟨2016938622328260189757813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689251496437680253010417 2016938622328260189757813)
                ·
                  refine ⟨189087995843274392789795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016938622328260189757813 189087995843274392789795)
                  ·
                    rfl

theorem cell22_1657114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_1657114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657114 prefixEnd_1657114 := by exact prefixLift 1657114
  have htrace : WordTrace (prefixWord ++ tailWord_1657114) baseStart_1657114 baseEnd_1657114 := by
    simpa [prefixWord, tailWord_1657114, baseEnd_1657114] using wordTrace_append hprefix tailTrace_1657114
  have hstable : (prefixWord ++ tailWord_1657114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657114).length < 2 ^ (prefixWord ++ tailWord_1657114).sum := by decide
  have hdescent : baseEnd_1657114 < baseStart_1657114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657159 : List Nat := [1, 1, 4, 1, 2, 2, 4, 3, 4]
def baseStart_1657159 : Nat := 118140960795 + 1657159 * 2 ^ 59
def prefixEnd_1657159 : Nat := 4983230072969 + 3 ^ 40 * 1657159 * 2
def baseEnd_1657159 : Nat := 189093130649819353664749

theorem tailTrace_1657159 : CollatzResearch.WordTrace tailWord_1657159 prefixEnd_1657159 189093130649819353664749 := by
  unfold tailWord_1657159
  simp only [CollatzResearch.WordTrace]
  refine ⟨60441554203403438069918531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40294369468935625379945687 60441554203403438069918531)
  ·
    refine ⟨90662331305105157104877797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60441554203403438069918531 90662331305105157104877797)
    ·
      refine ⟨16999187119707216957164587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90662331305105157104877797 16999187119707216957164587)
      ·
        refine ⟨25498780679560825435746881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16999187119707216957164587 25498780679560825435746881)
        ·
          refine ⟨19124085509670619076810161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25498780679560825435746881 19124085509670619076810161)
          ·
            refine ⟨14343064132252964307607621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19124085509670619076810161 14343064132252964307607621)
            ·
              refine ⟨2689324524797430807676429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14343064132252964307607621 2689324524797430807676429)
              ·
                refine ⟨1008496696799036552878661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2689324524797430807676429 1008496696799036552878661)
                ·
                  refine ⟨189093130649819353664749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1008496696799036552878661 189093130649819353664749)
                  ·
                    rfl

theorem cell22_1657159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 4].length) (baseStart_1657159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657159 prefixEnd_1657159 := by exact prefixLift 1657159
  have htrace : WordTrace (prefixWord ++ tailWord_1657159) baseStart_1657159 baseEnd_1657159 := by
    simpa [prefixWord, tailWord_1657159, baseEnd_1657159] using wordTrace_append hprefix tailTrace_1657159
  have hstable : (prefixWord ++ tailWord_1657159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657159).length < 2 ^ (prefixWord ++ tailWord_1657159).sum := by decide
  have hdescent : baseEnd_1657159 < baseStart_1657159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657182 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1657182 : Nat := 118140960795 + 1657182 * 2 ^ 59
def prefixEnd_1657182 : Nat := 4983230072969 + 3 ^ 40 * 1657182 * 2
def baseEnd_1657182 : Nat := 189095755106497889223059

theorem tailTrace_1657182 : CollatzResearch.WordTrace tailWord_1657182 prefixEnd_1657182 189095755106497889223059 := by
  unfold tailWord_1657182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555299135290014124750725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40294928721546741998670533 7555299135290014124750725)
  ·
    refine ⟨1416618587866877648390761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7555299135290014124750725 1416618587866877648390761)
    ·
      refine ⟨1062463940900158236293071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1416618587866877648390761 1062463940900158236293071)
      ·
        refine ⟨1593695911350237354439607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062463940900158236293071 1593695911350237354439607)
        ·
          refine ⟨2390543867025356031659411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593695911350237354439607 2390543867025356031659411)
          ·
            refine ⟨3585815800538034047489117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390543867025356031659411 3585815800538034047489117)
            ·
              refine ⟨1344680925201762767808419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3585815800538034047489117 1344680925201762767808419)
              ·
                refine ⟨2017021387802644151712629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344680925201762767808419 2017021387802644151712629)
                ·
                  refine ⟨189095755106497889223059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2017021387802644151712629 189095755106497889223059)
                  ·
                    rfl

theorem cell22_1657182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1657182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657182 prefixEnd_1657182 := by exact prefixLift 1657182
  have htrace : WordTrace (prefixWord ++ tailWord_1657182) baseStart_1657182 baseEnd_1657182 := by
    simpa [prefixWord, tailWord_1657182, baseEnd_1657182] using wordTrace_append hprefix tailTrace_1657182
  have hstable : (prefixWord ++ tailWord_1657182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657182).length < 2 ^ (prefixWord ++ tailWord_1657182).sum := by decide
  have hdescent : baseEnd_1657182 < baseStart_1657182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657247 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 1, 7]
def baseStart_1657247 : Nat := 118140960795 + 1657247 * 2 ^ 59
def prefixEnd_1657247 : Nat := 4983230072969 + 3 ^ 40 * 1657247 * 2
def baseEnd_1657247 : Nat := 567309516147855164793977

theorem tailTrace_1657247 : CollatzResearch.WordTrace tailWord_1657247 prefixEnd_1657247 567309516147855164793977 := by
  unfold tailWord_1657247
  simp only [CollatzResearch.WordTrace]
  refine ⟨60444763827084629099121995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40296509218056419399414663 60444763827084629099121995)
  ·
    refine ⟨90667145740626943648682993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60444763827084629099121995 90667145740626943648682993)
    ·
      refine ⟨68000359305470207736512245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90667145740626943648682993 68000359305470207736512245)
      ·
        refine ⟨6375033684887831975298023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68000359305470207736512245 6375033684887831975298023)
        ·
          refine ⟨9562550527331747962947035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375033684887831975298023 9562550527331747962947035)
          ·
            refine ⟨14343825790997621944420553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9562550527331747962947035 14343825790997621944420553)
            ·
              refine ⟨10757869343248216458315415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14343825790997621944420553 10757869343248216458315415)
              ·
                refine ⟨16136804014872324687473123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10757869343248216458315415 16136804014872324687473123)
                ·
                  refine ⟨24205206022308487031209685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16136804014872324687473123 24205206022308487031209685)
                  ·
                    refine ⟨567309516147855164793977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24205206022308487031209685 567309516147855164793977)
                    ·
                      rfl

theorem cell22_1657247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_1657247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657247 prefixEnd_1657247 := by exact prefixLift 1657247
  have htrace : WordTrace (prefixWord ++ tailWord_1657247) baseStart_1657247 baseEnd_1657247 := by
    simpa [prefixWord, tailWord_1657247, baseEnd_1657247] using wordTrace_append hprefix tailTrace_1657247
  have hstable : (prefixWord ++ tailWord_1657247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657247).length < 2 ^ (prefixWord ++ tailWord_1657247).sum := by decide
  have hdescent : baseEnd_1657247 < baseStart_1657247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657330 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_1657330 : Nat := 118140960795 + 1657330 * 2 ^ 59
def prefixEnd_1657330 : Nat := 4983230072969 + 3 ^ 40 * 1657330 * 2
def baseEnd_1657330 : Nat := 567337928744070614968723

theorem tailTrace_1657330 : CollatzResearch.WordTrace tailWord_1657330 prefixEnd_1657330 567337928744070614968723 := by
  unfold tailWord_1657330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15111947771445983568598361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40298527390522622849595629 15111947771445983568598361)
  ·
    refine ⟨11333960828584487676448771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15111947771445983568598361 11333960828584487676448771)
    ·
      refine ⟨17000941242876731514673157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11333960828584487676448771 17000941242876731514673157)
      ·
        refine ⟨3187676483039387159001217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17000941242876731514673157 3187676483039387159001217)
        ·
          refine ⟨2390757362279540369250913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3187676483039387159001217 2390757362279540369250913)
          ·
            refine ⟨1793068021709655276938185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2390757362279540369250913 1793068021709655276938185)
            ·
              refine ⟨1344801016282241457703639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793068021709655276938185 1344801016282241457703639)
              ·
                refine ⟨2017201524423362186555459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344801016282241457703639 2017201524423362186555459)
                ·
                  refine ⟨3025802286635043279833189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017201524423362186555459 3025802286635043279833189)
                  ·
                    refine ⟨567337928744070614968723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3025802286635043279833189 567337928744070614968723)
                    ·
                      rfl

theorem cell22_1657330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_1657330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657330 prefixEnd_1657330 := by exact prefixLift 1657330
  have htrace : WordTrace (prefixWord ++ tailWord_1657330) baseStart_1657330 baseEnd_1657330 := by
    simpa [prefixWord, tailWord_1657330, baseEnd_1657330] using wordTrace_append hprefix tailTrace_1657330
  have hstable : (prefixWord ++ tailWord_1657330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657330).length < 2 ^ (prefixWord ++ tailWord_1657330).sum := by decide
  have hdescent : baseEnd_1657330 < baseStart_1657330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657418 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_1657418 : Nat := 118140960795 + 1657418 * 2 ^ 59
def prefixEnd_1657418 : Nat := 4983230072969 + 3 ^ 40 * 1657418 * 2
def baseEnd_1657418 : Nat := 189122684314155906256151

theorem tailTrace_1657418 : CollatzResearch.WordTrace tailWord_1657418 prefixEnd_1657418 189122684314155906256151 := by
  unfold tailWord_1657418
  simp only [CollatzResearch.WordTrace]
  refine ⟨15112750177366281325899227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40300667139643416869064605 15112750177366281325899227)
  ·
    refine ⟨22669125266049421988848841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15112750177366281325899227 22669125266049421988848841)
    ·
      refine ⟨17001843949537066491636631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22669125266049421988848841 17001843949537066491636631)
      ·
        refine ⟨25502765924305599737454947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17001843949537066491636631 25502765924305599737454947)
        ·
          refine ⟨38254148886458399606182421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25502765924305599737454947 38254148886458399606182421)
          ·
            refine ⟨1793163229052737481539801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38254148886458399606182421 1793163229052737481539801)
            ·
              refine ⟨1344872421789553111154851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793163229052737481539801 1344872421789553111154851)
              ·
                refine ⟨2017308632684329666732277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344872421789553111154851 2017308632684329666732277)
                ·
                  refine ⟨189122684314155906256151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2017308632684329666732277 189122684314155906256151)
                  ·
                    rfl

theorem cell22_1657418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_1657418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657418 prefixEnd_1657418 := by exact prefixLift 1657418
  have htrace : WordTrace (prefixWord ++ tailWord_1657418) baseStart_1657418 baseEnd_1657418 := by
    simpa [prefixWord, tailWord_1657418, baseEnd_1657418] using wordTrace_append hprefix tailTrace_1657418
  have hstable : (prefixWord ++ tailWord_1657418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657418).length < 2 ^ (prefixWord ++ tailWord_1657418).sum := by decide
  have hdescent : baseEnd_1657418 < baseStart_1657418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657429 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 6]
def baseStart_1657429 : Nat := 118140960795 + 1657429 * 2 ^ 59
def prefixEnd_1657429 : Nat := 4983230072969 + 3 ^ 40 * 1657429 * 2
def baseEnd_1657429 : Nat := 189123939489089118914473

theorem tailTrace_1657429 : CollatzResearch.WordTrace tailWord_1657429 prefixEnd_1657429 189123939489089118914473 := by
  unfold tailWord_1657429
  simp only [CollatzResearch.WordTrace]
  refine ⟨60451401912425274182247341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40300934608283516121498227 60451401912425274182247341)
  ·
    refine ⟨22669275717159477818342753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60451401912425274182247341 22669275717159477818342753)
    ·
      refine ⟨17001956787869608363757065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22669275717159477818342753 17001956787869608363757065)
      ·
        refine ⟨12751467590902206272817799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17001956787869608363757065 12751467590902206272817799)
        ·
          refine ⟨19127201386353309409226699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12751467590902206272817799 19127201386353309409226699)
          ·
            refine ⟨28690802079529964113840049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19127201386353309409226699 28690802079529964113840049)
            ·
              refine ⟨21518101559647473085380037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28690802079529964113840049 21518101559647473085380037)
              ·
                refine ⟨4034644042433901203508757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21518101559647473085380037 4034644042433901203508757)
                ·
                  refine ⟨189123939489089118914473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4034644042433901203508757 189123939489089118914473)
                  ·
                    rfl

theorem cell22_1657429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_1657429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657429 prefixEnd_1657429 := by exact prefixLift 1657429
  have htrace : WordTrace (prefixWord ++ tailWord_1657429) baseStart_1657429 baseEnd_1657429 := by
    simpa [prefixWord, tailWord_1657429, baseEnd_1657429] using wordTrace_append hprefix tailTrace_1657429
  have hstable : (prefixWord ++ tailWord_1657429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657429).length < 2 ^ (prefixWord ++ tailWord_1657429).sum := by decide
  have hdescent : baseEnd_1657429 < baseStart_1657429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657459 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 4, 4]
def baseStart_1657459 : Nat := 118140960795 + 1657459 * 2 ^ 59
def prefixEnd_1657459 : Nat := 4983230072969 + 3 ^ 40 * 1657459 * 2
def baseEnd_1657459 : Nat := 567382088080357278493327

theorem tailTrace_1657459 : CollatzResearch.WordTrace tailWord_1657459 prefixEnd_1657459 567382088080357278493327 := by
  unfold tailWord_1657459
  simp only [CollatzResearch.WordTrace]
  refine ⟨60452496102316589305839431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40301664068211059537226287 60452496102316589305839431)
  ·
    refine ⟨90678744153474883958759147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60452496102316589305839431 90678744153474883958759147)
    ·
      refine ⟨136018116230212325938138721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90678744153474883958759147 136018116230212325938138721)
      ·
        refine ⟨102013587172659244453604041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136018116230212325938138721 102013587172659244453604041)
        ·
          refine ⟨76510190379494433340203031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102013587172659244453604041 76510190379494433340203031)
          ·
            refine ⟨114765285569241650010304547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76510190379494433340203031 114765285569241650010304547)
            ·
              refine ⟨172147928353862475015456821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114765285569241650010304547 172147928353862475015456821)
              ·
                refine ⟨16138868283174607032699077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172147928353862475015456821 16138868283174607032699077)
                ·
                  refine ⟨3026037803095238818631077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16138868283174607032699077 3026037803095238818631077)
                  ·
                    refine ⟨567382088080357278493327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3026037803095238818631077 567382088080357278493327)
                    ·
                      rfl

theorem cell22_1657459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 4].length) (baseStart_1657459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657459 prefixEnd_1657459 := by exact prefixLift 1657459
  have htrace : WordTrace (prefixWord ++ tailWord_1657459) baseStart_1657459 baseEnd_1657459 := by
    simpa [prefixWord, tailWord_1657459, baseEnd_1657459] using wordTrace_append hprefix tailTrace_1657459
  have hstable : (prefixWord ++ tailWord_1657459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657459).length < 2 ^ (prefixWord ++ tailWord_1657459).sum := by decide
  have hdescent : baseEnd_1657459 < baseStart_1657459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657463 : List Nat := [1, 1, 3, 1, 1, 3, 6, 2, 4]
def baseStart_1657463 : Nat := 118140960795 + 1657463 * 2 ^ 59
def prefixEnd_1657463 : Nat := 4983230072969 + 3 ^ 40 * 1657463 * 2
def baseEnd_1657463 : Nat := 189127819120700867131105

theorem tailTrace_1657463 : CollatzResearch.WordTrace tailWord_1657463 prefixEnd_1657463 189127819120700867131105 := by
  unfold tailWord_1657463
  simp only [CollatzResearch.WordTrace]
  refine ⟨60452641994302097988985043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40301761329534731992656695 60452641994302097988985043)
  ·
    refine ⟨90678962991453146983477565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60452641994302097988985043 90678962991453146983477565)
    ·
      refine ⟨34004611121794930118804087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90678962991453146983477565 34004611121794930118804087)
      ·
        refine ⟨51006916682692395178206131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34004611121794930118804087 51006916682692395178206131)
        ·
          refine ⟨76510375024038592767309197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51006916682692395178206131 76510375024038592767309197)
          ·
            refine ⟨28691390634014472287740949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76510375024038592767309197 28691390634014472287740949)
            ·
              refine ⟨1344908935969428388487857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28691390634014472287740949 1344908935969428388487857)
              ·
                refine ⟨1008681701977071291365893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344908935969428388487857 1008681701977071291365893)
                ·
                  refine ⟨189127819120700867131105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1008681701977071291365893 189127819120700867131105)
                  ·
                    rfl

theorem cell22_1657463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 4].length) (baseStart_1657463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657463 prefixEnd_1657463 := by exact prefixLift 1657463
  have htrace : WordTrace (prefixWord ++ tailWord_1657463) baseStart_1657463 baseEnd_1657463 := by
    simpa [prefixWord, tailWord_1657463, baseEnd_1657463] using wordTrace_append hprefix tailTrace_1657463
  have hstable : (prefixWord ++ tailWord_1657463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657463).length < 2 ^ (prefixWord ++ tailWord_1657463).sum := by decide
  have hdescent : baseEnd_1657463 < baseStart_1657463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657523 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 3, 3]
def baseStart_1657523 : Nat := 118140960795 + 1657523 * 2 ^ 59
def prefixEnd_1657523 : Nat := 4983230072969 + 3 ^ 40 * 1657523 * 2
def baseEnd_1657523 : Nat := 567403996588282444893131

theorem tailTrace_1657523 : CollatzResearch.WordTrace tailWord_1657523 prefixEnd_1657523 567403996588282444893131 := by
  unfold tailWord_1657523
  simp only [CollatzResearch.WordTrace]
  refine ⟨60454830374084728236169223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40303220249389818824112815 60454830374084728236169223)
  ·
    refine ⟨90682245561127092354253835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60454830374084728236169223 90682245561127092354253835)
    ·
      refine ⟨136023368341690638531380753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90682245561127092354253835 136023368341690638531380753)
      ·
        refine ⟨102017526256267978898535565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136023368341690638531380753 102017526256267978898535565)
        ·
          refine ⟨38256572346100492086950837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102017526256267978898535565 38256572346100492086950837)
          ·
            refine ⟨3586553657446921133151641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38256572346100492086950837 3586553657446921133151641)
            ·
              refine ⟨2689915243085190849863731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586553657446921133151641 2689915243085190849863731)
              ·
                refine ⟨4034872864627786274795597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689915243085190849863731 4034872864627786274795597)
                ·
                  refine ⟨1513077324235419853048349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4034872864627786274795597 1513077324235419853048349)
                  ·
                    refine ⟨567403996588282444893131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1513077324235419853048349 567403996588282444893131)
                    ·
                      rfl

theorem cell22_1657523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 3].length) (baseStart_1657523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657523 prefixEnd_1657523 := by exact prefixLift 1657523
  have htrace : WordTrace (prefixWord ++ tailWord_1657523) baseStart_1657523 baseEnd_1657523 := by
    simpa [prefixWord, tailWord_1657523, baseEnd_1657523] using wordTrace_append hprefix tailTrace_1657523
  have hstable : (prefixWord ++ tailWord_1657523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657523).length < 2 ^ (prefixWord ++ tailWord_1657523).sum := by decide
  have hdescent : baseEnd_1657523 < baseStart_1657523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657628 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1657628 : Nat := 118140960795 + 1657628 * 2 ^ 59
def prefixEnd_1657628 : Nat := 4983230072969 + 3 ^ 40 * 1657628 * 2
def baseEnd_1657628 : Nat := 567439940234097171017809

theorem tailTrace_1657628 : CollatzResearch.WordTrace tailWord_1657628 prefixEnd_1657628 567439940234097171017809 := by
  unfold tailWord_1657628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30229330019352165584370769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40305773359136220779161025 30229330019352165584370769)
  ·
    refine ⟨22671997514514124188278077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30229330019352165584370769 22671997514514124188278077)
    ·
      refine ⟨8501999067942796570604279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22671997514514124188278077 8501999067942796570604279)
      ·
        refine ⟨12752998601914194855906419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501999067942796570604279 12752998601914194855906419)
        ·
          refine ⟨19129497902871292283859629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12752998601914194855906419 19129497902871292283859629)
          ·
            refine ⟨7173561713576734606447361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19129497902871292283859629 7173561713576734606447361)
            ·
              refine ⟨5380171285182550954835521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173561713576734606447361 5380171285182550954835521)
              ·
                refine ⟨4035128463886913216126641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5380171285182550954835521 4035128463886913216126641)
                ·
                  refine ⟨3026346347915184912094981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4035128463886913216126641 3026346347915184912094981)
                  ·
                    refine ⟨567439940234097171017809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3026346347915184912094981 567439940234097171017809)
                    ·
                      rfl

theorem cell22_1657628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1657628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657628 prefixEnd_1657628 := by exact prefixLift 1657628
  have htrace : WordTrace (prefixWord ++ tailWord_1657628) baseStart_1657628 baseEnd_1657628 := by
    simpa [prefixWord, tailWord_1657628, baseEnd_1657628] using wordTrace_append hprefix tailTrace_1657628
  have hstable : (prefixWord ++ tailWord_1657628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657628).length < 2 ^ (prefixWord ++ tailWord_1657628).sum := by decide
  have hdescent : baseEnd_1657628 < baseStart_1657628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657632 : List Nat := [2, 1, 1, 5, 1, 4, 2, 2, 4]
def baseStart_1657632 : Nat := 118140960795 + 1657632 * 2 ^ 59
def prefixEnd_1657632 : Nat := 4983230072969 + 3 ^ 40 * 1657632 * 2
def baseEnd_1657632 : Nat := 189147103171947497972599

theorem tailTrace_1657632 : CollatzResearch.WordTrace tailWord_1657632 prefixEnd_1657632 189147103171947497972599 := by
  unfold tailWord_1657632
  simp only [CollatzResearch.WordTrace]
  refine ⟨30229402965344919925943575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40305870620459893234591433 30229402965344919925943575)
  ·
    refine ⟨45344104448017379888915363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30229402965344919925943575 45344104448017379888915363)
    ·
      refine ⟨68016156672026069833373045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45344104448017379888915363 68016156672026069833373045)
      ·
        refine ⟨6376514688002444046878723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68016156672026069833373045 6376514688002444046878723)
        ·
          refine ⟨9564772032003666070318085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376514688002444046878723 9564772032003666070318085)
          ·
            refine ⟨1793394756000687388184641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9564772032003666070318085 1793394756000687388184641)
            ·
              refine ⟨1345046067000515541138481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793394756000687388184641 1345046067000515541138481)
              ·
                refine ⟨1008784550250386655853861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345046067000515541138481 1008784550250386655853861)
                ·
                  refine ⟨189147103171947497972599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1008784550250386655853861 189147103171947497972599)
                  ·
                    rfl

theorem cell22_1657632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 4].length) (baseStart_1657632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657632 prefixEnd_1657632 := by exact prefixLift 1657632
  have htrace : WordTrace (prefixWord ++ tailWord_1657632) baseStart_1657632 baseEnd_1657632 := by
    simpa [prefixWord, tailWord_1657632, baseEnd_1657632] using wordTrace_append hprefix tailTrace_1657632
  have hstable : (prefixWord ++ tailWord_1657632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657632).length < 2 ^ (prefixWord ++ tailWord_1657632).sum := by decide
  have hdescent : baseEnd_1657632 < baseStart_1657632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657656 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_1657656 : Nat := 118140960795 + 1657656 * 2 ^ 59
def prefixEnd_1657656 : Nat := 4983230072969 + 3 ^ 40 * 1657656 * 2
def baseEnd_1657656 : Nat := 567449525206314431317723

theorem tailTrace_1657656 : CollatzResearch.WordTrace tailWord_1657656 prefixEnd_1657656 567449525206314431317723 := by
  unfold tailWord_1657656
  simp only [CollatzResearch.WordTrace]
  refine ⟨30229840641301445975380411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40306454188401927967173881 30229840641301445975380411)
  ·
    refine ⟨45344760961952168963070617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30229840641301445975380411 45344760961952168963070617)
    ·
      refine ⟨34008570721464126722302963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45344760961952168963070617 34008570721464126722302963)
      ·
        refine ⟨51012856082196190083454445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34008570721464126722302963 51012856082196190083454445)
        ·
          refine ⟨19129821030823571281295417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51012856082196190083454445 19129821030823571281295417)
          ·
            refine ⟨14347365773117678460971563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19129821030823571281295417 14347365773117678460971563)
            ·
              refine ⟨21521048659676517691457345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14347365773117678460971563 21521048659676517691457345)
              ·
                refine ⟨16140786494757388268593009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21521048659676517691457345 16140786494757388268593009)
                ·
                  refine ⟨12105589871068041201444757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16140786494757388268593009 12105589871068041201444757)
                  ·
                    refine ⟨567449525206314431317723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12105589871068041201444757 567449525206314431317723)
                    ·
                      rfl

theorem cell22_1657656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_1657656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657656 prefixEnd_1657656 := by exact prefixLift 1657656
  have htrace : WordTrace (prefixWord ++ tailWord_1657656) baseStart_1657656 baseEnd_1657656 := by
    simpa [prefixWord, tailWord_1657656, baseEnd_1657656] using wordTrace_append hprefix tailTrace_1657656
  have hstable : (prefixWord ++ tailWord_1657656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657656).length < 2 ^ (prefixWord ++ tailWord_1657656).sum := by decide
  have hdescent : baseEnd_1657656 < baseStart_1657656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657662 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1657662 : Nat := 118140960795 + 1657662 * 2 ^ 59
def prefixEnd_1657662 : Nat := 4983230072969 + 3 ^ 40 * 1657662 * 2
def baseEnd_1657662 : Nat := 567451579128932415667705

theorem tailTrace_1657662 : CollatzResearch.WordTrace tailWord_1657662 prefixEnd_1657662 567451579128932415667705 := by
  unfold tailWord_1657662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7557487515072644371934905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40306600080387436650319493 7557487515072644371934905)
  ·
    refine ⟨5668115636304483278951179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7557487515072644371934905 5668115636304483278951179)
    ·
      refine ⟨8502173454456724918426769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5668115636304483278951179 8502173454456724918426769)
      ·
        refine ⟨6376630090842543688820077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8502173454456724918426769 6376630090842543688820077)
        ·
          refine ⟨2391236284065953883307529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6376630090842543688820077 2391236284065953883307529)
          ·
            refine ⟨1793427213049465412480647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391236284065953883307529 1793427213049465412480647)
            ·
              refine ⟨2690140819574198118720971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793427213049465412480647 2690140819574198118720971)
              ·
                refine ⟨4035211229361297178081457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690140819574198118720971 4035211229361297178081457)
                ·
                  refine ⟨3026408422020972883561093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4035211229361297178081457 3026408422020972883561093)
                  ·
                    refine ⟨567451579128932415667705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3026408422020972883561093 567451579128932415667705)
                    ·
                      rfl

theorem cell22_1657662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1657662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657662 prefixEnd_1657662 := by exact prefixLift 1657662
  have htrace : WordTrace (prefixWord ++ tailWord_1657662) baseStart_1657662 baseEnd_1657662 := by
    simpa [prefixWord, tailWord_1657662, baseEnd_1657662] using wordTrace_append hprefix tailTrace_1657662
  have hstable : (prefixWord ++ tailWord_1657662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657662).length < 2 ^ (prefixWord ++ tailWord_1657662).sum := by decide
  have hdescent : baseEnd_1657662 < baseStart_1657662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657671 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 7]
def baseStart_1657671 : Nat := 118140960795 + 1657671 * 2 ^ 59
def prefixEnd_1657671 : Nat := 4983230072969 + 3 ^ 40 * 1657671 * 2
def baseEnd_1657671 : Nat := 189151553337619797397559

theorem tailTrace_1657671 : CollatzResearch.WordTrace tailWord_1657671 prefixEnd_1657671 189151553337619797397559 := by
  unfold tailWord_1657671
  simp only [CollatzResearch.WordTrace]
  refine ⟨60460228377548549512556867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40306818918365699675037911 60460228377548549512556867)
  ·
    refine ⟨90690342566322824268835301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60460228377548549512556867 90690342566322824268835301)
    ·
      refine ⟨17004439231185529550406619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90690342566322824268835301 17004439231185529550406619)
      ·
        refine ⟨25506658846778294325609929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17004439231185529550406619 25506658846778294325609929)
        ·
          refine ⟨19129994135083720744207447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25506658846778294325609929 19129994135083720744207447)
          ·
            refine ⟨28694991202625581116311171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19129994135083720744207447 28694991202625581116311171)
            ·
              refine ⟨43042486803938371674466757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28694991202625581116311171 43042486803938371674466757)
              ·
                refine ⟨8070466275738444688962517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43042486803938371674466757 8070466275738444688962517)
                ·
                  refine ⟨189151553337619797397559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8070466275738444688962517 189151553337619797397559)
                  ·
                    rfl

theorem cell22_1657671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 7].length) (baseStart_1657671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657671 prefixEnd_1657671 := by exact prefixLift 1657671
  have htrace : WordTrace (prefixWord ++ tailWord_1657671) baseStart_1657671 baseEnd_1657671 := by
    simpa [prefixWord, tailWord_1657671, baseEnd_1657671] using wordTrace_append hprefix tailTrace_1657671
  have hstable : (prefixWord ++ tailWord_1657671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657671).length < 2 ^ (prefixWord ++ tailWord_1657671).sum := by decide
  have hdescent : baseEnd_1657671 < baseStart_1657671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657692 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1657692 : Nat := 118140960795 + 1657692 * 2 ^ 59
def prefixEnd_1657692 : Nat := 4983230072969 + 3 ^ 40 * 1657692 * 2
def baseEnd_1657692 : Nat := 567461848742022337417613

theorem tailTrace_1657692 : CollatzResearch.WordTrace tailWord_1657692 prefixEnd_1657692 567461848742022337417613 := by
  unfold tailWord_1657692
  simp only [CollatzResearch.WordTrace]
  refine ⟨30230497155236235049535665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40307329540314980066047553 30230497155236235049535665)
  ·
    refine ⟨22672872866427176287151749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30230497155236235049535665 22672872866427176287151749)
    ·
      refine ⟨4251163662455095553840953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22672872866427176287151749 4251163662455095553840953)
      ·
        refine ⟨3188372746841321665380715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4251163662455095553840953 3188372746841321665380715)
        ·
          refine ⟨4782559120261982498071073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188372746841321665380715 4782559120261982498071073)
          ·
            refine ⟨3586919340196486873553305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4782559120261982498071073 3586919340196486873553305)
            ·
              refine ⟨2690189505147365155164979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586919340196486873553305 2690189505147365155164979)
              ·
                refine ⟨4035284257721047732747469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690189505147365155164979 4035284257721047732747469)
                ·
                  refine ⟨1513231596645392899780301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4035284257721047732747469 1513231596645392899780301)
                  ·
                    refine ⟨567461848742022337417613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1513231596645392899780301 567461848742022337417613)
                    ·
                      rfl

theorem cell22_1657692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1657692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657692 prefixEnd_1657692 := by exact prefixLift 1657692
  have htrace : WordTrace (prefixWord ++ tailWord_1657692) baseStart_1657692 baseEnd_1657692 := by
    simpa [prefixWord, tailWord_1657692, baseEnd_1657692] using wordTrace_append hprefix tailTrace_1657692
  have hstable : (prefixWord ++ tailWord_1657692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657692).length < 2 ^ (prefixWord ++ tailWord_1657692).sum := by decide
  have hdescent : baseEnd_1657692 < baseStart_1657692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657703 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1657703 : Nat := 118140960795 + 1657703 * 2 ^ 59
def prefixEnd_1657703 : Nat := 4983230072969 + 3 ^ 40 * 1657703 * 2
def baseEnd_1657703 : Nat := 567465614266821975392579

theorem tailTrace_1657703 : CollatzResearch.WordTrace tailWord_1657703 prefixEnd_1657703 567465614266821975392579 := by
  unfold tailWord_1657703
  simp only [CollatzResearch.WordTrace]
  refine ⟨60461395513432618977721763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40307597008955079318481175 60461395513432618977721763)
  ·
    refine ⟨90692093270148928466582645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60461395513432618977721763 90692093270148928466582645)
    ·
      refine ⟨8502383744076462043742123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90692093270148928466582645 8502383744076462043742123)
      ·
        refine ⟨12753575616114693065613185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8502383744076462043742123 12753575616114693065613185)
        ·
          refine ⟨9565181712086019799209889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12753575616114693065613185 9565181712086019799209889)
          ·
            refine ⟨7173886284064514849407417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9565181712086019799209889 7173886284064514849407417)
            ·
              refine ⟨5380414713048386137055563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173886284064514849407417 5380414713048386137055563)
              ·
                refine ⟨8070622069572579205583345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380414713048386137055563 8070622069572579205583345)
                ·
                  refine ⟨6052966552179434404187509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8070622069572579205583345 6052966552179434404187509)
                  ·
                    refine ⟨567465614266821975392579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6052966552179434404187509 567465614266821975392579)
                    ·
                      rfl

theorem cell22_1657703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1657703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657703 prefixEnd_1657703 := by exact prefixLift 1657703
  have htrace : WordTrace (prefixWord ++ tailWord_1657703) baseStart_1657703 baseEnd_1657703 := by
    simpa [prefixWord, tailWord_1657703, baseEnd_1657703] using wordTrace_append hprefix tailTrace_1657703
  have hstable : (prefixWord ++ tailWord_1657703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657703).length < 2 ^ (prefixWord ++ tailWord_1657703).sum := by decide
  have hdescent : baseEnd_1657703 < baseStart_1657703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657735 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1657735 : Nat := 118140960795 + 1657735 * 2 ^ 59
def prefixEnd_1657735 : Nat := 4983230072969 + 3 ^ 40 * 1657735 * 2
def baseEnd_1657735 : Nat := 567476568520784558592481

theorem tailTrace_1657735 : CollatzResearch.WordTrace tailWord_1657735 prefixEnd_1657735 567476568520784558592481 := by
  unfold tailWord_1657735
  simp only [CollatzResearch.WordTrace]
  refine ⟨60462562649316688442886659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40308375099544458961924439 60462562649316688442886659)
  ·
    refine ⟨90693843973975032664329989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60462562649316688442886659 90693843973975032664329989)
    ·
      refine ⟨17005095745120318624561873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90693843973975032664329989 17005095745120318624561873)
      ·
        refine ⟨12753821808840238968421405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17005095745120318624561873 12753821808840238968421405)
        ·
          refine ⟨4782683178315089613158027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12753821808840238968421405 4782683178315089613158027)
          ·
            refine ⟨7174024767472634419737041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782683178315089613158027 7174024767472634419737041)
            ·
              refine ⟨5380518575604475814802781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7174024767472634419737041 5380518575604475814802781)
              ·
                refine ⟨2017694465851678430551043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5380518575604475814802781 2017694465851678430551043)
                ·
                  refine ⟨3026541698777517645826565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017694465851678430551043 3026541698777517645826565)
                  ·
                    refine ⟨567476568520784558592481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3026541698777517645826565 567476568520784558592481)
                    ·
                      rfl

theorem cell22_1657735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1657735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657735 prefixEnd_1657735 := by exact prefixLift 1657735
  have htrace : WordTrace (prefixWord ++ tailWord_1657735) baseStart_1657735 baseEnd_1657735 := by
    simpa [prefixWord, tailWord_1657735, baseEnd_1657735] using wordTrace_append hprefix tailTrace_1657735
  have hstable : (prefixWord ++ tailWord_1657735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657735).length < 2 ^ (prefixWord ++ tailWord_1657735).sum := by decide
  have hdescent : baseEnd_1657735 < baseStart_1657735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657857 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 5]
def baseStart_1657857 : Nat := 118140960795 + 1657857 * 2 ^ 59
def prefixEnd_1657857 : Nat := 4983230072969 + 3 ^ 40 * 1657857 * 2
def baseEnd_1657857 : Nat := 189172777204672302347369

theorem tailTrace_1657857 : CollatzResearch.WordTrace tailWord_1657857 prefixEnd_1657857 189172777204672302347369 := by
  unfold tailWord_1657857
  simp only [CollatzResearch.WordTrace]
  refine ⟨60467012354874703278827825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40311341569916468852551883 60467012354874703278827825)
  ·
    refine ⟨45350259266156027459120869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60467012354874703278827825 45350259266156027459120869)
    ·
      refine ⟨8503173612404255148585163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45350259266156027459120869 8503173612404255148585163)
      ·
        refine ⟨12754760418606382722877745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503173612404255148585163 12754760418606382722877745)
        ·
          refine ⟨9566070313954787042158309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12754760418606382722877745 9566070313954787042158309)
          ·
            refine ⟨1793638183866522570404683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9566070313954787042158309 1793638183866522570404683)
            ·
              refine ⟨2690457275799783855607025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793638183866522570404683 2690457275799783855607025)
              ·
                refine ⟨2017842956849837891705269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690457275799783855607025 2017842956849837891705269)
                ·
                  refine ⟨189172777204672302347369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2017842956849837891705269 189172777204672302347369)
                  ·
                    rfl

theorem cell22_1657857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_1657857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657857 prefixEnd_1657857 := by exact prefixLift 1657857
  have htrace : WordTrace (prefixWord ++ tailWord_1657857) baseStart_1657857 baseEnd_1657857 := by
    simpa [prefixWord, tailWord_1657857, baseEnd_1657857] using wordTrace_append hprefix tailTrace_1657857
  have hstable : (prefixWord ++ tailWord_1657857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657857).length < 2 ^ (prefixWord ++ tailWord_1657857).sum := by decide
  have hdescent : baseEnd_1657857 < baseStart_1657857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657887 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 1, 4]
def baseStart_1657887 : Nat := 118140960795 + 1657887 * 2 ^ 59
def prefixEnd_1657887 : Nat := 4983230072969 + 3 ^ 40 * 1657887 * 2
def baseEnd_1657887 : Nat := 567528601227106828792015

theorem tailTrace_1657887 : CollatzResearch.WordTrace tailWord_1657887 prefixEnd_1657887 567528601227106828792015 := by
  unfold tailWord_1657887
  simp only [CollatzResearch.WordTrace]
  refine ⟨60468106544766018402419915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40312071029844012268279943 60468106544766018402419915)
  ·
    refine ⟨90702159817149027603629873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60468106544766018402419915 90702159817149027603629873)
    ·
      refine ⟨68026619862861770702722405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90702159817149027603629873 68026619862861770702722405)
      ·
        refine ⟨12754991224286582006760451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68026619862861770702722405 12754991224286582006760451)
        ·
          refine ⟨19132486836429873010140677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12754991224286582006760451 19132486836429873010140677)
          ·
            refine ⟨3587341281830601189401377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19132486836429873010140677 3587341281830601189401377)
            ·
              refine ⟨2690505961372950892051033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587341281830601189401377 2690505961372950892051033)
              ·
                refine ⟨2017879471029713169038275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690505961372950892051033 2017879471029713169038275)
                ·
                  refine ⟨3026819206544569753557413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017879471029713169038275 3026819206544569753557413)
                  ·
                    refine ⟨567528601227106828792015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3026819206544569753557413 567528601227106828792015)
                    ·
                      rfl

theorem cell22_1657887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_1657887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657887 prefixEnd_1657887 := by exact prefixLift 1657887
  have htrace : WordTrace (prefixWord ++ tailWord_1657887) baseStart_1657887 baseEnd_1657887 := by
    simpa [prefixWord, tailWord_1657887, baseEnd_1657887] using wordTrace_append hprefix tailTrace_1657887
  have hstable : (prefixWord ++ tailWord_1657887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657887).length < 2 ^ (prefixWord ++ tailWord_1657887).sum := by decide
  have hdescent : baseEnd_1657887 < baseStart_1657887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657900 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_1657900 : Nat := 118140960795 + 1657900 * 2 ^ 59
def prefixEnd_1657900 : Nat := 4983230072969 + 3 ^ 40 * 1657900 * 2
def baseEnd_1657900 : Nat := 567533051392779128216975

theorem tailTrace_1657900 : CollatzResearch.WordTrace tailWord_1657900 prefixEnd_1657900 567533051392779128216975 := by
  unfold tailWord_1657900
  simp only [CollatzResearch.WordTrace]
  refine ⟨30234290346859460811321577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40312387129145947748428769 30234290346859460811321577)
  ·
    refine ⟨22675717760144595608491183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30234290346859460811321577 22675717760144595608491183)
    ·
      refine ⟨34013576640216893412736775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22675717760144595608491183 34013576640216893412736775)
      ·
        refine ⟨51020364960325340119105163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34013576640216893412736775 51020364960325340119105163)
        ·
          refine ⟨76530547440488010178657745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51020364960325340119105163 76530547440488010178657745)
          ·
            refine ⟨57397910580366007633993309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76530547440488010178657745 57397910580366007633993309)
            ·
              refine ⟨21524216467637252862747491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57397910580366007633993309 21524216467637252862747491)
              ·
                refine ⟨32286324701455879294121237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21524216467637252862747491 32286324701455879294121237)
                ·
                  refine ⟨1513421470380744341911933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32286324701455879294121237 1513421470380744341911933)
                  ·
                    refine ⟨567533051392779128216975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1513421470380744341911933 567533051392779128216975)
                    ·
                      rfl

theorem cell22_1657900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_1657900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657900 prefixEnd_1657900 := by exact prefixLift 1657900
  have htrace : WordTrace (prefixWord ++ tailWord_1657900) baseStart_1657900 baseEnd_1657900 := by
    simpa [prefixWord, tailWord_1657900, baseEnd_1657900] using wordTrace_append hprefix tailTrace_1657900
  have hstable : (prefixWord ++ tailWord_1657900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657900).length < 2 ^ (prefixWord ++ tailWord_1657900).sum := by decide
  have hdescent : baseEnd_1657900 < baseStart_1657900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1657917 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1657917 : Nat := 118140960795 + 1657917 * 2 ^ 59
def prefixEnd_1657917 : Nat := 4983230072969 + 3 ^ 40 * 1657917 * 2
def baseEnd_1657917 : Nat := 567538870840196750541923

theorem tailTrace_1657917 : CollatzResearch.WordTrace tailWord_1657917 prefixEnd_1657917 567538870840196750541923 := by
  unfold tailWord_1657917
  simp only [CollatzResearch.WordTrace]
  refine ⟨60469200734657333526012005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40312800489771555684008003 60469200734657333526012005)
  ·
    refine ⟨11337975137748250036127251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60469200734657333526012005 11337975137748250036127251)
    ·
      refine ⟨17006962706622375054190877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11337975137748250036127251 17006962706622375054190877)
      ·
        refine ⟨6377611014983390645321579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17006962706622375054190877 6377611014983390645321579)
        ·
          refine ⟨9566416522475085967982369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6377611014983390645321579 9566416522475085967982369)
          ·
            refine ⟨7174812391856314475986777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9566416522475085967982369 7174812391856314475986777)
            ·
              refine ⟨5381109293892235856990083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7174812391856314475986777 5381109293892235856990083)
              ·
                refine ⟨8071663940838353785485125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381109293892235856990083 8071663940838353785485125)
                ·
                  refine ⟨1513436988907191334778461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8071663940838353785485125 1513436988907191334778461)
                  ·
                    refine ⟨567538870840196750541923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1513436988907191334778461 567538870840196750541923)
                    ·
                      rfl

theorem cell22_1657917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1657917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1657917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1657917 prefixEnd_1657917 := by exact prefixLift 1657917
  have htrace : WordTrace (prefixWord ++ tailWord_1657917) baseStart_1657917 baseEnd_1657917 := by
    simpa [prefixWord, tailWord_1657917, baseEnd_1657917] using wordTrace_append hprefix tailTrace_1657917
  have hstable : (prefixWord ++ tailWord_1657917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1657917).length < 2 ^ (prefixWord ++ tailWord_1657917).sum := by decide
  have hdescent : baseEnd_1657917 < baseStart_1657917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1657917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658026 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_1658026 : Nat := 118140960795 + 1658026 * 2 ^ 59
def prefixEnd_1658026 : Nat := 4983230072969 + 3 ^ 40 * 1658026 * 2
def baseEnd_1658026 : Nat := 189192061255918933188863

theorem tailTrace_1658026 : CollatzResearch.WordTrace tailWord_1658026 prefixEnd_1658026 189192061255918933188863 := by
  unfold tailWord_1658026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15118294072815611285432483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40315450860841630094486621 15118294072815611285432483)
  ·
    refine ⟨22677441109223416928148725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15118294072815611285432483 22677441109223416928148725)
    ·
      refine ⟨2126010103989695337013943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22677441109223416928148725 2126010103989695337013943)
      ·
        refine ⟨3189015155984543005520915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126010103989695337013943 3189015155984543005520915)
        ·
          refine ⟨4783522733976814508281373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189015155984543005520915 4783522733976814508281373)
          ·
            refine ⟨1793821025241305440605515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4783522733976814508281373 1793821025241305440605515)
            ·
              refine ⟨2690731537861958160908273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793821025241305440605515 2690731537861958160908273)
              ·
                refine ⟨2018048653396468620681205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690731537861958160908273 2018048653396468620681205)
                ·
                  refine ⟨189192061255918933188863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2018048653396468620681205 189192061255918933188863)
                  ·
                    rfl

theorem cell22_1658026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_1658026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658026 prefixEnd_1658026 := by exact prefixLift 1658026
  have htrace : WordTrace (prefixWord ++ tailWord_1658026) baseStart_1658026 baseEnd_1658026 := by
    simpa [prefixWord, tailWord_1658026, baseEnd_1658026] using wordTrace_append hprefix tailTrace_1658026
  have hstable : (prefixWord ++ tailWord_1658026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658026).length < 2 ^ (prefixWord ++ tailWord_1658026).sum := by decide
  have hdescent : baseEnd_1658026 < baseStart_1658026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658035 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 3, 5]
def baseStart_1658035 : Nat := 118140960795 + 1658035 * 2 ^ 59
def prefixEnd_1658035 : Nat := 4983230072969 + 3 ^ 40 * 1658035 * 2
def baseEnd_1658035 : Nat := 567579264651683776091561

theorem tailTrace_1658035 : CollatzResearch.WordTrace tailWord_1658035 prefixEnd_1658035 567579264651683776091561 := by
  unfold tailWord_1658035
  simp only [CollatzResearch.WordTrace]
  refine ⟨60473504548229839678807559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40315669698819893119205039 60473504548229839678807559)
  ·
    refine ⟨90710256822344759518211339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60473504548229839678807559 90710256822344759518211339)
    ·
      refine ⟨136065385233517139277317009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90710256822344759518211339 136065385233517139277317009)
      ·
        refine ⟨102049038925137854457987757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136065385233517139277317009 102049038925137854457987757)
        ·
          refine ⟨38268389596926695421745409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102049038925137854457987757 38268389596926695421745409)
          ·
            refine ⟨28701292197695021566309057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38268389596926695421745409 28701292197695021566309057)
            ·
              refine ⟨21525969148271266174731793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28701292197695021566309057 21525969148271266174731793)
              ·
                refine ⟨16144476861203449631048845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21525969148271266174731793 16144476861203449631048845)
                ·
                  refine ⟨6054178822951293611643317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16144476861203449631048845 6054178822951293611643317)
                  ·
                    refine ⟨567579264651683776091561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6054178822951293611643317 567579264651683776091561)
                    ·
                      rfl

theorem cell22_1658035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_1658035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658035 prefixEnd_1658035 := by exact prefixLift 1658035
  have htrace : WordTrace (prefixWord ++ tailWord_1658035) baseStart_1658035 baseEnd_1658035 := by
    simpa [prefixWord, tailWord_1658035, baseEnd_1658035] using wordTrace_append hprefix tailTrace_1658035
  have hstable : (prefixWord ++ tailWord_1658035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658035).length < 2 ^ (prefixWord ++ tailWord_1658035).sum := by decide
  have hdescent : baseEnd_1658035 < baseStart_1658035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658069 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_1658069 : Nat := 118140960795 + 1658069 * 2 ^ 59
def prefixEnd_1658069 : Nat := 4983230072969 + 3 ^ 40 * 1658069 * 2
def baseEnd_1658069 : Nat := 567590903546519020741457

theorem tailTrace_1658069 : CollatzResearch.WordTrace tailWord_1658069 prefixEnd_1658069 567590903546519020741457 := by
  unfold tailWord_1658069
  simp only [CollatzResearch.WordTrace]
  refine ⟨60474744630106663485545261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40316496420071108990363507 60474744630106663485545261)
  ·
    refine ⟨22678029236289998807079473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60474744630106663485545261 22678029236289998807079473)
    ·
      refine ⟨17008521927217499105309605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22678029236289998807079473 17008521927217499105309605)
      ·
        refine ⟨3189097861353281082245551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17008521927217499105309605 3189097861353281082245551)
        ·
          refine ⟨4783646792029921623368327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189097861353281082245551 4783646792029921623368327)
          ·
            refine ⟨7175470188044882435052491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4783646792029921623368327 7175470188044882435052491)
            ·
              refine ⟨10763205282067323652578737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7175470188044882435052491 10763205282067323652578737)
              ·
                refine ⟨8072403961550492739434053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10763205282067323652578737 8072403961550492739434053)
                ·
                  refine ⟨1513575742790717388643885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8072403961550492739434053 1513575742790717388643885)
                  ·
                    refine ⟨567590903546519020741457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1513575742790717388643885 567590903546519020741457)
                    ·
                      rfl

theorem cell22_1658069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_1658069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658069 prefixEnd_1658069 := by exact prefixLift 1658069
  have htrace : WordTrace (prefixWord ++ tailWord_1658069) baseStart_1658069 baseEnd_1658069 := by
    simpa [prefixWord, tailWord_1658069, baseEnd_1658069] using wordTrace_append hprefix tailTrace_1658069
  have hstable : (prefixWord ++ tailWord_1658069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658069).length < 2 ^ (prefixWord ++ tailWord_1658069).sum := by decide
  have hdescent : baseEnd_1658069 < baseStart_1658069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658172 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 8]
def baseStart_1658172 : Nat := 118140960795 + 1658172 * 2 ^ 59
def prefixEnd_1658172 : Nat := 4983230072969 + 3 ^ 40 * 1658172 * 2
def baseEnd_1658172 : Nat := 189208720850487028472047

theorem tailTrace_1658172 : CollatzResearch.WordTrace tailWord_1658172 prefixEnd_1658172 189208720850487028472047 := by
  unfold tailWord_1658172
  simp only [CollatzResearch.WordTrace]
  refine ⟨30239250674366756038272385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40319000899155674717696513 30239250674366756038272385)
  ·
    refine ⟨22679438005775067028704289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30239250674366756038272385 22679438005775067028704289)
    ·
      refine ⟨17009578504331300271528217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22679438005775067028704289 17009578504331300271528217)
      ·
        refine ⟨12757183878248475203646163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17009578504331300271528217 12757183878248475203646163)
        ·
          refine ⟨19135775817372712805469245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12757183878248475203646163 19135775817372712805469245)
          ·
            refine ⟨7175915931514767302050967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19135775817372712805469245 7175915931514767302050967)
            ·
              refine ⟨10763873897272150953076451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7175915931514767302050967 10763873897272150953076451)
              ·
                refine ⟨16145810845908226429614677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10763873897272150953076451 16145810845908226429614677)
                ·
                  refine ⟨189208720850487028472047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16145810845908226429614677 189208720850487028472047)
                  ·
                    rfl

theorem cell22_1658172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_1658172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658172 prefixEnd_1658172 := by exact prefixLift 1658172
  have htrace : WordTrace (prefixWord ++ tailWord_1658172) baseStart_1658172 baseEnd_1658172 := by
    simpa [prefixWord, tailWord_1658172, baseEnd_1658172] using wordTrace_append hprefix tailTrace_1658172
  have hstable : (prefixWord ++ tailWord_1658172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658172).length < 2 ^ (prefixWord ++ tailWord_1658172).sum := by decide
  have hdescent : baseEnd_1658172 < baseStart_1658172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658174 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1658174 : Nat := 118140960795 + 1658174 * 2 ^ 59
def prefixEnd_1658174 : Nat := 4983230072969 + 3 ^ 40 * 1658174 * 2
def baseEnd_1658174 : Nat := 567626847192333746866135

theorem tailTrace_1658174 : CollatzResearch.WordTrace tailWord_1658174 prefixEnd_1658174 567626847192333746866135 := by
  unfold tailWord_1658174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7559821786840783302264697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40319049529817510945411717 7559821786840783302264697)
  ·
    refine ⟨5669866340130587476698523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7559821786840783302264697 5669866340130587476698523)
    ·
      refine ⟨8504799510195881215047785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5669866340130587476698523 8504799510195881215047785)
      ·
        refine ⟨6378599632646910911285839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8504799510195881215047785 6378599632646910911285839)
        ·
          refine ⟨9567899448970366366928759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378599632646910911285839 9567899448970366366928759)
          ·
            refine ⟨14351849173455549550393139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9567899448970366366928759 14351849173455549550393139)
            ·
              refine ⟨21527773760183324325589709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14351849173455549550393139 21527773760183324325589709)
              ·
                refine ⟨8072915160068746622096141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21527773760183324325589709 8072915160068746622096141)
                ·
                  refine ⟨3027343185025779983286053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8072915160068746622096141 3027343185025779983286053)
                  ·
                    refine ⟨567626847192333746866135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3027343185025779983286053 567626847192333746866135)
                    ·
                      rfl

theorem cell22_1658174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1658174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658174 prefixEnd_1658174 := by exact prefixLift 1658174
  have htrace : WordTrace (prefixWord ++ tailWord_1658174) baseStart_1658174 baseEnd_1658174 := by
    simpa [prefixWord, tailWord_1658174, baseEnd_1658174] using wordTrace_append hprefix tailTrace_1658174
  have hstable : (prefixWord ++ tailWord_1658174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658174).length < 2 ^ (prefixWord ++ tailWord_1658174).sum := by decide
  have hdescent : baseEnd_1658174 < baseStart_1658174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658221 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1658221 : Nat := 118140960795 + 1658221 * 2 ^ 59
def prefixEnd_1658221 : Nat := 4983230072969 + 3 ^ 40 * 1658221 * 2
def baseEnd_1658221 : Nat := 567642936252841290940991

theorem tailTrace_1658221 : CollatzResearch.WordTrace tailWord_1658221 prefixEnd_1658221 567642936252841290940991 := by
  unfold tailWord_1658221
  simp only [CollatzResearch.WordTrace]
  refine ⟨60480288525555993445078517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40320192350370662296719011 60480288525555993445078517)
  ·
    refine ⟨5670027049270874385476111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60480288525555993445078517 5670027049270874385476111)
    ·
      refine ⟨8505040573906311578214167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5670027049270874385476111 8505040573906311578214167)
      ·
        refine ⟨12757560860859467367321251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8505040573906311578214167 12757560860859467367321251)
        ·
          refine ⟨19136341291289201050981877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12757560860859467367321251 19136341291289201050981877)
          ·
            refine ⟨1794031996058362598529551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19136341291289201050981877 1794031996058362598529551)
            ·
              refine ⟨2691047994087543897794327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794031996058362598529551 2691047994087543897794327)
              ·
                refine ⟨4036571991131315846691491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691047994087543897794327 4036571991131315846691491)
                ·
                  refine ⟨6054857986696973770037237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4036571991131315846691491 6054857986696973770037237)
                  ·
                    refine ⟨567642936252841290940991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6054857986696973770037237 567642936252841290940991)
                    ·
                      rfl

theorem cell22_1658221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1658221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658221 prefixEnd_1658221 := by exact prefixLift 1658221
  have htrace : WordTrace (prefixWord ++ tailWord_1658221) baseStart_1658221 baseEnd_1658221 := by
    simpa [prefixWord, tailWord_1658221, baseEnd_1658221] using wordTrace_append hprefix tailTrace_1658221
  have hstable : (prefixWord ++ tailWord_1658221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658221).length < 2 ^ (prefixWord ++ tailWord_1658221).sum := by decide
  have hdescent : baseEnd_1658221 < baseStart_1658221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658341 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 6]
def baseStart_1658341 : Nat := 118140960795 + 1658341 * 2 ^ 59
def prefixEnd_1658341 : Nat := 4983230072969 + 3 ^ 40 * 1658341 * 2
def baseEnd_1658341 : Nat := 189228004901733659313541

theorem tailTrace_1658341 : CollatzResearch.WordTrace tailWord_1658341 prefixEnd_1658341 189228004901733659313541 := by
  unfold tailWord_1658341
  simp only [CollatzResearch.WordTrace]
  refine ⟨60484665285121253939446877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40323110190080835959631251 60484665285121253939446877)
  ·
    refine ⟨22681749481920470227292579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60484665285121253939446877 22681749481920470227292579)
    ·
      refine ⟨34022624222880705340938869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22681749481920470227292579 34022624222880705340938869)
      ·
        refine ⟨3189621020895066125713019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34022624222880705340938869 3189621020895066125713019)
        ·
          refine ⟨4784431531342599188569529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189621020895066125713019 4784431531342599188569529)
          ·
            refine ⟨3588323648506949391427147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4784431531342599188569529 3588323648506949391427147)
            ·
              refine ⟨5382485472760424087140721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588323648506949391427147 5382485472760424087140721)
              ·
                refine ⟨4036864104570318065355541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5382485472760424087140721 4036864104570318065355541)
                ·
                  refine ⟨189228004901733659313541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4036864104570318065355541 189228004901733659313541)
                  ·
                    rfl

theorem cell22_1658341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_1658341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658341 prefixEnd_1658341 := by exact prefixLift 1658341
  have htrace : WordTrace (prefixWord ++ tailWord_1658341) baseStart_1658341 baseEnd_1658341 := by
    simpa [prefixWord, tailWord_1658341, baseEnd_1658341] using wordTrace_append hprefix tailTrace_1658341
  have hstable : (prefixWord ++ tailWord_1658341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658341).length < 2 ^ (prefixWord ++ tailWord_1658341).sum := by decide
  have hdescent : baseEnd_1658341 < baseStart_1658341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658358 : List Nat := [5, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_1658358 : Nat := 118140960795 + 1658358 * 2 ^ 59
def prefixEnd_1658358 : Nat := 4983230072969 + 3 ^ 40 * 1658358 * 2
def baseEnd_1658358 : Nat := 189229944717539533421857

theorem tailTrace_1658358 : CollatzResearch.WordTrace tailWord_1658358 prefixEnd_1658358 189229944717539533421857 := by
  unfold tailWord_1658358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780330332878729115175983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40323523550706443895210485 3780330332878729115175983)
  ·
    refine ⟨5670495499318093672763975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3780330332878729115175983 5670495499318093672763975)
    ·
      refine ⟨8505743248977140509145963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5670495499318093672763975 8505743248977140509145963)
      ·
        refine ⟨12758614873465710763718945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8505743248977140509145963 12758614873465710763718945)
        ·
          refine ⟨9568961155099283072789209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12758614873465710763718945 9568961155099283072789209)
          ·
            refine ⟨7176720866324462304591907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9568961155099283072789209 7176720866324462304591907)
            ·
              refine ⟨10765081299486693456887861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7176720866324462304591907 10765081299486693456887861)
              ·
                refine ⟨1009226371826877511583237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10765081299486693456887861 1009226371826877511583237)
                ·
                  refine ⟨189229944717539533421857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1009226371826877511583237 189229944717539533421857)
                  ·
                    rfl

theorem cell22_1658358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_1658358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658358 prefixEnd_1658358 := by exact prefixLift 1658358
  have htrace : WordTrace (prefixWord ++ tailWord_1658358) baseStart_1658358 baseEnd_1658358 := by
    simpa [prefixWord, tailWord_1658358, baseEnd_1658358] using wordTrace_append hprefix tailTrace_1658358
  have hstable : (prefixWord ++ tailWord_1658358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658358).length < 2 ^ (prefixWord ++ tailWord_1658358).sum := by decide
  have hdescent : baseEnd_1658358 < baseStart_1658358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658399 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 2, 6]
def baseStart_1658399 : Nat := 118140960795 + 1658399 * 2 ^ 59
def prefixEnd_1658399 : Nat := 4983230072969 + 3 ^ 40 * 1658399 * 2
def baseEnd_1658399 : Nat := 567703869290508159990445

theorem tailTrace_1658399 : CollatzResearch.WordTrace tailWord_1658399 prefixEnd_1658399 567703869290508159990445 := by
  unfold tailWord_1658399
  simp only [CollatzResearch.WordTrace]
  refine ⟨60486780718911129845058251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40324520479274086563372167 60486780718911129845058251)
  ·
    refine ⟨90730171078366694767587377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60486780718911129845058251 90730171078366694767587377)
    ·
      refine ⟨68047628308775021075690533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90730171078366694767587377 68047628308775021075690533)
      ·
        refine ⟨12758930307895316451691975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68047628308775021075690533 12758930307895316451691975)
        ·
          refine ⟨19138395461842974677537963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12758930307895316451691975 19138395461842974677537963)
          ·
            refine ⟨28707593192764462016306945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19138395461842974677537963 28707593192764462016306945)
            ·
              refine ⟨21530694894573346512230209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28707593192764462016306945 21530694894573346512230209)
              ·
                refine ⟨16148021170930009884172657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21530694894573346512230209 16148021170930009884172657)
                ·
                  refine ⟨12111015878197507413129493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16148021170930009884172657 12111015878197507413129493)
                  ·
                    refine ⟨567703869290508159990445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12111015878197507413129493 567703869290508159990445)
                    ·
                      rfl

theorem cell22_1658399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_1658399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658399 prefixEnd_1658399 := by exact prefixLift 1658399
  have htrace : WordTrace (prefixWord ++ tailWord_1658399) baseStart_1658399 baseEnd_1658399 := by
    simpa [prefixWord, tailWord_1658399, baseEnd_1658399] using wordTrace_append hprefix tailTrace_1658399
  have hstable : (prefixWord ++ tailWord_1658399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658399).length < 2 ^ (prefixWord ++ tailWord_1658399).sum := by decide
  have hdescent : baseEnd_1658399 < baseStart_1658399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658403 : List Nat := [1, 1, 1, 4, 5, 2, 2, 6]
def baseStart_1658403 : Nat := 118140960795 + 1658403 * 2 ^ 59
def prefixEnd_1658403 : Nat := 4983230072969 + 3 ^ 40 * 1658403 * 2
def baseEnd_1658403 : Nat := 63078359841361498098937

theorem tailTrace_1658403 : CollatzResearch.WordTrace tailWord_1658403 prefixEnd_1658403 63078359841361498098937 := by
  unfold tailWord_1658403
  simp only [CollatzResearch.WordTrace]
  refine ⟨60486926610896638528203863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40324617740597759018802575 60486926610896638528203863)
  ·
    refine ⟨90730389916344957792305795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60486926610896638528203863 90730389916344957792305795)
    ·
      refine ⟨136095584874517436688458693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90730389916344957792305795 136095584874517436688458693)
      ·
        refine ⟨25517922163972019379086005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136095584874517436688458693 25517922163972019379086005)
        ·
          refine ⟨2392305202872376816789313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25517922163972019379086005 2392305202872376816789313)
          ·
            refine ⟨1794228902154282612591985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392305202872376816789313 1794228902154282612591985)
            ·
              refine ⟨1345671676615711959443989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794228902154282612591985 1345671676615711959443989)
              ·
                refine ⟨63078359841361498098937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1345671676615711959443989 63078359841361498098937)
                ·
                  rfl

theorem cell22_1658403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 6].length) (baseStart_1658403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658403 prefixEnd_1658403 := by exact prefixLift 1658403
  have htrace : WordTrace (prefixWord ++ tailWord_1658403) baseStart_1658403 baseEnd_1658403 := by
    simpa [prefixWord, tailWord_1658403, baseEnd_1658403] using wordTrace_append hprefix tailTrace_1658403
  have hstable : (prefixWord ++ tailWord_1658403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658403).length < 2 ^ (prefixWord ++ tailWord_1658403).sum := by decide
  have hdescent : baseEnd_1658403 < baseStart_1658403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658508 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_1658508 : Nat := 118140960795 + 1658508 * 2 ^ 59
def prefixEnd_1658508 : Nat := 4983230072969 + 3 ^ 40 * 1658508 * 2
def baseEnd_1658508 : Nat := 567741182218068209015111

theorem tailTrace_1658508 : CollatzResearch.WordTrace tailWord_1658508 prefixEnd_1658508 567741182218068209015111 := by
  unfold tailWord_1658508
  simp only [CollatzResearch.WordTrace]
  refine ⟨30245378137758120730388089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40327170850344160973850785 30245378137758120730388089)
  ·
    refine ⟨22684033603318590547791067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30245378137758120730388089 22684033603318590547791067)
    ·
      refine ⟨34026050404977885821686601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22684033603318590547791067 34026050404977885821686601)
      ·
        refine ⟨25519537803733414366264951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34026050404977885821686601 25519537803733414366264951)
        ·
          refine ⟨38279306705600121549397427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25519537803733414366264951 38279306705600121549397427)
          ·
            refine ⟨57418960058400182324096141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38279306705600121549397427 57418960058400182324096141)
            ·
              refine ⟨21532110021900068371536053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57418960058400182324096141 21532110021900068371536053)
              ·
                refine ⟨2018635314553131409831505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21532110021900068371536053 2018635314553131409831505)
                ·
                  refine ⟨1513976485914848557373629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2018635314553131409831505 1513976485914848557373629)
                  ·
                    refine ⟨567741182218068209015111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1513976485914848557373629 567741182218068209015111)
                    ·
                      rfl

theorem cell22_1658508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_1658508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658508 prefixEnd_1658508 := by exact prefixLift 1658508
  have htrace : WordTrace (prefixWord ++ tailWord_1658508) baseStart_1658508 baseEnd_1658508 := by
    simpa [prefixWord, tailWord_1658508, baseEnd_1658508] using wordTrace_append hprefix tailTrace_1658508
  have hstable : (prefixWord ++ tailWord_1658508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658508).length < 2 ^ (prefixWord ++ tailWord_1658508).sum := by decide
  have hdescent : baseEnd_1658508 < baseStart_1658508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658527 : List Nat := [1, 1, 2, 7, 1, 1, 2, 3, 4]
def baseStart_1658527 : Nat := 118140960795 + 1658527 * 2 ^ 59
def prefixEnd_1658527 : Nat := 4983230072969 + 3 ^ 40 * 1658527 * 2
def baseEnd_1658527 : Nat := 189249228768786164263351

theorem tailTrace_1658527 : CollatzResearch.WordTrace tailWord_1658527 prefixEnd_1658527 189249228768786164263351 := by
  unfold tailWord_1658527
  simp only [CollatzResearch.WordTrace]
  refine ⟨60491449262447407705717835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40327632841631605137145223 60491449262447407705717835)
  ·
    refine ⟨90737173893671111558576753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60491449262447407705717835 90737173893671111558576753)
    ·
      refine ⟨68052880420253333668932565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90737173893671111558576753 68052880420253333668932565)
      ·
        refine ⟨1594989384849687507865607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 68052880420253333668932565 1594989384849687507865607)
        ·
          refine ⟨2392484077274531261798411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594989384849687507865607 2392484077274531261798411)
          ·
            refine ⟨3588726115911796892697617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392484077274531261798411 3588726115911796892697617)
            ·
              refine ⟨2691544586933847669523213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588726115911796892697617 2691544586933847669523213)
              ·
                refine ⟨1009329220100192876071205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2691544586933847669523213 1009329220100192876071205)
                ·
                  refine ⟨189249228768786164263351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1009329220100192876071205 189249228768786164263351)
                  ·
                    rfl

theorem cell22_1658527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 4].length) (baseStart_1658527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658527 prefixEnd_1658527 := by exact prefixLift 1658527
  have htrace : WordTrace (prefixWord ++ tailWord_1658527) baseStart_1658527 baseEnd_1658527 := by
    simpa [prefixWord, tailWord_1658527, baseEnd_1658527] using wordTrace_append hprefix tailTrace_1658527
  have hstable : (prefixWord ++ tailWord_1658527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658527).length < 2 ^ (prefixWord ++ tailWord_1658527).sum := by decide
  have hdescent : baseEnd_1658527 < baseStart_1658527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658542 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1658542 : Nat := 118140960795 + 1658542 * 2 ^ 59
def prefixEnd_1658542 : Nat := 4983230072969 + 3 ^ 40 * 1658542 * 2
def baseEnd_1658542 : Nat := 567752821112903453665007

theorem tailTrace_1658542 : CollatzResearch.WordTrace tailWord_1658542 prefixEnd_1658542 567752821112903453665007 := by
  unfold tailWord_1658542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7561499544674133158439235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40327997571595376845009253 7561499544674133158439235)
  ·
    refine ⟨11342249317011199737658853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7561499544674133158439235 11342249317011199737658853)
    ·
      refine ⟨2126671746939599950811035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11342249317011199737658853 2126671746939599950811035)
      ·
        refine ⟨3190007620409399926216553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126671746939599950811035 3190007620409399926216553)
        ·
          refine ⟨2392505715307049944662415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3190007620409399926216553 2392505715307049944662415)
          ·
            refine ⟨3588758572960574916993623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392505715307049944662415 3588758572960574916993623)
            ·
              refine ⟨5383137859440862375490435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588758572960574916993623 5383137859440862375490435)
              ·
                refine ⟨8074706789161293563235653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383137859440862375490435 8074706789161293563235653)
                ·
                  refine ⟨1514007522967742543106685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8074706789161293563235653 1514007522967742543106685)
                  ·
                    refine ⟨567752821112903453665007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1514007522967742543106685 567752821112903453665007)
                    ·
                      rfl

theorem cell22_1658542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1658542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658542 prefixEnd_1658542 := by exact prefixLift 1658542
  have htrace : WordTrace (prefixWord ++ tailWord_1658542) baseStart_1658542 baseEnd_1658542 := by
    simpa [prefixWord, tailWord_1658542, baseEnd_1658542] using wordTrace_append hprefix tailTrace_1658542
  have hstable : (prefixWord ++ tailWord_1658542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658542).length < 2 ^ (prefixWord ++ tailWord_1658542).sum := by decide
  have hdescent : baseEnd_1658542 < baseStart_1658542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658553 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 3, 3]
def baseStart_1658553 : Nat := 118140960795 + 1658553 * 2 ^ 59
def prefixEnd_1658553 : Nat := 4983230072969 + 3 ^ 40 * 1658553 * 2
def baseEnd_1658553 : Nat := 567756586637703091639973

theorem tailTrace_1658553 : CollatzResearch.WordTrace tailWord_1658553 prefixEnd_1658553 567756586637703091639973 := by
  unfold tailWord_1658553
  simp only [CollatzResearch.WordTrace]
  refine ⟨60492397560353214146164313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40328265040235476097442875 60492397560353214146164313)
  ·
    refine ⟨45369298170264910609623235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60492397560353214146164313 45369298170264910609623235)
    ·
      refine ⟨68053947255397365914434853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45369298170264910609623235 68053947255397365914434853)
      ·
        refine ⟨12760115110387006108956535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68053947255397365914434853 12760115110387006108956535)
        ·
          refine ⟨19140172665580509163434803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12760115110387006108956535 19140172665580509163434803)
          ·
            refine ⟨28710258998370763745152205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19140172665580509163434803 28710258998370763745152205)
            ·
              refine ⟨10766347124389036404432077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28710258998370763745152205 10766347124389036404432077)
              ·
                refine ⟨4037380171645888651662029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10766347124389036404432077 4037380171645888651662029)
                ·
                  refine ⟨1514017564367208244373261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4037380171645888651662029 1514017564367208244373261)
                  ·
                    refine ⟨567756586637703091639973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1514017564367208244373261 567756586637703091639973)
                    ·
                      rfl

theorem cell22_1658553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_1658553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658553 prefixEnd_1658553 := by exact prefixLift 1658553
  have htrace : WordTrace (prefixWord ++ tailWord_1658553) baseStart_1658553 baseEnd_1658553 := by
    simpa [prefixWord, tailWord_1658553, baseEnd_1658553] using wordTrace_append hprefix tailTrace_1658553
  have hstable : (prefixWord ++ tailWord_1658553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658553).length < 2 ^ (prefixWord ++ tailWord_1658553).sum := by decide
  have hdescent : baseEnd_1658553 < baseStart_1658553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658572 : List Nat := [2, 2, 1, 5, 3, 1, 2, 6]
def baseStart_1658572 : Nat := 118140960795 + 1658572 * 2 ^ 59
def prefixEnd_1658572 : Nat := 4983230072969 + 3 ^ 40 * 1658572 * 2
def baseEnd_1658572 : Nat := 63084787858443708379435

theorem tailTrace_1658572 : CollatzResearch.WordTrace tailWord_1658572 prefixEnd_1658572 63084787858443708379435 := by
  unfold tailWord_1658572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30246545273642190195552985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40328727031522920260737313 30246545273642190195552985)
  ·
    refine ⟨22684908955231642646664739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30246545273642190195552985 22684908955231642646664739)
    ·
      refine ⟨34027363432847463969997109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22684908955231642646664739 34027363432847463969997109)
      ·
        refine ⟨3190065321829449747187229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34027363432847463969997109 3190065321829449747187229)
        ·
          refine ⟨1196274495686043655195211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3190065321829449747187229 1196274495686043655195211)
          ·
            refine ⟨1794411743529065482792817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196274495686043655195211 1794411743529065482792817)
            ·
              refine ⟨1345808807646799112094613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794411743529065482792817 1345808807646799112094613)
              ·
                refine ⟨63084787858443708379435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1345808807646799112094613 63084787858443708379435)
                ·
                  rfl

theorem cell22_1658572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 6].length) (baseStart_1658572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658572 prefixEnd_1658572 := by exact prefixLift 1658572
  have htrace : WordTrace (prefixWord ++ tailWord_1658572) baseStart_1658572 baseEnd_1658572 := by
    simpa [prefixWord, tailWord_1658572, baseEnd_1658572] using wordTrace_append hprefix tailTrace_1658572
  have hstable : (prefixWord ++ tailWord_1658572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658572).length < 2 ^ (prefixWord ++ tailWord_1658572).sum := by decide
  have hdescent : baseEnd_1658572 < baseStart_1658572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658643 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 4, 3]
def baseStart_1658643 : Nat := 118140960795 + 1658643 * 2 ^ 59
def prefixEnd_1658643 : Nat := 4983230072969 + 3 ^ 40 * 1658643 * 2
def baseEnd_1658643 : Nat := 567787395476972856889697

theorem tailTrace_1658643 : CollatzResearch.WordTrace tailWord_1658643 prefixEnd_1658643 567787395476972856889697 := by
  unfold tailWord_1658643
  simp only [CollatzResearch.WordTrace]
  refine ⟨60495680130027159516940583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40330453420018106344627055 60495680130027159516940583)
  ·
    refine ⟨90743520195040739275410875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60495680130027159516940583 90743520195040739275410875)
    ·
      refine ⟨136115280292561108913116313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90743520195040739275410875 136115280292561108913116313)
      ·
        refine ⟨102086460219420831684837235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136115280292561108913116313 102086460219420831684837235)
        ·
          refine ⟨153129690329131247527255853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102086460219420831684837235 153129690329131247527255853)
          ·
            refine ⟨57423633873424217822720945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153129690329131247527255853 57423633873424217822720945)
            ·
              refine ⟨43067725405068163367040709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57423633873424217822720945 43067725405068163367040709)
              ·
                refine ⟨8075198513450280631320133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43067725405068163367040709 8075198513450280631320133)
                ·
                  refine ⟨1514099721271927618372525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8075198513450280631320133 1514099721271927618372525)
                  ·
                    refine ⟨567787395476972856889697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1514099721271927618372525 567787395476972856889697)
                    ·
                      rfl

theorem cell22_1658643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 3].length) (baseStart_1658643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658643 prefixEnd_1658643 := by exact prefixLift 1658643
  have htrace : WordTrace (prefixWord ++ tailWord_1658643) baseStart_1658643 baseEnd_1658643 := by
    simpa [prefixWord, tailWord_1658643, baseEnd_1658643] using wordTrace_append hprefix tailTrace_1658643
  have hstable : (prefixWord ++ tailWord_1658643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658643).length < 2 ^ (prefixWord ++ tailWord_1658643).sum := by decide
  have hdescent : baseEnd_1658643 < baseStart_1658643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658647 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 1, 4]
def baseStart_1658647 : Nat := 118140960795 + 1658647 * 2 ^ 59
def prefixEnd_1658647 : Nat := 4983230072969 + 3 ^ 40 * 1658647 * 2
def baseEnd_1658647 : Nat := 567788764758718179789685

theorem tailTrace_1658647 : CollatzResearch.WordTrace tailWord_1658647 prefixEnd_1658647 567788764758718179789685 := by
  unfold tailWord_1658647
  simp only [CollatzResearch.WordTrace]
  refine ⟨60495826022012668200086195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40330550681341778800057463 60495826022012668200086195)
  ·
    refine ⟨90743739033019002300129293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60495826022012668200086195 90743739033019002300129293)
    ·
      refine ⟨34028902137382125862548485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90743739033019002300129293 34028902137382125862548485)
      ·
        refine ⟨6380419150759148599227841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34028902137382125862548485 6380419150759148599227841)
        ·
          refine ⟨4785314363069361449420881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6380419150759148599227841 4785314363069361449420881)
          ·
            refine ⟨3588985772302021087065661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4785314363069361449420881 3588985772302021087065661)
            ·
              refine ⟨1345869664613257907649623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3588985772302021087065661 1345869664613257907649623)
              ·
                refine ⟨2018804496919886861474435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345869664613257907649623 2018804496919886861474435)
                ·
                  refine ⟨3028206745379830292211653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018804496919886861474435 3028206745379830292211653)
                  ·
                    refine ⟨567788764758718179789685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028206745379830292211653 567788764758718179789685)
                    ·
                      rfl

theorem cell22_1658647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_1658647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658647 prefixEnd_1658647 := by exact prefixLift 1658647
  have htrace : WordTrace (prefixWord ++ tailWord_1658647) baseStart_1658647 baseEnd_1658647 := by
    simpa [prefixWord, tailWord_1658647, baseEnd_1658647] using wordTrace_append hprefix tailTrace_1658647
  have hstable : (prefixWord ++ tailWord_1658647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658647).length < 2 ^ (prefixWord ++ tailWord_1658647).sum := by decide
  have hdescent : baseEnd_1658647 < baseStart_1658647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658673 : List Nat := [1, 2, 2, 3, 2, 2, 3, 7]
def baseStart_1658673 : Nat := 118140960795 + 1658673 * 2 ^ 59
def prefixEnd_1658673 : Nat := 4983230072969 + 3 ^ 40 * 1658673 * 2
def baseEnd_1658673 : Nat := 63088629454451419848845

theorem tailTrace_1658673 : CollatzResearch.WordTrace tailWord_1658673 prefixEnd_1658673 63088629454451419848845 := by
  unfold tailWord_1658673
  simp only [CollatzResearch.WordTrace]
  refine ⟨60496774319918474640532673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40331182879945649760355115 60496774319918474640532673)
  ·
    refine ⟨45372580739938855980399505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60496774319918474640532673 45372580739938855980399505)
    ·
      refine ⟨34029435554954141985299629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45372580739938855980399505 34029435554954141985299629)
      ·
        refine ⟨12761038333107803244487361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34029435554954141985299629 12761038333107803244487361)
        ·
          refine ⟨9570778749830852433365521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12761038333107803244487361 9570778749830852433365521)
          ·
            refine ⟨7178084062373139325024141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9570778749830852433365521 7178084062373139325024141)
            ·
              refine ⟨2691781523389927246884053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7178084062373139325024141 2691781523389927246884053)
              ·
                refine ⟨63088629454451419848845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2691781523389927246884053 63088629454451419848845)
                ·
                  rfl

theorem cell22_1658673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 7].length) (baseStart_1658673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658673 prefixEnd_1658673 := by exact prefixLift 1658673
  have htrace : WordTrace (prefixWord ++ tailWord_1658673) baseStart_1658673 baseEnd_1658673 := by
    simpa [prefixWord, tailWord_1658673, baseEnd_1658673] using wordTrace_append hprefix tailTrace_1658673
  have hstable : (prefixWord ++ tailWord_1658673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658673).length < 2 ^ (prefixWord ++ tailWord_1658673).sum := by decide
  have hdescent : baseEnd_1658673 < baseStart_1658673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658722 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1658722 : Nat := 118140960795 + 1658722 * 2 ^ 59
def prefixEnd_1658722 : Nat := 4983230072969 + 3 ^ 40 * 1658722 * 2
def baseEnd_1658722 : Nat := 567814438791442984164455

theorem tailTrace_1658722 : CollatzResearch.WordTrace tailWord_1658722 prefixEnd_1658722 567814438791442984164455 := by
  unfold tailWord_1658722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124640374185239002266605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40332374331160637339377613 15124640374185239002266605)
  ·
    refine ⟨5671740140319464625849977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15124640374185239002266605 5671740140319464625849977)
    ·
      refine ⟨4253805105239598469387483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5671740140319464625849977 4253805105239598469387483)
      ·
        refine ⟨6380707657859397704081225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4253805105239598469387483 6380707657859397704081225)
        ·
          refine ⟨4785530743394548278060919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6380707657859397704081225 4785530743394548278060919)
          ·
            refine ⟨7178296115091822417091379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785530743394548278060919 7178296115091822417091379)
            ·
              refine ⟨10767444172637733625637069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7178296115091822417091379 10767444172637733625637069)
              ·
                refine ⟨4037791564739150109613901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10767444172637733625637069 4037791564739150109613901)
                ·
                  refine ⟨1514171836777181291105213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4037791564739150109613901 1514171836777181291105213)
                  ·
                    refine ⟨567814438791442984164455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1514171836777181291105213 567814438791442984164455)
                    ·
                      rfl

theorem cell22_1658722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1658722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658722 prefixEnd_1658722 := by exact prefixLift 1658722
  have htrace : WordTrace (prefixWord ++ tailWord_1658722) baseStart_1658722 baseEnd_1658722 := by
    simpa [prefixWord, tailWord_1658722, baseEnd_1658722] using wordTrace_append hprefix tailTrace_1658722
  have hstable : (prefixWord ++ tailWord_1658722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658722).length < 2 ^ (prefixWord ++ tailWord_1658722).sum := by decide
  have hdescent : baseEnd_1658722 < baseStart_1658722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658786 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1658786 : Nat := 118140960795 + 1658786 * 2 ^ 59
def prefixEnd_1658786 : Nat := 4983230072969 + 3 ^ 40 * 1658786 * 2
def baseEnd_1658786 : Nat := 189278782433122716854753

theorem tailTrace_1658786 : CollatzResearch.WordTrace tailWord_1658786 prefixEnd_1658786 189278782433122716854753 := by
  unfold tailWord_1658786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15125223942127273734849053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40333930512339396626264141 15125223942127273734849053)
  ·
    refine ⟨5671958978297727650568395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15125223942127273734849053 5671958978297727650568395)
    ·
      refine ⟨8507938467446591475852593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5671958978297727650568395 8507938467446591475852593)
      ·
        refine ⟨6380953850584943606889445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8507938467446591475852593 6380953850584943606889445)
        ·
          refine ⟨1196428846984676926291771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6380953850584943606889445 1196428846984676926291771)
          ·
            refine ⟨1794643270477015389437657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196428846984676926291771 1794643270477015389437657)
            ·
              refine ⟨1345982452857761542078243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794643270477015389437657 1345982452857761542078243)
              ·
                refine ⟨2018973679286642313117365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345982452857761542078243 2018973679286642313117365)
                ·
                  refine ⟨189278782433122716854753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2018973679286642313117365 189278782433122716854753)
                  ·
                    rfl

theorem cell22_1658786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1658786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658786 prefixEnd_1658786 := by exact prefixLift 1658786
  have htrace : WordTrace (prefixWord ++ tailWord_1658786) baseStart_1658786 baseEnd_1658786 := by
    simpa [prefixWord, tailWord_1658786, baseEnd_1658786] using wordTrace_append hprefix tailTrace_1658786
  have hstable : (prefixWord ++ tailWord_1658786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658786).length < 2 ^ (prefixWord ++ tailWord_1658786).sum := by decide
  have hdescent : baseEnd_1658786 < baseStart_1658786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658793 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_1658793 : Nat := 118140960795 + 1658793 * 2 ^ 59
def prefixEnd_1658793 : Nat := 4983230072969 + 3 ^ 40 * 1658793 * 2
def baseEnd_1658793 : Nat := 567838743542422465639237

theorem tailTrace_1658793 : CollatzResearch.WordTrace tailWord_1658793 prefixEnd_1658793 567838743542422465639237 := by
  unfold tailWord_1658793
  simp only [CollatzResearch.WordTrace]
  refine ⟨60501151079483735134901033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40334100719655823423267355 60501151079483735134901033)
  ·
    refine ⟨45375863309612801351175775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60501151079483735134901033 45375863309612801351175775)
    ·
      refine ⟨68063794964419202026763663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45375863309612801351175775 68063794964419202026763663)
      ·
        refine ⟨102095692446628803040145495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68063794964419202026763663 102095692446628803040145495)
        ·
          refine ⟨153143538669943204560218243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102095692446628803040145495 153143538669943204560218243)
          ·
            refine ⟨229715308004914806840327365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153143538669943204560218243 229715308004914806840327365)
            ·
              refine ⟨43071620250921526282561381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229715308004914806840327365 43071620250921526282561381)
              ·
                refine ⟨8075928797047786177980259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43071620250921526282561381 8075928797047786177980259)
                ·
                  refine ⟨12113893195571679266970389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075928797047786177980259 12113893195571679266970389)
                  ·
                    refine ⟨567838743542422465639237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12113893195571679266970389 567838743542422465639237)
                    ·
                      rfl

theorem cell22_1658793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_1658793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658793 prefixEnd_1658793 := by exact prefixLift 1658793
  have htrace : WordTrace (prefixWord ++ tailWord_1658793) baseStart_1658793 baseEnd_1658793 := by
    simpa [prefixWord, tailWord_1658793, baseEnd_1658793] using wordTrace_append hprefix tailTrace_1658793
  have hstable : (prefixWord ++ tailWord_1658793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658793).length < 2 ^ (prefixWord ++ tailWord_1658793).sum := by decide
  have hdescent : baseEnd_1658793 < baseStart_1658793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658808 : List Nat := [2, 1, 2, 1, 2, 3, 1, 10]
def baseStart_1658808 : Nat := 118140960795 + 1658808 * 2 ^ 59
def prefixEnd_1658808 : Nat := 4983230072969 + 3 ^ 40 * 1658808 * 2
def baseEnd_1658808 : Nat := 63093764260996380723799

theorem tailTrace_1658808 : CollatzResearch.WordTrace tailWord_1658808 prefixEnd_1658808 63093764260996380723799 := by
  unfold tailWord_1658808
  simp only [CollatzResearch.WordTrace]
  refine ⟨30250849087214696348348539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40334465449619595131131385 30250849087214696348348539)
  ·
    refine ⟨45376273630822044522522809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30250849087214696348348539 45376273630822044522522809)
    ·
      refine ⟨34032205223116533391892107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45376273630822044522522809 34032205223116533391892107)
      ·
        refine ⟨51048307834674800087838161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34032205223116533391892107 51048307834674800087838161)
        ·
          refine ⟨38286230876006100065878621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51048307834674800087838161 38286230876006100065878621)
          ·
            refine ⟨14357336578502287524704483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38286230876006100065878621 14357336578502287524704483)
            ·
              refine ⟨21536004867753431287056725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14357336578502287524704483 21536004867753431287056725)
              ·
                refine ⟨63093764260996380723799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21536004867753431287056725 63093764260996380723799)
                ·
                  rfl

theorem cell22_1658808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 10].length) (baseStart_1658808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658808 prefixEnd_1658808 := by exact prefixLift 1658808
  have htrace : WordTrace (prefixWord ++ tailWord_1658808) baseStart_1658808 baseEnd_1658808 := by
    simpa [prefixWord, tailWord_1658808, baseEnd_1658808] using wordTrace_append hprefix tailTrace_1658808
  have hstable : (prefixWord ++ tailWord_1658808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658808).length < 2 ^ (prefixWord ++ tailWord_1658808).sum := by decide
  have hdescent : baseEnd_1658808 < baseStart_1658808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658842 : List Nat := [3, 1, 1, 2, 5, 2, 1, 7]
def baseStart_1658842 : Nat := 118140960795 + 1658842 * 2 ^ 59
def prefixEnd_1658842 : Nat := 4983230072969 + 3 ^ 40 * 1658842 * 2
def baseEnd_1658842 : Nat := 63095057471533630129343

theorem tailTrace_1658842 : CollatzResearch.WordTrace tailWord_1658842 prefixEnd_1658842 63095057471533630129343 := by
  unfold tailWord_1658842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15125734564076554125858695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40335292170870811002289853 15125734564076554125858695)
  ·
    refine ⟨22688601846114831188788043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15125734564076554125858695 22688601846114831188788043)
    ·
      refine ⟨34032902769172246783182065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22688601846114831188788043 34032902769172246783182065)
      ·
        refine ⟨25524677076879185087386549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34032902769172246783182065 25524677076879185087386549)
        ·
          refine ⟨2392938475957423601942489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25524677076879185087386549 2392938475957423601942489)
          ·
            refine ⟨1794703856968067701456867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392938475957423601942489 1794703856968067701456867)
            ·
              refine ⟨2692055785452101552185301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794703856968067701456867 2692055785452101552185301)
              ·
                refine ⟨63095057471533630129343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2692055785452101552185301 63095057471533630129343)
                ·
                  rfl

theorem cell22_1658842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_1658842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658842 prefixEnd_1658842 := by exact prefixLift 1658842
  have htrace : WordTrace (prefixWord ++ tailWord_1658842) baseStart_1658842 baseEnd_1658842 := by
    simpa [prefixWord, tailWord_1658842, baseEnd_1658842] using wordTrace_append hprefix tailTrace_1658842
  have hstable : (prefixWord ++ tailWord_1658842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658842).length < 2 ^ (prefixWord ++ tailWord_1658842).sum := by decide
  have hdescent : baseEnd_1658842 < baseStart_1658842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658861 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_1658861 : Nat := 118140960795 + 1658861 * 2 ^ 59
def prefixEnd_1658861 : Nat := 4983230072969 + 3 ^ 40 * 1658861 * 2
def baseEnd_1658861 : Nat := 567862021332092954939029

theorem tailTrace_1658861 : CollatzResearch.WordTrace tailWord_1658861 prefixEnd_1658861 567862021332092954939029 := by
  unfold tailWord_1658861
  simp only [CollatzResearch.WordTrace]
  refine ⟨60503631243237382748376437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40335754162158255165584291 60503631243237382748376437)
  ·
    refine ⟨5672215429053504632660291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60503631243237382748376437 5672215429053504632660291)
    ·
      refine ⟨8508323143580256948990437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672215429053504632660291 8508323143580256948990437)
      ·
        refine ⟨1595310589421298177935707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8508323143580256948990437 1595310589421298177935707)
        ·
          refine ⟨2392965884131947266903561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595310589421298177935707 2392965884131947266903561)
          ·
            refine ⟨1794724413098960450177671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392965884131947266903561 1794724413098960450177671)
            ·
              refine ⟨2692086619648440675266507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794724413098960450177671 2692086619648440675266507)
              ·
                refine ⟨4038129929472661012899761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692086619648440675266507 4038129929472661012899761)
                ·
                  refine ⟨3028597447104495759674821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038129929472661012899761 3028597447104495759674821)
                  ·
                    refine ⟨567862021332092954939029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028597447104495759674821 567862021332092954939029)
                    ·
                      rfl

theorem cell22_1658861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_1658861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658861 prefixEnd_1658861 := by exact prefixLift 1658861
  have htrace : WordTrace (prefixWord ++ tailWord_1658861) baseStart_1658861 baseEnd_1658861 := by
    simpa [prefixWord, tailWord_1658861, baseEnd_1658861] using wordTrace_append hprefix tailTrace_1658861
  have hstable : (prefixWord ++ tailWord_1658861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658861).length < 2 ^ (prefixWord ++ tailWord_1658861).sum := by decide
  have hdescent : baseEnd_1658861 < baseStart_1658861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658885 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_1658885 : Nat := 118140960795 + 1658885 * 2 ^ 59
def prefixEnd_1658885 : Nat := 4983230072969 + 3 ^ 40 * 1658885 * 2
def baseEnd_1658885 : Nat := 567870237022564892338955

theorem tailTrace_1658885 : CollatzResearch.WordTrace tailWord_1658885 prefixEnd_1658885 567870237022564892338955 := by
  unfold tailWord_1658885
  simp only [CollatzResearch.WordTrace]
  refine ⟨60504506595150434847250109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40336337730100289898166739 60504506595150434847250109)
  ·
    refine ⟨22689189973181413067718791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60504506595150434847250109 22689189973181413067718791)
    ·
      refine ⟨34033784959772119601578187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22689189973181413067718791 34033784959772119601578187)
      ·
        refine ⟨51050677439658179402367281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34033784959772119601578187 51050677439658179402367281)
        ·
          refine ⟨38288008079743634551775461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51050677439658179402367281 38288008079743634551775461)
          ·
            refine ⟨7179001514951931478457899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38288008079743634551775461 7179001514951931478457899)
            ·
              refine ⟨10768502272427897217686849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7179001514951931478457899 10768502272427897217686849)
              ·
                refine ⟨8076376704320922913265137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10768502272427897217686849 8076376704320922913265137)
                ·
                  refine ⟨6057282528240692184948853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8076376704320922913265137 6057282528240692184948853)
                  ·
                    refine ⟨567870237022564892338955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6057282528240692184948853 567870237022564892338955)
                    ·
                      rfl

theorem cell22_1658885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_1658885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658885 prefixEnd_1658885 := by exact prefixLift 1658885
  have htrace : WordTrace (prefixWord ++ tailWord_1658885) baseStart_1658885 baseEnd_1658885 := by
    simpa [prefixWord, tailWord_1658885, baseEnd_1658885] using wordTrace_append hprefix tailTrace_1658885
  have hstable : (prefixWord ++ tailWord_1658885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658885).length < 2 ^ (prefixWord ++ tailWord_1658885).sum := by decide
  have hdescent : baseEnd_1658885 < baseStart_1658885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658887 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 5]
def baseStart_1658887 : Nat := 118140960795 + 1658887 * 2 ^ 59
def prefixEnd_1658887 : Nat := 4983230072969 + 3 ^ 40 * 1658887 * 2
def baseEnd_1658887 : Nat := 189290307221145851262983

theorem tailTrace_1658887 : CollatzResearch.WordTrace tailWord_1658887 prefixEnd_1658887 189290307221145851262983 := by
  unfold tailWord_1658887
  simp only [CollatzResearch.WordTrace]
  refine ⟨60504579541143189188822915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40336386360762126125881943 60504579541143189188822915)
  ·
    refine ⟨90756869311714783783234373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60504579541143189188822915 90756869311714783783234373)
    ·
      refine ⟨17016912995946521959356445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90756869311714783783234373 17016912995946521959356445)
      ·
        refine ⟨6381342373479945734758667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17016912995946521959356445 6381342373479945734758667)
        ·
          refine ⟨9572013560219918602138001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381342373479945734758667 9572013560219918602138001)
          ·
            refine ⟨7179010170164938951603501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9572013560219918602138001 7179010170164938951603501)
            ·
              refine ⟨2692128813811852106851313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7179010170164938951603501 2692128813811852106851313)
              ·
                refine ⟨2019096610358889080138485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692128813811852106851313 2019096610358889080138485)
                ·
                  refine ⟨189290307221145851262983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2019096610358889080138485 189290307221145851262983)
                  ·
                    rfl

theorem cell22_1658887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 5].length) (baseStart_1658887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658887 prefixEnd_1658887 := by exact prefixLift 1658887
  have htrace : WordTrace (prefixWord ++ tailWord_1658887) baseStart_1658887 baseEnd_1658887 := by
    simpa [prefixWord, tailWord_1658887, baseEnd_1658887] using wordTrace_append hprefix tailTrace_1658887
  have hstable : (prefixWord ++ tailWord_1658887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658887).length < 2 ^ (prefixWord ++ tailWord_1658887).sum := by decide
  have hdescent : baseEnd_1658887 < baseStart_1658887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658915 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 6]
def baseStart_1658915 : Nat := 118140960795 + 1658915 * 2 ^ 59
def prefixEnd_1658915 : Nat := 4983230072969 + 3 ^ 40 * 1658915 * 2
def baseEnd_1658915 : Nat := 189293502211884938029621

theorem tailTrace_1658915 : CollatzResearch.WordTrace tailWord_1658915 prefixEnd_1658915 189293502211884938029621 := by
  unfold tailWord_1658915
  simp only [CollatzResearch.WordTrace]
  refine ⟨60505600785041749970842199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40337067190027833313894799 60505600785041749970842199)
  ·
    refine ⟨90758401177562624956263299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60505600785041749970842199 90758401177562624956263299)
    ·
      refine ⟨136137601766343937434394949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90758401177562624956263299 136137601766343937434394949)
      ·
        refine ⟨25525800331189488268949053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136137601766343937434394949 25525800331189488268949053)
        ·
          refine ⟨9572175124196058100855895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25525800331189488268949053 9572175124196058100855895)
          ·
            refine ⟨14358262686294087151283843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572175124196058100855895 14358262686294087151283843)
            ·
              refine ⟨21537394029441130726925765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14358262686294087151283843 21537394029441130726925765)
              ·
                refine ⟨4038261380520212011298581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21537394029441130726925765 4038261380520212011298581)
                ·
                  refine ⟨189293502211884938029621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4038261380520212011298581 189293502211884938029621)
                  ·
                    rfl

theorem cell22_1658915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 6].length) (baseStart_1658915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658915 prefixEnd_1658915 := by exact prefixLift 1658915
  have htrace : WordTrace (prefixWord ++ tailWord_1658915) baseStart_1658915 baseEnd_1658915 := by
    simpa [prefixWord, tailWord_1658915, baseEnd_1658915] using wordTrace_append hprefix tailTrace_1658915
  have hstable : (prefixWord ++ tailWord_1658915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658915).length < 2 ^ (prefixWord ++ tailWord_1658915).sum := by decide
  have hdescent : baseEnd_1658915 < baseStart_1658915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658917 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_1658917 : Nat := 118140960795 + 1658917 * 2 ^ 59
def prefixEnd_1658917 : Nat := 4983230072969 + 3 ^ 40 * 1658917 * 2
def baseEnd_1658917 : Nat := 567881191276527475538857

theorem tailTrace_1658917 : CollatzResearch.WordTrace tailWord_1658917 prefixEnd_1658917 567881191276527475538857 := by
  unfold tailWord_1658917
  simp only [CollatzResearch.WordTrace]
  refine ⟨60505673731034504312415005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40337115820689669541610003 60505673731034504312415005)
  ·
    refine ⟨22689627649137939117155627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60505673731034504312415005 22689627649137939117155627)
    ·
      refine ⟨34034441473706908675733441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22689627649137939117155627 34034441473706908675733441)
      ·
        refine ⟨25525831105280181506800081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34034441473706908675733441 25525831105280181506800081)
        ·
          refine ⟨19144373328960136130100061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25525831105280181506800081 19144373328960136130100061)
          ·
            refine ⟨7179139998360051048787523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19144373328960136130100061 7179139998360051048787523)
            ·
              refine ⟨10768709997540076573181285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7179139998360051048787523 10768709997540076573181285)
              ·
                refine ⟨2019133124538764357471491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10768709997540076573181285 2019133124538764357471491)
                ·
                  refine ⟨3028699686808146536207237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019133124538764357471491 3028699686808146536207237)
                  ·
                    refine ⟨567881191276527475538857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028699686808146536207237 567881191276527475538857)
                    ·
                      rfl

theorem cell22_1658917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_1658917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658917 prefixEnd_1658917 := by exact prefixLift 1658917
  have htrace : WordTrace (prefixWord ++ tailWord_1658917) baseStart_1658917 baseEnd_1658917 := by
    simpa [prefixWord, tailWord_1658917, baseEnd_1658917] using wordTrace_append hprefix tailTrace_1658917
  have hstable : (prefixWord ++ tailWord_1658917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658917).length < 2 ^ (prefixWord ++ tailWord_1658917).sum := by decide
  have hdescent : baseEnd_1658917 < baseStart_1658917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1658934 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1658934 : Nat := 118140960795 + 1658934 * 2 ^ 59
def prefixEnd_1658934 : Nat := 4983230072969 + 3 ^ 40 * 1658934 * 2
def baseEnd_1658934 : Nat := 567887010723945097863805

theorem tailTrace_1658934 : CollatzResearch.WordTrace tailWord_1658934 prefixEnd_1658934 567887010723945097863805 := by
  unfold tailWord_1658934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781643360748307263486491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40337529181315277477189237 3781643360748307263486491)
  ·
    refine ⟨5672465041122460895229737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3781643360748307263486491 5672465041122460895229737)
    ·
      refine ⟨4254348780841845671422303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5672465041122460895229737 4254348780841845671422303)
      ·
        refine ⟨6381523171262768507133455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254348780841845671422303 6381523171262768507133455)
        ·
          refine ⟨9572284756894152760700183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381523171262768507133455 9572284756894152760700183)
          ·
            refine ⟨14358427135341229141050275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572284756894152760700183 14358427135341229141050275)
            ·
              refine ⟨21537640703011843711575413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14358427135341229141050275 21537640703011843711575413)
              ·
                refine ⟨2019153815907360347960195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21537640703011843711575413 2019153815907360347960195)
                ·
                  refine ⟨3028730723861040521940293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019153815907360347960195 3028730723861040521940293)
                  ·
                    refine ⟨567887010723945097863805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028730723861040521940293 567887010723945097863805)
                    ·
                      rfl

theorem cell22_1658934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1658934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1658934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1658934 prefixEnd_1658934 := by exact prefixLift 1658934
  have htrace : WordTrace (prefixWord ++ tailWord_1658934) baseStart_1658934 baseEnd_1658934 := by
    simpa [prefixWord, tailWord_1658934, baseEnd_1658934] using wordTrace_append hprefix tailTrace_1658934
  have hstable : (prefixWord ++ tailWord_1658934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1658934).length < 2 ^ (prefixWord ++ tailWord_1658934).sum := by decide
  have hdescent : baseEnd_1658934 < baseStart_1658934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1658934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659030 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1659030 : Nat := 118140960795 + 1659030 * 2 ^ 59
def prefixEnd_1659030 : Nat := 4983230072969 + 3 ^ 40 * 1659030 * 2
def baseEnd_1659030 : Nat := 567919873485832847463511

theorem tailTrace_1659030 : CollatzResearch.WordTrace tailWord_1659030 prefixEnd_1659030 567919873485832847463511 := by
  unfold tailWord_1659030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781862198726570288204909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40339863453083416407519029 3781862198726570288204909)
  ·
    refine ⟨1418198324522463858076841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3781862198726570288204909 1418198324522463858076841)
    ·
      refine ⟨1063648743391847893557631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1418198324522463858076841 1063648743391847893557631)
      ·
        refine ⟨1595473115087771840336447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063648743391847893557631 1595473115087771840336447)
        ·
          refine ⟨2393209672631657760504671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595473115087771840336447 2393209672631657760504671)
          ·
            refine ⟨3589814508947486640757007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393209672631657760504671 3589814508947486640757007)
            ·
              refine ⟨5384721763421229961135511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589814508947486640757007 5384721763421229961135511)
              ·
                refine ⟨8077082645131844941703267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384721763421229961135511 8077082645131844941703267)
                ·
                  refine ⟨12115623967697767412554901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8077082645131844941703267 12115623967697767412554901)
                  ·
                    refine ⟨567919873485832847463511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12115623967697767412554901 567919873485832847463511)
                    ·
                      rfl

theorem cell22_1659030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1659030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659030 prefixEnd_1659030 := by exact prefixLift 1659030
  have htrace : WordTrace (prefixWord ++ tailWord_1659030) baseStart_1659030 baseEnd_1659030 := by
    simpa [prefixWord, tailWord_1659030, baseEnd_1659030] using wordTrace_append hprefix tailTrace_1659030
  have hstable : (prefixWord ++ tailWord_1659030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659030).length < 2 ^ (prefixWord ++ tailWord_1659030).sum := by decide
  have hdescent : baseEnd_1659030 < baseStart_1659030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659035 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 2, 8]
def baseStart_1659035 : Nat := 118140960795 + 1659035 * 2 ^ 59
def prefixEnd_1659035 : Nat := 4983230072969 + 3 ^ 40 * 1659035 * 2
def baseEnd_1659035 : Nat := 567921585088014501088495

theorem tailTrace_1659035 : CollatzResearch.WordTrace tailWord_1659035 prefixEnd_1659035 567921585088014501088495 := by
  unfold tailWord_1659035
  simp only [CollatzResearch.WordTrace]
  refine ⟨60509977544607010465210559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40339985029738006976807039 60509977544607010465210559)
  ·
    refine ⟨90764966316910515697815839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60509977544607010465210559 90764966316910515697815839)
    ·
      refine ⟨136147449475365773546723759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90764966316910515697815839 136147449475365773546723759)
      ·
        refine ⟨204221174213048660320085639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136147449475365773546723759 204221174213048660320085639)
        ·
          refine ⟨306331761319572990480128459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204221174213048660320085639 306331761319572990480128459)
          ·
            refine ⟨459497641979359485720192689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306331761319572990480128459 459497641979359485720192689)
            ·
              refine ⟨344623231484519614290144517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459497641979359485720192689 344623231484519614290144517)
              ·
                refine ⟨64616855903347427679402097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344623231484519614290144517 64616855903347427679402097)
                ·
                  refine ⟨48462641927510570759551573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64616855903347427679402097 48462641927510570759551573)
                  ·
                    refine ⟨567921585088014501088495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48462641927510570759551573 567921585088014501088495)
                    ·
                      rfl

theorem cell22_1659035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_1659035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659035 prefixEnd_1659035 := by exact prefixLift 1659035
  have htrace : WordTrace (prefixWord ++ tailWord_1659035) baseStart_1659035 baseEnd_1659035 := by
    simpa [prefixWord, tailWord_1659035, baseEnd_1659035] using wordTrace_append hprefix tailTrace_1659035
  have hstable : (prefixWord ++ tailWord_1659035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659035).length < 2 ^ (prefixWord ++ tailWord_1659035).sum := by decide
  have hdescent : baseEnd_1659035 < baseStart_1659035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659067 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 6]
def baseStart_1659067 : Nat := 118140960795 + 1659067 * 2 ^ 59
def prefixEnd_1659067 : Nat := 4983230072969 + 3 ^ 40 * 1659067 * 2
def baseEnd_1659067 : Nat := 189310846447325694762799

theorem tailTrace_1659067 : CollatzResearch.WordTrace tailWord_1659067 prefixEnd_1659067 189310846447325694762799 := by
  unfold tailWord_1659067
  simp only [CollatzResearch.WordTrace]
  refine ⟨60511144680491079930375455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40340763120327386620250303 60511144680491079930375455)
  ·
    refine ⟨90766717020736619895563183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60511144680491079930375455 90766717020736619895563183)
    ·
      refine ⟨136150075531104929843344775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90766717020736619895563183 136150075531104929843344775)
      ·
        refine ⟨204225113296657394765017163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136150075531104929843344775 204225113296657394765017163)
        ·
          refine ⟨306337669944986092147525745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204225113296657394765017163 306337669944986092147525745)
          ·
            refine ⟨229753252458739569110644309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306337669944986092147525745 229753252458739569110644309)
            ·
              refine ⟨2692420927250854325515363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 229753252458739569110644309 2692420927250854325515363)
              ·
                refine ⟨4038631390876281488273045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692420927250854325515363 4038631390876281488273045)
                ·
                  refine ⟨189310846447325694762799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4038631390876281488273045 189310846447325694762799)
                  ·
                    rfl

theorem cell22_1659067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 6].length) (baseStart_1659067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659067 prefixEnd_1659067 := by exact prefixLift 1659067
  have htrace : WordTrace (prefixWord ++ tailWord_1659067) baseStart_1659067 baseEnd_1659067 := by
    simpa [prefixWord, tailWord_1659067, baseEnd_1659067] using wordTrace_append hprefix tailTrace_1659067
  have hstable : (prefixWord ++ tailWord_1659067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659067).length < 2 ^ (prefixWord ++ tailWord_1659067).sum := by decide
  have hdescent : baseEnd_1659067 < baseStart_1659067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
