import V185TrunkScan22Chunk428

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3826126 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_3826126 : Nat := 118140960795 + 3826126 * 2 ^ 59
def prefixEnd_3826126 : Nat := 4983230072969 + 3 ^ 40 * 3826126 * 2
def baseEnd_3826126 : Nat := 436587040592133888473105

theorem tailTrace_3826126 : CollatzResearch.WordTrace tailWord_3826126 prefixEnd_3826126 436587040592133888473105 := by
  unfold tailWord_3826126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443784967075803392759279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93033519824404284761382821 17443784967075803392759279)
  ·
    refine ⟨26165677450613705089138919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17443784967075803392759279 26165677450613705089138919)
    ·
      refine ⟨39248516175920557633708379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26165677450613705089138919 39248516175920557633708379)
      ·
        refine ⟨58872774263880836450562569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39248516175920557633708379 58872774263880836450562569)
        ·
          refine ⟨44154580697910627337921927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58872774263880836450562569 44154580697910627337921927)
          ·
            refine ⟨66231871046865941006882891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44154580697910627337921927 66231871046865941006882891)
            ·
              refine ⟨99347806570298911510324337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66231871046865941006882891 99347806570298911510324337)
              ·
                refine ⟨74510854927724183632743253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99347806570298911510324337 74510854927724183632743253)
                ·
                  refine ⟨436587040592133888473105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74510854927724183632743253 436587040592133888473105)
                  ·
                    rfl

theorem cell22_3826126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_3826126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826126 prefixEnd_3826126 := by exact prefixLift 3826126
  have htrace : WordTrace (prefixWord ++ tailWord_3826126) baseStart_3826126 baseEnd_3826126 := by
    simpa [prefixWord, tailWord_3826126, baseEnd_3826126] using wordTrace_append hprefix tailTrace_3826126
  have hstable : (prefixWord ++ tailWord_3826126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826126).length < 2 ^ (prefixWord ++ tailWord_3826126).sum := by decide
  have hdescent : baseEnd_3826126 < baseStart_3826126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826158 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_3826158 : Nat := 118140960795 + 3826158 * 2 ^ 59
def prefixEnd_3826158 : Nat := 4983230072969 + 3 ^ 40 * 3826158 * 2
def baseEnd_3826158 : Nat := 1309772076030364248619217

theorem tailTrace_3826158 : CollatzResearch.WordTrace tailWord_3826158 prefixEnd_3826158 1309772076030364248619217 := by
  unfold tailWord_3826158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17443930859061312075904891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93034297914993664404826085 17443930859061312075904891)
  ·
    refine ⟨26165896288591968113857337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17443930859061312075904891 26165896288591968113857337)
    ·
      refine ⟨19624422216443976085393003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26165896288591968113857337 19624422216443976085393003)
      ·
        refine ⟨29436633324665964128089505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19624422216443976085393003 29436633324665964128089505)
        ·
          refine ⟨22077474993499473096067129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29436633324665964128089505 22077474993499473096067129)
          ·
            refine ⟨16558106245124604822050347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22077474993499473096067129 16558106245124604822050347)
            ·
              refine ⟨24837159367686907233075521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16558106245124604822050347 24837159367686907233075521)
              ·
                refine ⟨18627869525765180424806641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24837159367686907233075521 18627869525765180424806641)
                ·
                  refine ⟨13970902144323885318604981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18627869525765180424806641 13970902144323885318604981)
                  ·
                    refine ⟨1309772076030364248619217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13970902144323885318604981 1309772076030364248619217)
                    ·
                      rfl

theorem cell22_3826158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_3826158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826158 prefixEnd_3826158 := by exact prefixLift 3826158
  have htrace : WordTrace (prefixWord ++ tailWord_3826158) baseStart_3826158 baseEnd_3826158 := by
    simpa [prefixWord, tailWord_3826158, baseEnd_3826158] using wordTrace_append hprefix tailTrace_3826158
  have hstable : (prefixWord ++ tailWord_3826158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826158).length < 2 ^ (prefixWord ++ tailWord_3826158).sum := by decide
  have hdescent : baseEnd_3826158 < baseStart_3826158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826188 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 6]
def baseStart_3826188 : Nat := 118140960795 + 3826188 * 2 ^ 59
def prefixEnd_3826188 : Nat := 4983230072969 + 3 ^ 40 * 3826188 * 2
def baseEnd_3826188 : Nat := 436594115214484723456375

theorem tailTrace_3826188 : CollatzResearch.WordTrace tailWord_3826188 prefixEnd_3826188 436594115214484723456375 := by
  unfold tailWord_3826188
  simp only [CollatzResearch.WordTrace]
  refine ⟨69776270531190905865415609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93035027374921207820554145 69776270531190905865415609)
  ·
    refine ⟨52332202898393179399061707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69776270531190905865415609 52332202898393179399061707)
    ·
      refine ⟨78498304347589769098592561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52332202898393179399061707 78498304347589769098592561)
      ·
        refine ⟨58873728260692326823944421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78498304347589769098592561 58873728260692326823944421)
        ·
          refine ⟨11038824048879811279489579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58873728260692326823944421 11038824048879811279489579)
          ·
            refine ⟨16558236073319716919234369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038824048879811279489579 16558236073319716919234369)
            ·
              refine ⟨12418677054989787689425777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16558236073319716919234369 12418677054989787689425777)
              ·
                refine ⟨9314007791242340767069333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12418677054989787689425777 9314007791242340767069333)
                ·
                  refine ⟨436594115214484723456375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9314007791242340767069333 436594115214484723456375)
                  ·
                    rfl

theorem cell22_3826188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_3826188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826188 prefixEnd_3826188 := by exact prefixLift 3826188
  have htrace : WordTrace (prefixWord ++ tailWord_3826188) baseStart_3826188 baseEnd_3826188 := by
    simpa [prefixWord, tailWord_3826188, baseEnd_3826188] using wordTrace_append hprefix tailTrace_3826188
  have hstable : (prefixWord ++ tailWord_3826188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826188).length < 2 ^ (prefixWord ++ tailWord_3826188).sum := by decide
  have hdescent : baseEnd_3826188 < baseStart_3826188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826190 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_3826190 : Nat := 118140960795 + 3826190 * 2 ^ 59
def prefixEnd_3826190 : Nat := 4983230072969 + 3 ^ 40 * 3826190 * 2
def baseEnd_3826190 : Nat := 1309783030284326831819119

theorem tailTrace_3826190 : CollatzResearch.WordTrace tailWord_3826190 prefixEnd_3826190 1309783030284326831819119 := by
  unfold tailWord_3826190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444076751046820759050503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93035076005583044048269349 17444076751046820759050503)
  ·
    refine ⟨26166115126570231138575755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17444076751046820759050503 26166115126570231138575755)
    ·
      refine ⟨39249172689855346707863633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26166115126570231138575755 39249172689855346707863633)
      ·
        refine ⟨29436879517391510030897725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39249172689855346707863633 29436879517391510030897725)
        ·
          refine ⟨11038829819021816261586647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29436879517391510030897725 11038829819021816261586647)
          ·
            refine ⟨16558244728532724392379971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038829819021816261586647 16558244728532724392379971)
            ·
              refine ⟨24837367092799086588569957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16558244728532724392379971 24837367092799086588569957)
              ·
                refine ⟨4657006329899828735356867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24837367092799086588569957 4657006329899828735356867)
                ·
                  refine ⟨6985509494849743103035301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657006329899828735356867 6985509494849743103035301)
                  ·
                    refine ⟨1309783030284326831819119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6985509494849743103035301 1309783030284326831819119)
                    ·
                      rfl

theorem cell22_3826190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_3826190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826190 prefixEnd_3826190 := by exact prefixLift 3826190
  have htrace : WordTrace (prefixWord ++ tailWord_3826190) baseStart_3826190 baseEnd_3826190 := by
    simpa [prefixWord, tailWord_3826190, baseEnd_3826190] using wordTrace_append hprefix tailTrace_3826190
  have hstable : (prefixWord ++ tailWord_3826190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826190).length < 2 ^ (prefixWord ++ tailWord_3826190).sum := by decide
  have hdescent : baseEnd_3826190 < baseStart_3826190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826222 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_3826222 : Nat := 118140960795 + 3826222 * 2 ^ 59
def prefixEnd_3826222 : Nat := 4983230072969 + 3 ^ 40 * 3826222 * 2
def baseEnd_3826222 : Nat := 436597994846096471673007

theorem tailTrace_3826222 : CollatzResearch.WordTrace tailWord_3826222 prefixEnd_3826222 436597994846096471673007 := by
  unfold tailWord_3826222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444222643032329442196115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93035854096172423691712613 17444222643032329442196115)
  ·
    refine ⟨26166333964548494163294173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17444222643032329442196115 26166333964548494163294173)
    ·
      refine ⟨9812375236705685311235315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26166333964548494163294173 9812375236705685311235315)
      ·
        refine ⟨14718562855058527966852973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9812375236705685311235315 14718562855058527966852973)
        ·
          refine ⟨5519461070646947987569865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14718562855058527966852973 5519461070646947987569865)
          ·
            refine ⟨4139595802985210990677399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5519461070646947987569865 4139595802985210990677399)
            ·
              refine ⟨6209393704477816486016099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139595802985210990677399 6209393704477816486016099)
              ·
                refine ⟨9314090556716724729024149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209393704477816486016099 9314090556716724729024149)
                ·
                  refine ⟨436597994846096471673007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9314090556716724729024149 436597994846096471673007)
                  ·
                    rfl

theorem cell22_3826222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_3826222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826222 prefixEnd_3826222 := by exact prefixLift 3826222
  have htrace : WordTrace (prefixWord ++ tailWord_3826222) baseStart_3826222 baseEnd_3826222 := by
    simpa [prefixWord, tailWord_3826222, baseEnd_3826222] using wordTrace_append hprefix tailTrace_3826222
  have hstable : (prefixWord ++ tailWord_3826222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826222).length < 2 ^ (prefixWord ++ tailWord_3826222).sum := by decide
  have hdescent : baseEnd_3826222 < baseStart_3826222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826233 : List Nat := [1, 2, 1, 5, 1, 1, 4, 7]
def baseStart_3826233 : Nat := 118140960795 + 3826233 * 2 ^ 59
def prefixEnd_3826233 : Nat := 4983230072969 + 3 ^ 40 * 3826233 * 2
def baseEnd_3826233 : Nat := 145533083340343228110443

theorem tailTrace_3826233 : CollatzResearch.WordTrace tailWord_3826233 prefixEnd_3826233 145533083340343228110443 := by
  unfold tailWord_3826233
  simp only [CollatzResearch.WordTrace]
  refine ⟨139554182347218784416219353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93036121564812522944146235 139554182347218784416219353)
  ·
    refine ⟨104665636760414088312164515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139554182347218784416219353 104665636760414088312164515)
    ·
      refine ⟨156998455140621132468246773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104665636760414088312164515 156998455140621132468246773)
      ·
        refine ⟨14718605169433231168898135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156998455140621132468246773 14718605169433231168898135)
        ·
          refine ⟨22077907754149846753347203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14718605169433231168898135 22077907754149846753347203)
          ·
            refine ⟨33116861631224770130020805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22077907754149846753347203 33116861631224770130020805)
            ·
              refine ⟨6209411555854644399378901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33116861631224770130020805 6209411555854644399378901)
              ·
                refine ⟨145533083340343228110443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6209411555854644399378901 145533083340343228110443)
                ·
                  rfl

theorem cell22_3826233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 7].length) (baseStart_3826233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826233 prefixEnd_3826233 := by exact prefixLift 3826233
  have htrace : WordTrace (prefixWord ++ tailWord_3826233) baseStart_3826233 baseEnd_3826233 := by
    simpa [prefixWord, tailWord_3826233, baseEnd_3826233] using wordTrace_append hprefix tailTrace_3826233
  have hstable : (prefixWord ++ tailWord_3826233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826233).length < 2 ^ (prefixWord ++ tailWord_3826233).sum := by decide
  have hdescent : baseEnd_3826233 < baseStart_3826233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826237 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_3826237 : Nat := 118140960795 + 3826237 * 2 ^ 59
def prefixEnd_3826237 : Nat := 4983230072969 + 3 ^ 40 * 3826237 * 2
def baseEnd_3826237 : Nat := 1309799119344834375893975

theorem tailTrace_3826237 : CollatzResearch.WordTrace tailWord_3826237 prefixEnd_3826237 1309799119344834375893975 := by
  unfold tailWord_3826237
  simp only [CollatzResearch.WordTrace]
  refine ⟨139554328239204293099364965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93036218826136195399576643 139554328239204293099364965)
  ·
    refine ⟨26166436544850804956130931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139554328239204293099364965 26166436544850804956130931)
    ·
      refine ⟨39249654817276207434196397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26166436544850804956130931 39249654817276207434196397)
      ·
        refine ⟨14718620556478577787823649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39249654817276207434196397 14718620556478577787823649)
        ·
          refine ⟨11038965417358933340867737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14718620556478577787823649 11038965417358933340867737)
          ·
            refine ⟨8279224063019200005650803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11038965417358933340867737 8279224063019200005650803)
            ·
              refine ⟨12418836094528800008476205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8279224063019200005650803 12418836094528800008476205)
              ·
                refine ⟨4657063535448300003178577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12418836094528800008476205 4657063535448300003178577)
                ·
                  refine ⟨3492797651586225002383933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4657063535448300003178577 3492797651586225002383933)
                  ·
                    refine ⟨1309799119344834375893975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492797651586225002383933 1309799119344834375893975)
                    ·
                      rfl

theorem cell22_3826237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_3826237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826237 prefixEnd_3826237 := by exact prefixLift 3826237
  have htrace : WordTrace (prefixWord ++ tailWord_3826237) baseStart_3826237 baseEnd_3826237 := by
    simpa [prefixWord, tailWord_3826237, baseEnd_3826237] using wordTrace_append hprefix tailTrace_3826237
  have hstable : (prefixWord ++ tailWord_3826237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826237).length < 2 ^ (prefixWord ++ tailWord_3826237).sum := by decide
  have hdescent : baseEnd_3826237 < baseStart_3826237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826340 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 6]
def baseStart_3826340 : Nat := 118140960795 + 3826340 * 2 ^ 59
def prefixEnd_3826340 : Nat := 4983230072969 + 3 ^ 40 * 3826340 * 2
def baseEnd_3826340 : Nat := 436611459449925480189553

theorem tailTrace_3826340 : CollatzResearch.WordTrace tailWord_3826340 prefixEnd_3826340 436611459449925480189553 := by
  unfold tailWord_3826340
  simp only [CollatzResearch.WordTrace]
  refine ⟨69779042478915570845182237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93038723305220761126909649 69779042478915570845182237)
  ·
    refine ⟨26167140929593339066943339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69779042478915570845182237 26167140929593339066943339)
    ·
      refine ⟨39250711394390008600415009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26167140929593339066943339 39250711394390008600415009)
      ·
        refine ⟨29438033545792506450311257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39250711394390008600415009 29438033545792506450311257)
        ·
          refine ⟨22078525159344379837733443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29438033545792506450311257 22078525159344379837733443)
          ·
            refine ⟨33117787739016569756600165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22078525159344379837733443 33117787739016569756600165)
            ·
              refine ⟨6209585201065606829362531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33117787739016569756600165 6209585201065606829362531)
              ·
                refine ⟨9314377801598410244043797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209585201065606829362531 9314377801598410244043797)
                ·
                  refine ⟨436611459449925480189553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9314377801598410244043797 436611459449925480189553)
                  ·
                    rfl

theorem cell22_3826340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_3826340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826340 prefixEnd_3826340 := by exact prefixLift 3826340
  have htrace : WordTrace (prefixWord ++ tailWord_3826340) baseStart_3826340 baseEnd_3826340 := by
    simpa [prefixWord, tailWord_3826340, baseEnd_3826340] using wordTrace_append hprefix tailTrace_3826340
  have hstable : (prefixWord ++ tailWord_3826340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826340).length < 2 ^ (prefixWord ++ tailWord_3826340).sum := by decide
  have hdescent : baseEnd_3826340 < baseStart_3826340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826346 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_3826346 : Nat := 118140960795 + 3826346 * 2 ^ 59
def prefixEnd_3826346 : Nat := 4983230072969 + 3 ^ 40 * 3826346 * 2
def baseEnd_3826346 : Nat := 436612144090798141639547

theorem tailTrace_3826346 : CollatzResearch.WordTrace tailWord_3826346 prefixEnd_3826346 436612144090798141639547 := by
  unfold tailWord_3826346
  simp only [CollatzResearch.WordTrace]
  refine ⟨34889575948952351178770723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93038869197206269810055261 34889575948952351178770723)
  ·
    refine ⟨52334363923428526768156085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34889575948952351178770723 52334363923428526768156085)
    ·
      refine ⟨4906346617821424384514633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52334363923428526768156085 4906346617821424384514633)
      ·
        refine ⟨3679759963366068288385975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4906346617821424384514633 3679759963366068288385975)
        ·
          refine ⟨5519639945049102432578963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679759963366068288385975 5519639945049102432578963)
          ·
            refine ⟨8279459917573653648868445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5519639945049102432578963 8279459917573653648868445)
            ·
              refine ⟨3104797469090120118325667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8279459917573653648868445 3104797469090120118325667)
              ·
                refine ⟨4657196203635180177488501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104797469090120118325667 4657196203635180177488501)
                ·
                  refine ⟨436612144090798141639547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4657196203635180177488501 436612144090798141639547)
                  ·
                    rfl

theorem cell22_3826346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_3826346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826346 prefixEnd_3826346 := by exact prefixLift 3826346
  have htrace : WordTrace (prefixWord ++ tailWord_3826346) baseStart_3826346 baseEnd_3826346 := by
    simpa [prefixWord, tailWord_3826346, baseEnd_3826346] using wordTrace_append hprefix tailTrace_3826346
  have hstable : (prefixWord ++ tailWord_3826346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826346).length < 2 ^ (prefixWord ++ tailWord_3826346).sum := by decide
  have hdescent : baseEnd_3826346 < baseStart_3826346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826355 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 1, 5]
def baseStart_3826355 : Nat := 118140960795 + 3826355 * 2 ^ 59
def prefixEnd_3826355 : Nat := 4983230072969 + 3 ^ 40 * 3826355 * 2
def baseEnd_3826355 : Nat := 1309839513156321401443613

theorem tailTrace_3826355 : CollatzResearch.WordTrace tailWord_3826355 prefixEnd_3826355 1309839513156321401443613 := by
  unfold tailWord_3826355
  simp only [CollatzResearch.WordTrace]
  refine ⟨139558632052776799252160519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93039088035184532834773679 139558632052776799252160519)
  ·
    refine ⟨209337948079165198878240779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139558632052776799252160519 209337948079165198878240779)
    ·
      refine ⟨314006922118747798317361169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209337948079165198878240779 314006922118747798317361169)
      ·
        refine ⟨235505191589060848738020877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314006922118747798317361169 235505191589060848738020877)
        ·
          refine ⟨88314446845897818276757829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235505191589060848738020877 88314446845897818276757829)
          ·
            refine ⟨16558958783605840926892093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88314446845897818276757829 16558958783605840926892093)
            ·
              refine ⟨6209609543852190347584535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16558958783605840926892093 6209609543852190347584535)
              ·
                refine ⟨9314414315778285521376803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209609543852190347584535 9314414315778285521376803)
                ·
                  refine ⟨13971621473667428282065205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9314414315778285521376803 13971621473667428282065205)
                  ·
                    refine ⟨1309839513156321401443613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13971621473667428282065205 1309839513156321401443613)
                    ·
                      rfl

theorem cell22_3826355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 5].length) (baseStart_3826355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826355 prefixEnd_3826355 := by exact prefixLift 3826355
  have htrace : WordTrace (prefixWord ++ tailWord_3826355) baseStart_3826355 baseEnd_3826355 := by
    simpa [prefixWord, tailWord_3826355, baseEnd_3826355] using wordTrace_append hprefix tailTrace_3826355
  have hstable : (prefixWord ++ tailWord_3826355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826355).length < 2 ^ (prefixWord ++ tailWord_3826355).sum := by decide
  have hdescent : baseEnd_3826355 < baseStart_3826355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826372 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3826372 : Nat := 118140960795 + 3826372 * 2 ^ 59
def prefixEnd_3826372 : Nat := 4983230072969 + 3 ^ 40 * 3826372 * 2
def baseEnd_3826372 : Nat := 1309845332603739023768561

theorem tailTrace_3826372 : CollatzResearch.WordTrace tailWord_3826372 prefixEnd_3826372 1309845332603739023768561 := by
  unfold tailWord_3826372
  simp only [CollatzResearch.WordTrace]
  refine ⟨69779626046857605577764685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93039501395810140770352913 69779626046857605577764685)
  ·
    refine ⟨26167359767571602091661757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69779626046857605577764685 26167359767571602091661757)
    ·
      refine ⟨9812759912839350784373159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26167359767571602091661757 9812759912839350784373159)
      ·
        refine ⟨14719139869259026176559739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9812759912839350784373159 14719139869259026176559739)
        ·
          refine ⟨22078709803888539264839609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14719139869259026176559739 22078709803888539264839609)
          ·
            refine ⟨16559032352916404448629707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22078709803888539264839609 16559032352916404448629707)
            ·
              refine ⟨24838548529374606672944561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16559032352916404448629707 24838548529374606672944561)
              ·
                refine ⟨18628911397030955004708421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24838548529374606672944561 18628911397030955004708421)
                ·
                  refine ⟨3492920886943304063382829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18628911397030955004708421 3492920886943304063382829)
                  ·
                    refine ⟨1309845332603739023768561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492920886943304063382829 1309845332603739023768561)
                    ·
                      rfl

theorem cell22_3826372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3826372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826372 prefixEnd_3826372 := by exact prefixLift 3826372
  have htrace : WordTrace (prefixWord ++ tailWord_3826372) baseStart_3826372 baseEnd_3826372 := by
    simpa [prefixWord, tailWord_3826372, baseEnd_3826372] using wordTrace_append hprefix tailTrace_3826372
  have hstable : (prefixWord ++ tailWord_3826372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826372).length < 2 ^ (prefixWord ++ tailWord_3826372).sum := by decide
  have hdescent : baseEnd_3826372 < baseStart_3826372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826524 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3826524 : Nat := 118140960795 + 3826524 * 2 ^ 59
def prefixEnd_3826524 : Nat := 4983230072969 + 3 ^ 40 * 3826524 * 2
def baseEnd_3826524 : Nat := 1309897365310061293968095

theorem tailTrace_3826524 : CollatzResearch.WordTrace tailWord_3826524 prefixEnd_3826524 1309897365310061293968095 := by
  unfold tailWord_3826524
  simp only [CollatzResearch.WordTrace]
  refine ⟨69782397994582270557531313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93043197326109694076708417 69782397994582270557531313)
  ·
    refine ⟨52336798495936702918148485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69782397994582270557531313 52336798495936702918148485)
    ·
      refine ⟨9813149717988131797152841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52336798495936702918148485 9813149717988131797152841)
      ·
        refine ⟨7359862288491098847864631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9813149717988131797152841 7359862288491098847864631)
        ·
          refine ⟨11039793432736648271796947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359862288491098847864631 11039793432736648271796947)
          ·
            refine ⟨16559690149104972407695421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039793432736648271796947 16559690149104972407695421)
            ·
              refine ⟨6209883805914364652885783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16559690149104972407695421 6209883805914364652885783)
              ·
                refine ⟨9314825708871546979328675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209883805914364652885783 9314825708871546979328675)
                ·
                  refine ⟨13972238563307320468993013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9314825708871546979328675 13972238563307320468993013)
                  ·
                    refine ⟨1309897365310061293968095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13972238563307320468993013 1309897365310061293968095)
                    ·
                      rfl

theorem cell22_3826524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3826524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826524 prefixEnd_3826524 := by exact prefixLift 3826524
  have htrace : WordTrace (prefixWord ++ tailWord_3826524) baseStart_3826524 baseEnd_3826524 := by
    simpa [prefixWord, tailWord_3826524, baseEnd_3826524] using wordTrace_append hprefix tailTrace_3826524
  have hstable : (prefixWord ++ tailWord_3826524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826524).length < 2 ^ (prefixWord ++ tailWord_3826524).sum := by decide
  have hdescent : baseEnd_3826524 < baseStart_3826524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826569 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 3, 3]
def baseStart_3826569 : Nat := 118140960795 + 3826569 * 2 ^ 59
def prefixEnd_3826569 : Nat := 4983230072969 + 3 ^ 40 * 3826569 * 2
def baseEnd_3826569 : Nat := 1309912769729696176592957

theorem tailTrace_3826569 : CollatzResearch.WordTrace tailWord_3826569 prefixEnd_3826569 1309912769729696176592957 := by
  unfold tailWord_3826569
  simp only [CollatzResearch.WordTrace]
  refine ⟨139566437274001513800450761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93044291516001009200300507 139566437274001513800450761)
  ·
    refine ⟨104674827955501135350338071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139566437274001513800450761 104674827955501135350338071)
    ·
      refine ⟨157012241933251703025507107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104674827955501135350338071 157012241933251703025507107)
      ·
        refine ⟨235518362899877554538260661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157012241933251703025507107 235518362899877554538260661)
        ·
          refine ⟨22079846521863520737961937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235518362899877554538260661 22079846521863520737961937)
          ·
            refine ⟨16559884891397640553471453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22079846521863520737961937 16559884891397640553471453)
            ·
              refine ⟨6209956834274115207551795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16559884891397640553471453 6209956834274115207551795)
              ·
                refine ⟨9314935251411172811327693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209956834274115207551795 9314935251411172811327693)
                ·
                  refine ⟨3493100719279189804247885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9314935251411172811327693 3493100719279189804247885)
                  ·
                    refine ⟨1309912769729696176592957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493100719279189804247885 1309912769729696176592957)
                    ·
                      rfl

theorem cell22_3826569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_3826569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826569 prefixEnd_3826569 := by exact prefixLift 3826569
  have htrace : WordTrace (prefixWord ++ tailWord_3826569) baseStart_3826569 baseEnd_3826569 := by
    simpa [prefixWord, tailWord_3826569, baseEnd_3826569] using wordTrace_append hprefix tailTrace_3826569
  have hstable : (prefixWord ++ tailWord_3826569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826569).length < 2 ^ (prefixWord ++ tailWord_3826569).sum := by decide
  have hdescent : baseEnd_3826569 < baseStart_3826569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826644 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 6]
def baseStart_3826644 : Nat := 118140960795 + 3826644 * 2 ^ 59
def prefixEnd_3826644 : Nat := 4983230072969 + 3 ^ 40 * 3826644 * 2
def baseEnd_3826644 : Nat := 436646147920806993655909

theorem tailTrace_3826644 : CollatzResearch.WordTrace tailWord_3826644 prefixEnd_3826644 436646147920806993655909 := by
  unfold tailWord_3826644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69784586374364900804715493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93046115165819867739620657 69784586374364900804715493)
  ·
    refine ⟨13084609945193418900884155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69784586374364900804715493 13084609945193418900884155)
    ·
      refine ⟨19626914917790128351326233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13084609945193418900884155 19626914917790128351326233)
      ·
        refine ⟨14720186188342596263494675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19626914917790128351326233 14720186188342596263494675)
        ·
          refine ⟨22080279282513894395242013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14720186188342596263494675 22080279282513894395242013)
          ·
            refine ⟨8280104730942710398215755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22080279282513894395242013 8280104730942710398215755)
            ·
              refine ⟨12420157096414065597323633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280104730942710398215755 12420157096414065597323633)
              ·
                refine ⟨9315117822310549197992725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12420157096414065597323633 9315117822310549197992725)
                ·
                  refine ⟨436646147920806993655909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9315117822310549197992725 436646147920806993655909)
                  ·
                    rfl

theorem cell22_3826644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_3826644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826644 prefixEnd_3826644 := by exact prefixLift 3826644
  have htrace : WordTrace (prefixWord ++ tailWord_3826644) baseStart_3826644 baseEnd_3826644 := by
    simpa [prefixWord, tailWord_3826644, baseEnd_3826644] using wordTrace_append hprefix tailTrace_3826644
  have hstable : (prefixWord ++ tailWord_3826644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826644).length < 2 ^ (prefixWord ++ tailWord_3826644).sum := by decide
  have hdescent : baseEnd_3826644 < baseStart_3826644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826646 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3826646 : Nat := 118140960795 + 3826646 * 2 ^ 59
def prefixEnd_3826646 : Nat := 4983230072969 + 3 ^ 40 * 3826646 * 2
def baseEnd_3826646 : Nat := 1309939128403293642417721

theorem tailTrace_3826646 : CollatzResearch.WordTrace tailWord_3826646 prefixEnd_3826646 1309939128403293642417721 := by
  unfold tailWord_3826646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723077855920159746937737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93046163796481703967335861 8723077855920159746937737)
  ·
    refine ⟨6542308391940119810203303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8723077855920159746937737 6542308391940119810203303)
    ·
      refine ⟨9813462587910179715304955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542308391940119810203303 9813462587910179715304955)
      ·
        refine ⟨14720193881865269572957433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9813462587910179715304955 14720193881865269572957433)
        ·
          refine ⟨11040145411398952179718075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14720193881865269572957433 11040145411398952179718075)
          ·
            refine ⟨16560218117098428269577113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040145411398952179718075 16560218117098428269577113)
            ·
              refine ⟨12420163587823821202182835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16560218117098428269577113 12420163587823821202182835)
              ·
                refine ⟨18630245381735731803274253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12420163587823821202182835 18630245381735731803274253)
                ·
                  refine ⟨6986342018150899426227845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18630245381735731803274253 6986342018150899426227845)
                  ·
                    refine ⟨1309939128403293642417721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6986342018150899426227845 1309939128403293642417721)
                    ·
                      rfl

theorem cell22_3826646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3826646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826646 prefixEnd_3826646 := by exact prefixLift 3826646
  have htrace : WordTrace (prefixWord ++ tailWord_3826646) baseStart_3826646 baseEnd_3826646 := by
    simpa [prefixWord, tailWord_3826646, baseEnd_3826646] using wordTrace_append hprefix tailTrace_3826646
  have hstable : (prefixWord ++ tailWord_3826646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826646).length < 2 ^ (prefixWord ++ tailWord_3826646).sum := by decide
  have hdescent : baseEnd_3826646 < baseStart_3826646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826659 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 4, 3]
def baseStart_3826659 : Nat := 118140960795 + 3826659 * 2 ^ 59
def prefixEnd_3826659 : Nat := 4983230072969 + 3 ^ 40 * 3826659 * 2
def baseEnd_3826659 : Nat := 1309943578568965941842681

theorem tailTrace_3826659 : CollatzResearch.WordTrace tailWord_3826659 prefixEnd_3826659 1309943578568965941842681 := by
  unfold tailWord_3826659
  simp only [CollatzResearch.WordTrace]
  refine ⟨139569719843675459171227031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93046479895783639447484687 139569719843675459171227031)
  ·
    refine ⟨209354579765513188756840547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139569719843675459171227031 209354579765513188756840547)
    ·
      refine ⟨314031869648269783135260821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209354579765513188756840547 314031869648269783135260821)
      ·
        refine ⟨14720243889762646084465351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 314031869648269783135260821 14720243889762646084465351)
        ·
          refine ⟨22080365834643969126698027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14720243889762646084465351 22080365834643969126698027)
          ·
            refine ⟨33120548751965953690047041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22080365834643969126698027 33120548751965953690047041)
            ·
              refine ⟨24840411563974465267535281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33120548751965953690047041 24840411563974465267535281)
              ·
                refine ⟨18630308672980848950651461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24840411563974465267535281 18630308672980848950651461)
                ·
                  refine ⟨3493182876183909178247149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18630308672980848950651461 3493182876183909178247149)
                  ·
                    refine ⟨1309943578568965941842681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493182876183909178247149 1309943578568965941842681)
                    ·
                      rfl

theorem cell22_3826659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 3].length) (baseStart_3826659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826659 prefixEnd_3826659 := by exact prefixLift 3826659
  have htrace : WordTrace (prefixWord ++ tailWord_3826659) baseStart_3826659 baseEnd_3826659 := by
    simpa [prefixWord, tailWord_3826659, baseEnd_3826659] using wordTrace_append hprefix tailTrace_3826659
  have hstable : (prefixWord ++ tailWord_3826659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826659).length < 2 ^ (prefixWord ++ tailWord_3826659).sum := by decide
  have hdescent : baseEnd_3826659 < baseStart_3826659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826663 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3826663 : Nat := 118140960795 + 3826663 * 2 ^ 59
def prefixEnd_3826663 : Nat := 4983230072969 + 3 ^ 40 * 3826663 * 2
def baseEnd_3826663 : Nat := 1309944947850711264742669

theorem tailTrace_3826663 : CollatzResearch.WordTrace tailWord_3826663 prefixEnd_3826663 1309944947850711264742669 := by
  unfold tailWord_3826663
  simp only [CollatzResearch.WordTrace]
  refine ⟨139569865735660967854372643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93046577157107311902915095 139569865735660967854372643)
  ·
    refine ⟨209354798603491451781558965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139569865735660967854372643 209354798603491451781558965)
    ·
      refine ⟨19627012369077323604521153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209354798603491451781558965 19627012369077323604521153)
      ·
        refine ⟨14720259276807992703390865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19627012369077323604521153 14720259276807992703390865)
        ·
          refine ⟨11040194457605994527543149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14720259276807992703390865 11040194457605994527543149)
          ·
            refine ⟨4140072921602247947828681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11040194457605994527543149 4140072921602247947828681)
            ·
              refine ⟨3105054691201685960871511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4140072921602247947828681 3105054691201685960871511)
              ·
                refine ⟨4657582036802528941307267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105054691201685960871511 4657582036802528941307267)
                ·
                  refine ⟨6986373055203793411960901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657582036802528941307267 6986373055203793411960901)
                  ·
                    refine ⟨1309944947850711264742669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6986373055203793411960901 1309944947850711264742669)
                    ·
                      rfl

theorem cell22_3826663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3826663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826663 prefixEnd_3826663 := by exact prefixLift 3826663
  have htrace : WordTrace (prefixWord ++ tailWord_3826663) baseStart_3826663 baseEnd_3826663 := by
    simpa [prefixWord, tailWord_3826663, baseEnd_3826663] using wordTrace_append hprefix tailTrace_3826663
  have hstable : (prefixWord ++ tailWord_3826663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826663).length < 2 ^ (prefixWord ++ tailWord_3826663).sum := by decide
  have hdescent : baseEnd_3826663 < baseStart_3826663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826734 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_3826734 : Nat := 118140960795 + 3826734 * 2 ^ 59
def prefixEnd_3826734 : Nat := 4983230072969 + 3 ^ 40 * 3826734 * 2
def baseEnd_3826734 : Nat := 436656417533896915405817

theorem tailTrace_3826734 : CollatzResearch.WordTrace tailWord_3826734 prefixEnd_3826734 436656417533896915405817 := by
  unfold tailWord_3826734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17446556914800468372525907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93048303545602497986804837 17446556914800468372525907)
  ·
    refine ⟨26169835372200702558788861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17446556914800468372525907 26169835372200702558788861)
    ·
      refine ⟨9813688264575263459545823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26169835372200702558788861 9813688264575263459545823)
      ·
        refine ⟨14720532396862895189318735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9813688264575263459545823 14720532396862895189318735)
        ·
          refine ⟨22080798595294342783978103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14720532396862895189318735 22080798595294342783978103)
          ·
            refine ⟨33121197892941514175967155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22080798595294342783978103 33121197892941514175967155)
            ·
              refine ⟨49681796839412271263950733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33121197892941514175967155 49681796839412271263950733)
              ·
                refine ⟨18630673814779601723981525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49681796839412271263950733 18630673814779601723981525)
                ·
                  refine ⟨436656417533896915405817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18630673814779601723981525 436656417533896915405817)
                  ·
                    rfl

theorem cell22_3826734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_3826734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826734 prefixEnd_3826734 := by exact prefixLift 3826734
  have htrace : WordTrace (prefixWord ++ tailWord_3826734) baseStart_3826734 baseEnd_3826734 := by
    simpa [prefixWord, tailWord_3826734, baseEnd_3826734] using wordTrace_append hprefix tailTrace_3826734
  have hstable : (prefixWord ++ tailWord_3826734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826734).length < 2 ^ (prefixWord ++ tailWord_3826734).sum := by decide
  have hdescent : baseEnd_3826734 < baseStart_3826734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826796 : List Nat := [2, 2, 1, 1, 3, 2, 3, 4, 4]
def baseStart_3826796 : Nat := 118140960795 + 3826796 * 2 ^ 59
def prefixEnd_3826796 : Nat := 4983230072969 + 3 ^ 40 * 3826796 * 2
def baseEnd_3826796 : Nat := 436663492156247750389087

theorem tailTrace_3826796 : CollatzResearch.WordTrace tailWord_3826796 prefixEnd_3826796 436663492156247750389087 := by
  unfold tailWord_3826796
  simp only [CollatzResearch.WordTrace]
  refine ⟨69787358322089565784482121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93049811096119421045976161 69787358322089565784482121)
  ·
    refine ⟨52340518741567174338361591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69787358322089565784482121 52340518741567174338361591)
    ·
      refine ⟨78510778112350761507542387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52340518741567174338361591 78510778112350761507542387)
      ·
        refine ⟨117766167168526142261313581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78510778112350761507542387 117766167168526142261313581)
        ·
          refine ⟨44162312688197303347992593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117766167168526142261313581 44162312688197303347992593)
          ·
            refine ⟨33121734516147977510994445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44162312688197303347992593 33121734516147977510994445)
            ·
              refine ⟨12420650443555491566622917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33121734516147977510994445 12420650443555491566622917)
              ·
                refine ⟨2328871958166654668741797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12420650443555491566622917 2328871958166654668741797)
                ·
                  refine ⟨436663492156247750389087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2328871958166654668741797 436663492156247750389087)
                  ·
                    rfl

theorem cell22_3826796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_3826796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826796 prefixEnd_3826796 := by exact prefixLift 3826796
  have htrace : WordTrace (prefixWord ++ tailWord_3826796) baseStart_3826796 baseEnd_3826796 := by
    simpa [prefixWord, tailWord_3826796, baseEnd_3826796] using wordTrace_append hprefix tailTrace_3826796
  have hstable : (prefixWord ++ tailWord_3826796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826796).length < 2 ^ (prefixWord ++ tailWord_3826796).sum := by decide
  have hdescent : baseEnd_3826796 < baseStart_3826796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826890 : List Nat := [3, 1, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_3826890 : Nat := 118140960795 + 3826890 * 2 ^ 59
def prefixEnd_3826890 : Nat := 4983230072969 + 3 ^ 40 * 3826890 * 2
def baseEnd_3826890 : Nat := 1310022654589758339316973

theorem tailTrace_3826890 : CollatzResearch.WordTrace tailWord_3826890 prefixEnd_3826890 1310022654589758339316973 := by
  unfold tailWord_3826890
  simp only [CollatzResearch.WordTrace]
  refine ⟨34894536276459646405721531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93052096737225723748590749 34894536276459646405721531)
  ·
    refine ⟨52341804414689469608582297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34894536276459646405721531 52341804414689469608582297)
    ·
      refine ⟨39256353311017102206436723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52341804414689469608582297 39256353311017102206436723)
      ·
        refine ⟨58884529966525653309655085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39256353311017102206436723 58884529966525653309655085)
        ·
          refine ⟨22081698737447119991120657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58884529966525653309655085 22081698737447119991120657)
          ·
            refine ⟨16561274053085339993340493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22081698737447119991120657 16561274053085339993340493)
            ·
              refine ⟨6210477769907002497502685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16561274053085339993340493 6210477769907002497502685)
              ·
                refine ⟨2328929163715125936563507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6210477769907002497502685 2328929163715125936563507)
                ·
                  refine ⟨3493393745572688904845261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328929163715125936563507 3493393745572688904845261)
                  ·
                    refine ⟨1310022654589758339316973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493393745572688904845261 1310022654589758339316973)
                    ·
                      rfl

theorem cell22_3826890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_3826890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826890 prefixEnd_3826890 := by exact prefixLift 3826890
  have htrace : WordTrace (prefixWord ++ tailWord_3826890) baseStart_3826890 baseEnd_3826890 := by
    simpa [prefixWord, tailWord_3826890, baseEnd_3826890] using wordTrace_append hprefix tailTrace_3826890
  have hstable : (prefixWord ++ tailWord_3826890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826890).length < 2 ^ (prefixWord ++ tailWord_3826890).sum := by decide
  have hdescent : baseEnd_3826890 < baseStart_3826890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826961 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_3826961 : Nat := 118140960795 + 3826961 * 2 ^ 59
def prefixEnd_3826961 : Nat := 4983230072969 + 3 ^ 40 * 3826961 * 2
def baseEnd_3826961 : Nat := 1310046959340737820791755

theorem tailTrace_3826961 : CollatzResearch.WordTrace tailWord_3826961 prefixEnd_3826961 1310046959340737820791755 := by
  unfold tailWord_3826961
  simp only [CollatzResearch.WordTrace]
  refine ⟨139580734688581364748720737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93053823125720909832480491 139580734688581364748720737)
  ·
    refine ⟨104685551016436023561540553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139580734688581364748720737 104685551016436023561540553)
    ·
      refine ⟨78514163262327017671155415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104685551016436023561540553 78514163262327017671155415)
      ·
        refine ⟨117771244893490526506733123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78514163262327017671155415 117771244893490526506733123)
        ·
          refine ⟨176656867340235789760099685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117771244893490526506733123 176656867340235789760099685)
          ·
            refine ⟨33123162626294210580018691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176656867340235789760099685 33123162626294210580018691)
            ·
              refine ⟨49684743939441315870028037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33123162626294210580018691 49684743939441315870028037)
              ·
                refine ⟨9315889488645246725630257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49684743939441315870028037 9315889488645246725630257)
                ·
                  refine ⟨6986917116483935044222693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9315889488645246725630257 6986917116483935044222693)
                  ·
                    refine ⟨1310046959340737820791755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6986917116483935044222693 1310046959340737820791755)
                    ·
                      rfl

theorem cell22_3826961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_3826961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826961 prefixEnd_3826961 := by exact prefixLift 3826961
  have htrace : WordTrace (prefixWord ++ tailWord_3826961) baseStart_3826961 baseEnd_3826961 := by
    simpa [prefixWord, tailWord_3826961, baseEnd_3826961] using wordTrace_append hprefix tailTrace_3826961
  have hstable : (prefixWord ++ tailWord_3826961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826961).length < 2 ^ (prefixWord ++ tailWord_3826961).sum := by decide
  have hdescent : baseEnd_3826961 < baseStart_3826961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826993 : List Nat := [1, 2, 2, 3, 3, 2, 3, 6]
def baseStart_3826993 : Nat := 118140960795 + 3826993 * 2 ^ 59
def prefixEnd_3826993 : Nat := 4983230072969 + 3 ^ 40 * 3826993 * 2
def baseEnd_3826993 : Nat := 145561990399411155999073

theorem tailTrace_3826993 : CollatzResearch.WordTrace tailWord_3826993 prefixEnd_3826993 145561990399411155999073 := by
  unfold tailWord_3826993
  simp only [CollatzResearch.WordTrace]
  refine ⟨139581901824465434213885633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93054601216310289475923755 139581901824465434213885633)
  ·
    refine ⟨104686426368349075660414225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139581901824465434213885633 104686426368349075660414225)
    ·
      refine ⟨78514819776261806745310669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104686426368349075660414225 78514819776261806745310669)
      ·
        refine ⟨29443057416098177529491501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78514819776261806745310669 29443057416098177529491501)
        ·
          refine ⟨11041146531036816573559313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29443057416098177529491501 11041146531036816573559313)
          ·
            refine ⟨8280859898277612430169485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11041146531036816573559313 8280859898277612430169485)
            ·
              refine ⟨3105322461854104661313557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8280859898277612430169485 3105322461854104661313557)
              ·
                refine ⟨145561990399411155999073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3105322461854104661313557 145561990399411155999073)
                ·
                  rfl

theorem cell22_3826993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 6].length) (baseStart_3826993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826993 prefixEnd_3826993 := by exact prefixLift 3826993
  have htrace : WordTrace (prefixWord ++ tailWord_3826993) baseStart_3826993 baseEnd_3826993 := by
    simpa [prefixWord, tailWord_3826993, baseEnd_3826993] using wordTrace_append hprefix tailTrace_3826993
  have hstable : (prefixWord ++ tailWord_3826993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826993).length < 2 ^ (prefixWord ++ tailWord_3826993).sum := by decide
  have hdescent : baseEnd_3826993 < baseStart_3826993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827014 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3827014 : Nat := 118140960795 + 3827014 * 2 ^ 59
def prefixEnd_3827014 : Nat := 4983230072969 + 3 ^ 40 * 3827014 * 2
def baseEnd_3827014 : Nat := 1310065102323863349216593

theorem tailTrace_3827014 : CollatzResearch.WordTrace tailWord_3827014 prefixEnd_3827014 1310065102323863349216593 := by
  unfold tailWord_3827014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361958367418417337512503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93055111838259569866933397 4361958367418417337512503)
  ·
    refine ⟨6542937551127626006268755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4361958367418417337512503 6542937551127626006268755)
    ·
      refine ⟨9814406326691439009403133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542937551127626006268755 9814406326691439009403133)
      ·
        refine ⟨3680402372509289628526175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9814406326691439009403133 3680402372509289628526175)
        ·
          refine ⟨5520603558763934442789263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680402372509289628526175 5520603558763934442789263)
          ·
            refine ⟨8280905338145901664183895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5520603558763934442789263 8280905338145901664183895)
            ·
              refine ⟨12421358007218852496275843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280905338145901664183895 12421358007218852496275843)
              ·
                refine ⟨18632037010828278744413765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12421358007218852496275843 18632037010828278744413765)
                ·
                  refine ⟨3493506939530302264577581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18632037010828278744413765 3493506939530302264577581)
                  ·
                    refine ⟨1310065102323863349216593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493506939530302264577581 1310065102323863349216593)
                    ·
                      rfl

theorem cell22_3827014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3827014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827014 prefixEnd_3827014 := by exact prefixLift 3827014
  have htrace : WordTrace (prefixWord ++ tailWord_3827014) baseStart_3827014 baseEnd_3827014 := by
    simpa [prefixWord, tailWord_3827014, baseEnd_3827014] using wordTrace_append hprefix tailTrace_3827014
  have hstable : (prefixWord ++ tailWord_3827014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827014).length < 2 ^ (prefixWord ++ tailWord_3827014).sum := by decide
  have hdescent : baseEnd_3827014 < baseStart_3827014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827025 : List Nat := [1, 2, 2, 1, 4, 1, 1, 6, 1, 3]
def baseStart_3827025 : Nat := 118140960795 + 3827025 * 2 ^ 59
def prefixEnd_3827025 : Nat := 4983230072969 + 3 ^ 40 * 3827025 * 2
def baseEnd_3827025 : Nat := 1310068867848662987191559

theorem tailTrace_3827025 : CollatzResearch.WordTrace tailWord_3827025 prefixEnd_3827025 1310068867848662987191559 := by
  unfold tailWord_3827025
  simp only [CollatzResearch.WordTrace]
  refine ⟨139583068960349503679050529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93055379306899669119367019 139583068960349503679050529)
  ·
    refine ⟨104687301720262127759287897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139583068960349503679050529 104687301720262127759287897)
    ·
      refine ⟨78515476290196595819465923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104687301720262127759287897 78515476290196595819465923)
      ·
        refine ⟨117773214435294893729198885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78515476290196595819465923 117773214435294893729198885)
        ·
          refine ⟨22082477706617792574224791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117773214435294893729198885 22082477706617792574224791)
          ·
            refine ⟨33123716559926688861337187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22082477706617792574224791 33123716559926688861337187)
            ·
              refine ⟨49685574839890033292005781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33123716559926688861337187 49685574839890033292005781)
              ·
                refine ⟨2329011320619845310562771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49685574839890033292005781 2329011320619845310562771)
                ·
                  refine ⟨3493516980929767965844157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329011320619845310562771 3493516980929767965844157)
                  ·
                    refine ⟨1310068867848662987191559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493516980929767965844157 1310068867848662987191559)
                    ·
                      rfl

theorem cell22_3827025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_3827025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827025 prefixEnd_3827025 := by exact prefixLift 3827025
  have htrace : WordTrace (prefixWord ++ tailWord_3827025) baseStart_3827025 baseEnd_3827025 := by
    simpa [prefixWord, tailWord_3827025, baseEnd_3827025] using wordTrace_append hprefix tailTrace_3827025
  have hstable : (prefixWord ++ tailWord_3827025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827025).length < 2 ^ (prefixWord ++ tailWord_3827025).sum := by decide
  have hdescent : baseEnd_3827025 < baseStart_3827025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827068 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_3827068 : Nat := 118140960795 + 3827068 * 2 ^ 59
def prefixEnd_3827068 : Nat := 4983230072969 + 3 ^ 40 * 3827068 * 2
def baseEnd_3827068 : Nat := 1310083587627425208366427

theorem tailTrace_3827068 : CollatzResearch.WordTrace tailWord_3827068 prefixEnd_3827068 1310083587627425208366427 := by
  unfold tailWord_3827068
  simp only [CollatzResearch.WordTrace]
  refine ⟨69792318649596861011432929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93056424866129148015243905 69792318649596861011432929)
  ·
    refine ⟨52344238987197645758574697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69792318649596861011432929 52344238987197645758574697)
    ·
      refine ⟨39258179240398234318931023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52344238987197645758574697 39258179240398234318931023)
      ·
        refine ⟨58887268860597351478396535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39258179240398234318931023 58887268860597351478396535)
        ·
          refine ⟨88330903290896027217594803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58887268860597351478396535 88330903290896027217594803)
          ·
            refine ⟨132496354936344040826392205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88330903290896027217594803 132496354936344040826392205)
            ·
              refine ⟨49686133101129015309897077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132496354936344040826392205 49686133101129015309897077)
              ·
                refine ⟨4658074978230845185302851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49686133101129015309897077 4658074978230845185302851)
                ·
                  refine ⟨6987112467346267777954277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658074978230845185302851 6987112467346267777954277)
                  ·
                    refine ⟨1310083587627425208366427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987112467346267777954277 1310083587627425208366427)
                    ·
                      rfl

theorem cell22_3827068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_3827068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827068 prefixEnd_3827068 := by exact prefixLift 3827068
  have htrace : WordTrace (prefixWord ++ tailWord_3827068) baseStart_3827068 baseEnd_3827068 := by
    simpa [prefixWord, tailWord_3827068, baseEnd_3827068] using wordTrace_append hprefix tailTrace_3827068
  have hstable : (prefixWord ++ tailWord_3827068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827068).length < 2 ^ (prefixWord ++ tailWord_3827068).sum := by decide
  have hdescent : baseEnd_3827068 < baseStart_3827068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827098 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_3827098 : Nat := 118140960795 + 3827098 * 2 ^ 59
def prefixEnd_3827098 : Nat := 4983230072969 + 3 ^ 40 * 3827098 * 2
def baseEnd_3827098 : Nat := 1310093857240515130116335

theorem tailTrace_3827098 : CollatzResearch.WordTrace tailWord_3827098 prefixEnd_3827098 1310093857240515130116335 := by
  unfold tailWord_3827098
  simp only [CollatzResearch.WordTrace]
  refine ⟨34896432872271259286614487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93057154326056691430971965 34896432872271259286614487)
  ·
    refine ⟨52344649308406888929921731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34896432872271259286614487 52344649308406888929921731)
    ·
      refine ⟨78516973962610333394882597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52344649308406888929921731 78516973962610333394882597)
      ·
        refine ⟨14721932617989437511540487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78516973962610333394882597 14721932617989437511540487)
        ·
          refine ⟨22082898926984156267310731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14721932617989437511540487 22082898926984156267310731)
          ·
            refine ⟨33124348390476234400966097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22082898926984156267310731 33124348390476234400966097)
            ·
              refine ⟨24843261292857175800724573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33124348390476234400966097 24843261292857175800724573)
              ·
                refine ⟨9316222984821440925271715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24843261292857175800724573 9316222984821440925271715)
                ·
                  refine ⟨13974334477232161387907573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9316222984821440925271715 13974334477232161387907573)
                  ·
                    refine ⟨1310093857240515130116335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13974334477232161387907573 1310093857240515130116335)
                    ·
                      rfl

theorem cell22_3827098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_3827098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827098 prefixEnd_3827098 := by exact prefixLift 3827098
  have htrace : WordTrace (prefixWord ++ tailWord_3827098) baseStart_3827098 baseEnd_3827098 := by
    simpa [prefixWord, tailWord_3827098, baseEnd_3827098] using wordTrace_append hprefix tailTrace_3827098
  have hstable : (prefixWord ++ tailWord_3827098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827098).length < 2 ^ (prefixWord ++ tailWord_3827098).sum := by decide
  have hdescent : baseEnd_3827098 < baseStart_3827098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827102 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3827102 : Nat := 118140960795 + 3827102 * 2 ^ 59
def prefixEnd_3827102 : Nat := 4983230072969 + 3 ^ 40 * 3827102 * 2
def baseEnd_3827102 : Nat := 1310095226522260453016323

theorem tailTrace_3827102 : CollatzResearch.WordTrace tailWord_3827102 prefixEnd_3827102 1310095226522260453016323 := by
  unfold tailWord_3827102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17448234672633818228700445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93057251587380363886402373 17448234672633818228700445)
  ·
    refine ⟨6543088002237681835762667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17448234672633818228700445 6543088002237681835762667)
    ·
      refine ⟨9814632003356522753644001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6543088002237681835762667 9814632003356522753644001)
      ·
        refine ⟨7360974002517392065233001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9814632003356522753644001 7360974002517392065233001)
        ·
          refine ⟨5520730501888044048924751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7360974002517392065233001 5520730501888044048924751)
          ·
            refine ⟨8281095752832066073387127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5520730501888044048924751 8281095752832066073387127)
            ·
              refine ⟨12421643629248099110080691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281095752832066073387127 12421643629248099110080691)
              ·
                refine ⟨18632465443872148665121037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12421643629248099110080691 18632465443872148665121037)
                ·
                  refine ⟨6987174541452055749420389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18632465443872148665121037 6987174541452055749420389)
                  ·
                    refine ⟨1310095226522260453016323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987174541452055749420389 1310095226522260453016323)
                    ·
                      rfl

theorem cell22_3827102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3827102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827102 prefixEnd_3827102 := by exact prefixLift 3827102
  have htrace : WordTrace (prefixWord ++ tailWord_3827102) baseStart_3827102 baseEnd_3827102 := by
    simpa [prefixWord, tailWord_3827102, baseEnd_3827102] using wordTrace_append hprefix tailTrace_3827102
  have hstable : (prefixWord ++ tailWord_3827102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827102).length < 2 ^ (prefixWord ++ tailWord_3827102).sum := by decide
  have hdescent : baseEnd_3827102 < baseStart_3827102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827190 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3827190 : Nat := 118140960795 + 3827190 * 2 ^ 59
def prefixEnd_3827190 : Nat := 4983230072969 + 3 ^ 40 * 3827190 * 2
def baseEnd_3827190 : Nat := 436708450240219185605351

theorem tailTrace_3827190 : CollatzResearch.WordTrace tailWord_3827190 prefixEnd_3827190 436708450240219185605351 := by
  unfold tailWord_3827190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724317937796983553675439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93059391336501157905871349 8724317937796983553675439)
  ·
    refine ⟨13086476906695475330513159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8724317937796983553675439 13086476906695475330513159)
    ·
      refine ⟨19629715360043212995769739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13086476906695475330513159 19629715360043212995769739)
      ·
        refine ⟨29444573040064819493654609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19629715360043212995769739 29444573040064819493654609)
        ·
          refine ⟨22083429780048614620240957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29444573040064819493654609 22083429780048614620240957)
          ·
            refine ⟨8281286167518230482590359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22083429780048614620240957 8281286167518230482590359)
            ·
              refine ⟨12421929251277345723885539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281286167518230482590359 12421929251277345723885539)
              ·
                refine ⟨18632893876916018585828309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12421929251277345723885539 18632893876916018585828309)
                ·
                  refine ⟨436708450240219185605351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18632893876916018585828309 436708450240219185605351)
                  ·
                    rfl

theorem cell22_3827190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3827190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827190 prefixEnd_3827190 := by exact prefixLift 3827190
  have htrace : WordTrace (prefixWord ++ tailWord_3827190) baseStart_3827190 baseEnd_3827190 := by
    simpa [prefixWord, tailWord_3827190, baseEnd_3827190] using wordTrace_append hprefix tailTrace_3827190
  have hstable : (prefixWord ++ tailWord_3827190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827190).length < 2 ^ (prefixWord ++ tailWord_3827190).sum := by decide
  have hdescent : baseEnd_3827190 < baseStart_3827190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827203 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 3, 4]
def baseStart_3827203 : Nat := 118140960795 + 3827203 * 2 ^ 59
def prefixEnd_3827203 : Nat := 4983230072969 + 3 ^ 40 * 3827203 * 2
def baseEnd_3827203 : Nat := 1310129800886329856241013

theorem tailTrace_3827203 : CollatzResearch.WordTrace tailWord_3827203 prefixEnd_3827203 1310129800886329856241013 := by
  unfold tailWord_3827203
  simp only [CollatzResearch.WordTrace]
  refine ⟨139589561153704640079030263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93059707435803093386020175 139589561153704640079030263)
  ·
    refine ⟨209384341730556960118545395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139589561153704640079030263 209384341730556960118545395)
    ·
      refine ⟨314076512595835440177818093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209384341730556960118545395 314076512595835440177818093)
      ·
        refine ⟨117778692223438290066681785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314076512595835440177818093 117778692223438290066681785)
        ·
          refine ⟨88334019167578717550011339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117778692223438290066681785 88334019167578717550011339)
          ·
            refine ⟨132501028751368076325017009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88334019167578717550011339 132501028751368076325017009)
            ·
              refine ⟨99375771563526057243762757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132501028751368076325017009 99375771563526057243762757)
              ·
                refine ⟨18632957168161135733205517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99375771563526057243762757 18632957168161135733205517)
                ·
                  refine ⟨6987358938060425899952069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18632957168161135733205517 6987358938060425899952069)
                  ·
                    refine ⟨1310129800886329856241013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987358938060425899952069 1310129800886329856241013)
                    ·
                      rfl

theorem cell22_3827203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 4].length) (baseStart_3827203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827203 prefixEnd_3827203 := by exact prefixLift 3827203
  have htrace : WordTrace (prefixWord ++ tailWord_3827203) baseStart_3827203 baseEnd_3827203 := by
    simpa [prefixWord, tailWord_3827203, baseEnd_3827203] using wordTrace_append hprefix tailTrace_3827203
  have hstable : (prefixWord ++ tailWord_3827203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827203).length < 2 ^ (prefixWord ++ tailWord_3827203).sum := by decide
  have hdescent : baseEnd_3827203 < baseStart_3827203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827207 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 5]
def baseStart_3827207 : Nat := 118140960795 + 3827207 * 2 ^ 59
def prefixEnd_3827207 : Nat := 4983230072969 + 3 ^ 40 * 3827207 * 2
def baseEnd_3827207 : Nat := 436710390056025059713667

theorem tailTrace_3827207 : CollatzResearch.WordTrace tailWord_3827207 prefixEnd_3827207 436710390056025059713667 := by
  unfold tailWord_3827207
  simp only [CollatzResearch.WordTrace]
  refine ⟨139589707045690148762175875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93059804697126765841450583 139589707045690148762175875)
  ·
    refine ⟨209384560568535223143263813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139589707045690148762175875 209384560568535223143263813)
    ·
      refine ⟨39259605106600354339361965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209384560568535223143263813 39259605106600354339361965)
      ·
        refine ⟨14722351914975132877260737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39259605106600354339361965 14722351914975132877260737)
        ·
          refine ⟨11041763936231349657945553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14722351914975132877260737 11041763936231349657945553)
          ·
            refine ⟨8281322952173512243459165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11041763936231349657945553 8281322952173512243459165)
            ·
              refine ⟨3105496107065067091297187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8281322952173512243459165 3105496107065067091297187)
              ·
                refine ⟨4658244160597600636945781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105496107065067091297187 4658244160597600636945781)
                ·
                  refine ⟨436710390056025059713667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4658244160597600636945781 436710390056025059713667)
                  ·
                    rfl

theorem cell22_3827207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 5].length) (baseStart_3827207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827207 prefixEnd_3827207 := by exact prefixLift 3827207
  have htrace : WordTrace (prefixWord ++ tailWord_3827207) baseStart_3827207 baseEnd_3827207 := by
    simpa [prefixWord, tailWord_3827207, baseEnd_3827207] using wordTrace_append hprefix tailTrace_3827207
  have hstable : (prefixWord ++ tailWord_3827207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827207).length < 2 ^ (prefixWord ++ tailWord_3827207).sum := by decide
  have hdescent : baseEnd_3827207 < baseStart_3827207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827263 : List Nat := [1, 1, 2, 2, 3, 3, 1, 9]
def baseStart_3827263 : Nat := 118140960795 + 3827263 * 2 ^ 59
def prefixEnd_3827263 : Nat := 4983230072969 + 3 ^ 40 * 3827263 * 2
def baseEnd_3827263 : Nat := 145572260012501077748981

theorem tailTrace_3827263 : CollatzResearch.WordTrace tailWord_3827263 prefixEnd_3827263 145572260012501077748981 := by
  unfold tailWord_3827263
  simp only [CollatzResearch.WordTrace]
  refine ⟨139591749533487270326214443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93061166355658180217476295 139591749533487270326214443)
  ·
    refine ⟨209387624300230905489321665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139591749533487270326214443 209387624300230905489321665)
    ·
      refine ⟨157040718225173179116991249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209387624300230905489321665 157040718225173179116991249)
      ·
        refine ⟨117780538668879884337743437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157040718225173179116991249 117780538668879884337743437)
        ·
          refine ⟨44167702000829956626653789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117780538668879884337743437 44167702000829956626653789)
          ·
            refine ⟨16562888250311233734995171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44167702000829956626653789 16562888250311233734995171)
            ·
              refine ⟨24844332375466850602492757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16562888250311233734995171 24844332375466850602492757)
              ·
                refine ⟨145572260012501077748981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24844332375466850602492757 145572260012501077748981)
                ·
                  rfl

theorem cell22_3827263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 9].length) (baseStart_3827263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827263 prefixEnd_3827263 := by exact prefixLift 3827263
  have htrace : WordTrace (prefixWord ++ tailWord_3827263) baseStart_3827263 baseEnd_3827263 := by
    simpa [prefixWord, tailWord_3827263, baseEnd_3827263] using wordTrace_append hprefix tailTrace_3827263
  have hstable : (prefixWord ++ tailWord_3827263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827263).length < 2 ^ (prefixWord ++ tailWord_3827263).sum := by decide
  have hdescent : baseEnd_3827263 < baseStart_3827263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827265 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3827265 : Nat := 118140960795 + 3827265 * 2 ^ 59
def prefixEnd_3827265 : Nat := 4983230072969 + 3 ^ 40 * 3827265 * 2
def baseEnd_3827265 : Nat := 1310151024753382361190823

theorem tailTrace_3827265 : CollatzResearch.WordTrace tailWord_3827265 prefixEnd_3827265 1310151024753382361190823 := by
  unfold tailWord_3827265
  simp only [CollatzResearch.WordTrace]
  refine ⟨139591822479480024667787249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93061214986320016445191499 139591822479480024667787249)
  ·
    refine ⟨104693866859610018500840437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139591822479480024667787249 104693866859610018500840437)
    ·
      refine ⟨9815050018088439234453791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104693866859610018500840437 9815050018088439234453791)
      ·
        refine ⟨14722575027132658851680687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9815050018088439234453791 14722575027132658851680687)
        ·
          refine ⟨22083862540698988277521031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14722575027132658851680687 22083862540698988277521031)
          ·
            refine ⟨33125793811048482416281547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22083862540698988277521031 33125793811048482416281547)
            ·
              refine ⟨49688690716572723624422321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33125793811048482416281547 49688690716572723624422321)
              ·
                refine ⟨37266518037429542718316741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49688690716572723624422321 37266518037429542718316741)
                ·
                  refine ⟨6987472132018039259684389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37266518037429542718316741 6987472132018039259684389)
                  ·
                    refine ⟨1310151024753382361190823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987472132018039259684389 1310151024753382361190823)
                    ·
                      rfl

theorem cell22_3827265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3827265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827265 prefixEnd_3827265 := by exact prefixLift 3827265
  have htrace : WordTrace (prefixWord ++ tailWord_3827265) baseStart_3827265 baseEnd_3827265 := by
    simpa [prefixWord, tailWord_3827265, baseEnd_3827265] using wordTrace_append hprefix tailTrace_3827265
  have hstable : (prefixWord ++ tailWord_3827265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827265).length < 2 ^ (prefixWord ++ tailWord_3827265).sum := by decide
  have hdescent : baseEnd_3827265 < baseStart_3827265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827282 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_3827282 : Nat := 118140960795 + 3827282 * 2 ^ 59
def prefixEnd_3827282 : Nat := 4983230072969 + 3 ^ 40 * 3827282 * 2
def baseEnd_3827282 : Nat := 1310156844200799983515771

theorem tailTrace_3827282 : CollatzResearch.WordTrace tailWord_3827282 prefixEnd_3827282 1310156844200799983515771 := by
  unfold tailWord_3827282
  simp only [CollatzResearch.WordTrace]
  refine ⟨34898110630104609142789025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93061628346945624380770733 34898110630104609142789025)
  ·
    refine ⟨26173582972578456857091769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34898110630104609142789025 26173582972578456857091769)
    ·
      refine ⟨19630187229433842642818827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26173582972578456857091769 19630187229433842642818827)
      ·
        refine ⟨29445280844150763964228241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19630187229433842642818827 29445280844150763964228241)
        ·
          refine ⟨22083960633113072973171181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29445280844150763964228241 22083960633113072973171181)
          ·
            refine ⟨8281485237417402364939193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22083960633113072973171181 8281485237417402364939193)
            ·
              refine ⟨6211113928063051773704395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8281485237417402364939193 6211113928063051773704395)
              ·
                refine ⟨9316670892094577660556593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211113928063051773704395 9316670892094577660556593)
                ·
                  refine ⟨6987503169070933245417445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9316670892094577660556593 6987503169070933245417445)
                  ·
                    refine ⟨1310156844200799983515771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987503169070933245417445 1310156844200799983515771)
                    ·
                      rfl

theorem cell22_3827282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_3827282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827282 prefixEnd_3827282 := by exact prefixLift 3827282
  have htrace : WordTrace (prefixWord ++ tailWord_3827282) baseStart_3827282 baseEnd_3827282 := by
    simpa [prefixWord, tailWord_3827282, baseEnd_3827282] using wordTrace_append hprefix tailTrace_3827282
  have hstable : (prefixWord ++ tailWord_3827282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827282).length < 2 ^ (prefixWord ++ tailWord_3827282).sum := by decide
  have hdescent : baseEnd_3827282 < baseStart_3827282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827400 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_3827400 : Nat := 118140960795 + 3827400 * 2 ^ 59
def prefixEnd_3827400 : Nat := 4983230072969 + 3 ^ 40 * 3827400 * 2
def baseEnd_3827400 : Nat := 1310197238012287009065409

theorem tailTrace_3827400 : CollatzResearch.WordTrace tailWord_3827400 prefixEnd_3827400 1310197238012287009065409 := by
  unfold tailWord_3827400
  simp only [CollatzResearch.WordTrace]
  refine ⟨69798373166995471361975827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93064497555993961815967769 69798373166995471361975827)
  ·
    refine ⟨104697559750493207042963741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69798373166995471361975827 104697559750493207042963741)
    ·
      refine ⟨39261584906434952641111403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104697559750493207042963741 39261584906434952641111403)
      ·
        refine ⟨58892377359652428961667105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39261584906434952641111403 58892377359652428961667105)
        ·
          refine ⟨44169283019739321721250329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58892377359652428961667105 44169283019739321721250329)
          ·
            refine ⟨33126962264804491290937747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44169283019739321721250329 33126962264804491290937747)
            ·
              refine ⟨49690443397206736936406621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33126962264804491290937747 49690443397206736936406621)
              ·
                refine ⟨18633916273952526351152483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49690443397206736936406621 18633916273952526351152483)
                ·
                  refine ⟨27950874410928789526728725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18633916273952526351152483 27950874410928789526728725)
                  ·
                    refine ⟨1310197238012287009065409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27950874410928789526728725 1310197238012287009065409)
                    ·
                      rfl

theorem cell22_3827400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_3827400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827400 prefixEnd_3827400 := by exact prefixLift 3827400
  have htrace : WordTrace (prefixWord ++ tailWord_3827400) baseStart_3827400 baseEnd_3827400 := by
    simpa [prefixWord, tailWord_3827400, baseEnd_3827400] using wordTrace_append hprefix tailTrace_3827400
  have hstable : (prefixWord ++ tailWord_3827400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827400).length < 2 ^ (prefixWord ++ tailWord_3827400).sum := by decide
  have hdescent : baseEnd_3827400 < baseStart_3827400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827417 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_3827417 : Nat := 118140960795 + 3827417 * 2 ^ 59
def prefixEnd_3827417 : Nat := 4983230072969 + 3 ^ 40 * 3827417 * 2
def baseEnd_3827417 : Nat := 1310203057459704631390357

theorem tailTrace_3827417 : CollatzResearch.WordTrace tailWord_3827417 prefixEnd_3827417 1310203057459704631390357 := by
  unfold tailWord_3827417
  simp only [CollatzResearch.WordTrace]
  refine ⟨139597366374929354627320505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93064910916619569751547003 139597366374929354627320505)
  ·
    refine ⟨104698024781197015970490379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139597366374929354627320505 104698024781197015970490379)
    ·
      refine ⟨157047037171795523955735569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104698024781197015970490379 157047037171795523955735569)
      ·
        refine ⟨117785277878846642966801677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157047037171795523955735569 117785277878846642966801677)
        ·
          refine ⟨44169479204567491112550629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117785277878846642966801677 44169479204567491112550629)
          ·
            refine ⟨8281777350856404583603243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44169479204567491112550629 8281777350856404583603243)
            ·
              refine ⟨12422666026284606875404865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8281777350856404583603243 12422666026284606875404865)
              ·
                refine ⟨9316999519713455156553649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12422666026284606875404865 9316999519713455156553649)
                ·
                  refine ⟨6987749639785091367415237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9316999519713455156553649 6987749639785091367415237)
                  ·
                    refine ⟨1310203057459704631390357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6987749639785091367415237 1310203057459704631390357)
                    ·
                      rfl

theorem cell22_3827417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_3827417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827417 prefixEnd_3827417 := by exact prefixLift 3827417
  have htrace : WordTrace (prefixWord ++ tailWord_3827417) baseStart_3827417 baseEnd_3827417 := by
    simpa [prefixWord, tailWord_3827417, baseEnd_3827417] using wordTrace_append hprefix tailTrace_3827417
  have hstable : (prefixWord ++ tailWord_3827417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827417).length < 2 ^ (prefixWord ++ tailWord_3827417).sum := by decide
  have hdescent : baseEnd_3827417 < baseStart_3827417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827421 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 6]
def baseStart_3827421 : Nat := 118140960795 + 3827421 * 2 ^ 59
def prefixEnd_3827421 : Nat := 4983230072969 + 3 ^ 40 * 3827421 * 2
def baseEnd_3827421 : Nat := 436734808913816651430115

theorem tailTrace_3827421 : CollatzResearch.WordTrace tailWord_3827421 prefixEnd_3827421 436734808913816651430115 := by
  unfold tailWord_3827421
  simp only [CollatzResearch.WordTrace]
  refine ⟨139597512266914863310466117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93065008177943242206977411 139597512266914863310466117)
  ·
    refine ⟨26174533550046536870712397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139597512266914863310466117 26174533550046536870712397)
    ·
      refine ⟨9815450081267451326517149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26174533550046536870712397 9815450081267451326517149)
      ·
        refine ⟨3680793780475294247443931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9815450081267451326517149 3680793780475294247443931)
        ·
          refine ⟨5521190670712941371165897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680793780475294247443931 5521190670712941371165897)
          ·
            refine ⟨4140893003034706028374423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5521190670712941371165897 4140893003034706028374423)
            ·
              refine ⟨6211339504552059042561635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4140893003034706028374423 6211339504552059042561635)
              ·
                refine ⟨9317009256828088563842453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211339504552059042561635 9317009256828088563842453)
                ·
                  refine ⟨436734808913816651430115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9317009256828088563842453 436734808913816651430115)
                  ·
                    rfl

theorem cell22_3827421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_3827421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827421 prefixEnd_3827421 := by exact prefixLift 3827421
  have htrace : WordTrace (prefixWord ++ tailWord_3827421) baseStart_3827421 baseEnd_3827421 := by
    simpa [prefixWord, tailWord_3827421, baseEnd_3827421] using wordTrace_append hprefix tailTrace_3827421
  have hstable : (prefixWord ++ tailWord_3827421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827421).length < 2 ^ (prefixWord ++ tailWord_3827421).sum := by decide
  have hdescent : baseEnd_3827421 < baseStart_3827421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827432 : List Nat := [2, 1, 4, 1, 3, 2, 2, 7]
def baseStart_3827432 : Nat := 118140960795 + 3827432 * 2 ^ 59
def prefixEnd_3827432 : Nat := 4983230072969 + 3 ^ 40 * 3827432 * 2
def baseEnd_3827432 : Nat := 145578688029583288029479

theorem tailTrace_3827432 : CollatzResearch.WordTrace tailWord_3827432 prefixEnd_3827432 145578688029583288029479 := by
  unfold tailWord_3827432
  simp only [CollatzResearch.WordTrace]
  refine ⟨69798956734937506094558275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93065275646583341459411033 69798956734937506094558275)
  ·
    refine ⟨104698435102406259141837413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69798956734937506094558275 104698435102406259141837413)
    ·
      refine ⟨19630956581701173589094515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104698435102406259141837413 19630956581701173589094515)
      ·
        refine ⟨29446434872551760383641773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19630956581701173589094515 29446434872551760383641773)
        ·
          refine ⟨11042413077206910143865665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29446434872551760383641773 11042413077206910143865665)
          ·
            refine ⟨8281809807905182607899249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11042413077206910143865665 8281809807905182607899249)
            ·
              refine ⟨6211357355928886955924437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8281809807905182607899249 6211357355928886955924437)
              ·
                refine ⟨145578688029583288029479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6211357355928886955924437 145578688029583288029479)
                ·
                  rfl

theorem cell22_3827432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 7].length) (baseStart_3827432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827432 prefixEnd_3827432 := by exact prefixLift 3827432
  have htrace : WordTrace (prefixWord ++ tailWord_3827432) baseStart_3827432 baseEnd_3827432 := by
    simpa [prefixWord, tailWord_3827432, baseEnd_3827432] using wordTrace_append hprefix tailTrace_3827432
  have hstable : (prefixWord ++ tailWord_3827432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827432).length < 2 ^ (prefixWord ++ tailWord_3827432).sum := by decide
  have hdescent : baseEnd_3827432 < baseStart_3827432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827447 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 3, 3]
def baseStart_3827447 : Nat := 118140960795 + 3827447 * 2 ^ 59
def prefixEnd_3827447 : Nat := 4983230072969 + 3 ^ 40 * 3827447 * 2
def baseEnd_3827447 : Nat := 1310213327072794553140265

theorem tailTrace_3827447 : CollatzResearch.WordTrace tailWord_3827447 prefixEnd_3827447 1310213327072794553140265 := by
  unfold tailWord_3827447
  simp only [CollatzResearch.WordTrace]
  refine ⟨139598460564820669750912595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93065640376547113167275063 139598460564820669750912595)
  ·
    refine ⟨209397690847231004626368893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139598460564820669750912595 209397690847231004626368893)
    ·
      refine ⟨78524134067711626734888335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209397690847231004626368893 78524134067711626734888335)
      ·
        refine ⟨117786201101567440102332503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78524134067711626734888335 117786201101567440102332503)
        ·
          refine ⟨176679301652351160153498755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117786201101567440102332503 176679301652351160153498755)
          ·
            refine ⟨265018952478526740230248133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176679301652351160153498755 265018952478526740230248133)
            ·
              refine ⟨49691053589723763793171525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265018952478526740230248133 49691053589723763793171525)
              ·
                refine ⟨9317072548073205711219661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49691053589723763793171525 9317072548073205711219661)
                ·
                  refine ⟨3493902205527452141707373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9317072548073205711219661 3493902205527452141707373)
                  ·
                    refine ⟨1310213327072794553140265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493902205527452141707373 1310213327072794553140265)
                    ·
                      rfl

theorem cell22_3827447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_3827447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827447 prefixEnd_3827447 := by exact prefixLift 3827447
  have htrace : WordTrace (prefixWord ++ tailWord_3827447) baseStart_3827447 baseEnd_3827447 := by
    simpa [prefixWord, tailWord_3827447, baseEnd_3827447] using wordTrace_append hprefix tailTrace_3827447
  have hstable : (prefixWord ++ tailWord_3827447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827447).length < 2 ^ (prefixWord ++ tailWord_3827447).sum := by decide
  have hdescent : baseEnd_3827447 < baseStart_3827447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827477 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 5]
def baseStart_3827477 : Nat := 118140960795 + 3827477 * 2 ^ 59
def prefixEnd_3827477 : Nat := 4983230072969 + 3 ^ 40 * 3827477 * 2
def baseEnd_3827477 : Nat := 436741198895294824963391

theorem tailTrace_3827477 : CollatzResearch.WordTrace tailWord_3827477 prefixEnd_3827477 436741198895294824963391 := by
  unfold tailWord_3827477
  simp only [CollatzResearch.WordTrace]
  refine ⟨139599554754711984874504685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93066369836474656583003123 139599554754711984874504685)
  ·
    refine ⟨52349833033016994327939257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139599554754711984874504685 52349833033016994327939257)
    ·
      refine ⟨39262374774762745745954443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52349833033016994327939257 39262374774762745745954443)
      ·
        refine ⟨58893562162144118618931665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39262374774762745745954443 58893562162144118618931665)
        ·
          refine ⟨44170171621608088964198749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58893562162144118618931665 44170171621608088964198749)
          ·
            refine ⟨16563814358103033361574531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44170171621608088964198749 16563814358103033361574531)
            ·
              refine ⟨24845721537154550042361797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16563814358103033361574531 24845721537154550042361797)
              ·
                refine ⟨4658572788216478132942837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24845721537154550042361797 4658572788216478132942837)
                ·
                  refine ⟨436741198895294824963391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4658572788216478132942837 436741198895294824963391)
                  ·
                    rfl

theorem cell22_3827477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_3827477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827477 prefixEnd_3827477 := by exact prefixLift 3827477
  have htrace : WordTrace (prefixWord ++ tailWord_3827477) baseStart_3827477 baseEnd_3827477 := by
    simpa [prefixWord, tailWord_3827477, baseEnd_3827477] using wordTrace_append hprefix tailTrace_3827477
  have hstable : (prefixWord ++ tailWord_3827477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827477).length < 2 ^ (prefixWord ++ tailWord_3827477).sum := by decide
  have hdescent : baseEnd_3827477 < baseStart_3827477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827492 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_3827492 : Nat := 118140960795 + 3827492 * 2 ^ 59
def prefixEnd_3827492 : Nat := 4983230072969 + 3 ^ 40 * 3827492 * 2
def baseEnd_3827492 : Nat := 1310228731492429435765127

theorem tailTrace_3827492 : CollatzResearch.WordTrace tailWord_3827492 prefixEnd_3827492 1310228731492429435765127 := by
  unfold tailWord_3827492
  simp only [CollatzResearch.WordTrace]
  refine ⟨69800050924828821218150365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93066734566438428290867153 69800050924828821218150365)
  ·
    refine ⟨26175019096810807956806387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69800050924828821218150365 26175019096810807956806387)
    ·
      refine ⟨39262528645216211935209581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26175019096810807956806387 39262528645216211935209581)
      ·
        refine ⟨14723448241956079475703593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39262528645216211935209581 14723448241956079475703593)
        ·
          refine ⟨11042586181467059606777695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14723448241956079475703593 11042586181467059606777695)
          ·
            refine ⟨16563879272200589410166543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11042586181467059606777695 16563879272200589410166543)
            ·
              refine ⟨24845818908300884115249815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16563879272200589410166543 24845818908300884115249815)
              ·
                refine ⟨37268728362451326172874723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24845818908300884115249815 37268728362451326172874723)
                ·
                  refine ⟨55903092543676989259312085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37268728362451326172874723 55903092543676989259312085)
                  ·
                    refine ⟨1310228731492429435765127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55903092543676989259312085 1310228731492429435765127)
                    ·
                      rfl

theorem cell22_3827492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_3827492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827492 prefixEnd_3827492 := by exact prefixLift 3827492
  have htrace : WordTrace (prefixWord ++ tailWord_3827492) baseStart_3827492 baseEnd_3827492 := by
    simpa [prefixWord, tailWord_3827492, baseEnd_3827492] using wordTrace_append hprefix tailTrace_3827492
  have hstable : (prefixWord ++ tailWord_3827492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827492).length < 2 ^ (prefixWord ++ tailWord_3827492).sum := by decide
  have hdescent : baseEnd_3827492 < baseStart_3827492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827526 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3827526 : Nat := 118140960795 + 3827526 * 2 ^ 59
def prefixEnd_3827526 : Nat := 4983230072969 + 3 ^ 40 * 3827526 * 2
def baseEnd_3827526 : Nat := 1310240370387264680415023

theorem tailTrace_3827526 : CollatzResearch.WordTrace tailWord_3827526 prefixEnd_3827526 1310240370387264680415023 := by
  unfold tailWord_3827526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362541935360452070094951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93067561287689644162025621 4362541935360452070094951)
  ·
    refine ⟨6543812903040678105142427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4362541935360452070094951 6543812903040678105142427)
    ·
      refine ⟨9815719354561017157713641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6543812903040678105142427 9815719354561017157713641)
      ·
        refine ⟨7361789515920762868285231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9815719354561017157713641 7361789515920762868285231)
        ·
          refine ⟨11042684273881144302427847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7361789515920762868285231 11042684273881144302427847)
          ·
            refine ⟨16564026410821716453641771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11042684273881144302427847 16564026410821716453641771)
            ·
              refine ⟨24846039616232574680462657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16564026410821716453641771 24846039616232574680462657)
              ·
                refine ⟨18634529712174431010346993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24846039616232574680462657 18634529712174431010346993)
                ·
                  refine ⟨13975897284130823257760245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18634529712174431010346993 13975897284130823257760245)
                  ·
                    refine ⟨1310240370387264680415023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13975897284130823257760245 1310240370387264680415023)
                    ·
                      rfl

theorem cell22_3827526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3827526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827526 prefixEnd_3827526 := by exact prefixLift 3827526
  have htrace : WordTrace (prefixWord ++ tailWord_3827526) baseStart_3827526 baseEnd_3827526 := by
    simpa [prefixWord, tailWord_3827526, baseEnd_3827526] using wordTrace_append hprefix tailTrace_3827526
  have hstable : (prefixWord ++ tailWord_3827526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827526).length < 2 ^ (prefixWord ++ tailWord_3827526).sum := by decide
  have hdescent : baseEnd_3827526 < baseStart_3827526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827552 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_3827552 : Nat := 118140960795 + 3827552 * 2 ^ 59
def prefixEnd_3827552 : Nat := 4983230072969 + 3 ^ 40 * 3827552 * 2
def baseEnd_3827552 : Nat := 1310249270718609279264943

theorem tailTrace_3827552 : CollatzResearch.WordTrace tailWord_3827552 prefixEnd_3827552 1310249270718609279264943 := by
  unfold tailWord_3827552
  simp only [CollatzResearch.WordTrace]
  refine ⟨69801145114720136341742455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93068193486293515122323273 69801145114720136341742455)
  ·
    refine ⟨104701717672080204512613683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69801145114720136341742455 104701717672080204512613683)
    ·
      refine ⟨157052576508120306768920525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104701717672080204512613683 157052576508120306768920525)
      ·
        refine ⟨58894716190545115038345197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157052576508120306768920525 58894716190545115038345197)
        ·
          refine ⟨22085518571454418139379449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58894716190545115038345197 22085518571454418139379449)
          ·
            refine ⟨16564138928590813604534587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22085518571454418139379449 16564138928590813604534587)
            ·
              refine ⟨24846208392886220406801881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16564138928590813604534587 24846208392886220406801881)
              ·
                refine ⟨18634656294664665305101411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24846208392886220406801881 18634656294664665305101411)
                ·
                  refine ⟨27951984441996997957652117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18634656294664665305101411 27951984441996997957652117)
                  ·
                    refine ⟨1310249270718609279264943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27951984441996997957652117 1310249270718609279264943)
                    ·
                      rfl

theorem cell22_3827552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_3827552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827552 prefixEnd_3827552 := by exact prefixLift 3827552
  have htrace : WordTrace (prefixWord ++ tailWord_3827552) baseStart_3827552 baseEnd_3827552 := by
    simpa [prefixWord, tailWord_3827552, baseEnd_3827552] using wordTrace_append hprefix tailTrace_3827552
  have hstable : (prefixWord ++ tailWord_3827552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827552).length < 2 ^ (prefixWord ++ tailWord_3827552).sum := by decide
  have hdescent : baseEnd_3827552 < baseStart_3827552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827646 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_3827646 : Nat := 118140960795 + 3827646 * 2 ^ 59
def prefixEnd_3827646 : Nat := 4983230072969 + 3 ^ 40 * 3827646 * 2
def baseEnd_3827646 : Nat := 436760482946541455804885

theorem tailTrace_3827646 : CollatzResearch.WordTrace tailWord_3827646 prefixEnd_3827646 436760482946541455804885 := by
  unfold tailWord_3827646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17450714836387465842175849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93070479127399817824937861 17450714836387465842175849)
  ·
    refine ⟨13088036127290599381631887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17450714836387465842175849 13088036127290599381631887)
    ·
      refine ⟨19632054190935899072447831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13088036127290599381631887 19632054190935899072447831)
      ·
        refine ⟨29448081286403848608671747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19632054190935899072447831 29448081286403848608671747)
        ·
          refine ⟨44172121929605772913007621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29448081286403848608671747 44172121929605772913007621)
          ·
            refine ⟨8282272861801082421188929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44172121929605772913007621 8282272861801082421188929)
            ·
              refine ⟨6211704646350811815891697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8282272861801082421188929 6211704646350811815891697)
              ·
                refine ⟨4658778484763108861918773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6211704646350811815891697 4658778484763108861918773)
                ·
                  refine ⟨436760482946541455804885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4658778484763108861918773 436760482946541455804885)
                  ·
                    rfl

theorem cell22_3827646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_3827646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827646 prefixEnd_3827646 := by exact prefixLift 3827646
  have htrace : WordTrace (prefixWord ++ tailWord_3827646) baseStart_3827646 baseEnd_3827646 := by
    simpa [prefixWord, tailWord_3827646, baseEnd_3827646] using wordTrace_append hprefix tailTrace_3827646
  have hstable : (prefixWord ++ tailWord_3827646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827646).length < 2 ^ (prefixWord ++ tailWord_3827646).sum := by decide
  have hdescent : baseEnd_3827646 < baseStart_3827646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827704 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_3827704 : Nat := 118140960795 + 3827704 * 2 ^ 59
def prefixEnd_3827704 : Nat := 4983230072969 + 3 ^ 40 * 3827704 * 2
def baseEnd_3827704 : Nat := 1310301303424931549464477

theorem tailTrace_3827704 : CollatzResearch.WordTrace tailWord_3827704 prefixEnd_3827704 1310301303424931549464477 := by
  unfold tailWord_3827704
  simp only [CollatzResearch.WordTrace]
  refine ⟨69803917062444801321509083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93071889416593068428678777 69803917062444801321509083)
  ·
    refine ⟨104705875593667201982263625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69803917062444801321509083 104705875593667201982263625)
    ·
      refine ⟨78529406695250401486697719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104705875593667201982263625 78529406695250401486697719)
      ·
        refine ⟨117794110042875602230046579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78529406695250401486697719 117794110042875602230046579)
        ·
          refine ⟨176691165064313403345069869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117794110042875602230046579 176691165064313403345069869)
          ·
            refine ⟨66259186899117526254401201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176691165064313403345069869 66259186899117526254401201)
            ·
              refine ⟨49694390174338144690800901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66259186899117526254401201 49694390174338144690800901)
              ·
                refine ⟨9317698157688402129525169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49694390174338144690800901 9317698157688402129525169)
                ·
                  refine ⟨6988273618266301597143877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9317698157688402129525169 6988273618266301597143877)
                  ·
                    refine ⟨1310301303424931549464477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6988273618266301597143877 1310301303424931549464477)
                    ·
                      rfl

theorem cell22_3827704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_3827704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827704 prefixEnd_3827704 := by exact prefixLift 3827704
  have htrace : WordTrace (prefixWord ++ tailWord_3827704) baseStart_3827704 baseEnd_3827704 := by
    simpa [prefixWord, tailWord_3827704, baseEnd_3827704] using wordTrace_append hprefix tailTrace_3827704
  have hstable : (prefixWord ++ tailWord_3827704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827704).length < 2 ^ (prefixWord ++ tailWord_3827704).sum := by decide
  have hdescent : baseEnd_3827704 < baseStart_3827704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827723 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 2, 3]
def baseStart_3827723 : Nat := 118140960795 + 3827723 * 2 ^ 59
def prefixEnd_3827723 : Nat := 4983230072969 + 3 ^ 40 * 3827723 * 2
def baseEnd_3827723 : Nat := 1310307807513221833239419

theorem tailTrace_3827723 : CollatzResearch.WordTrace tailWord_3827723 prefixEnd_3827723 1310307807513221833239419 := by
  unfold tailWord_3827723
  simp only [CollatzResearch.WordTrace]
  refine ⟨139608527111820768887959823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93072351407880512591973215 139608527111820768887959823)
  ·
    refine ⟨209412790667731153331939735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139608527111820768887959823 209412790667731153331939735)
    ·
      refine ⟨314119186001596729997909603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209412790667731153331939735 314119186001596729997909603)
      ·
        refine ⟨471178779002395094996864405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314119186001596729997909603 471178779002395094996864405)
        ·
          refine ⟨22086505265737270077978019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 471178779002395094996864405 22086505265737270077978019)
          ·
            refine ⟨33129757898605905116967029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22086505265737270077978019 33129757898605905116967029)
            ·
              refine ⟨3105914802994303604715659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33129757898605905116967029 3105914802994303604715659)
              ·
                refine ⟨4658872204491455407073489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105914802994303604715659 4658872204491455407073489)
                ·
                  refine ⟨3494154153368591555305117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4658872204491455407073489 3494154153368591555305117)
                  ·
                    refine ⟨1310307807513221833239419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494154153368591555305117 1310307807513221833239419)
                    ·
                      rfl

theorem cell22_3827723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 3].length) (baseStart_3827723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827723 prefixEnd_3827723 := by exact prefixLift 3827723
  have htrace : WordTrace (prefixWord ++ tailWord_3827723) baseStart_3827723 baseEnd_3827723 := by
    simpa [prefixWord, tailWord_3827723, baseEnd_3827723] using wordTrace_append hprefix tailTrace_3827723
  have hstable : (prefixWord ++ tailWord_3827723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827723).length < 2 ^ (prefixWord ++ tailWord_3827723).sum := by decide
  have hdescent : baseEnd_3827723 < baseStart_3827723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827766 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3827766 : Nat := 118140960795 + 3827766 * 2 ^ 59
def prefixEnd_3827766 : Nat := 4983230072969 + 3 ^ 40 * 3827766 * 2
def baseEnd_3827766 : Nat := 1310322527291984054414287

theorem tailTrace_3827766 : CollatzResearch.WordTrace tailWord_3827766 prefixEnd_3827766 1310322527291984054414287 := by
  unfold tailWord_3827766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8725630965666561701985947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93073396967109991487850101 8725630965666561701985947)
  ·
    refine ⟨13088446448499842552978921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8725630965666561701985947 13088446448499842552978921)
    ·
      refine ⟨9816334836374881914734191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13088446448499842552978921 9816334836374881914734191)
      ·
        refine ⟨14724502254562322872101287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9816334836374881914734191 14724502254562322872101287)
        ·
          refine ⟨22086753381843484308151931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14724502254562322872101287 22086753381843484308151931)
          ·
            refine ⟨33130130072765226462227897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22086753381843484308151931 33130130072765226462227897)
            ·
              refine ⟨24847597554573919846670923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33130130072765226462227897 24847597554573919846670923)
              ·
                refine ⟨37271396331860879770006385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24847597554573919846670923 37271396331860879770006385)
                ·
                  refine ⟨27953547248895659827504789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37271396331860879770006385 27953547248895659827504789)
                  ·
                    refine ⟨1310322527291984054414287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27953547248895659827504789 1310322527291984054414287)
                    ·
                      rfl

theorem cell22_3827766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3827766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827766 prefixEnd_3827766 := by exact prefixLift 3827766
  have htrace : WordTrace (prefixWord ++ tailWord_3827766) baseStart_3827766 baseEnd_3827766 := by
    simpa [prefixWord, tailWord_3827766, baseEnd_3827766] using wordTrace_append hprefix tailTrace_3827766
  have hstable : (prefixWord ++ tailWord_3827766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827766).length < 2 ^ (prefixWord ++ tailWord_3827766).sum := by decide
  have hdescent : baseEnd_3827766 < baseStart_3827766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827774 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3827774 : Nat := 118140960795 + 3827774 * 2 ^ 59
def prefixEnd_3827774 : Nat := 4983230072969 + 3 ^ 40 * 3827774 * 2
def baseEnd_3827774 : Nat := 1310325265855474700214263

theorem tailTrace_3827774 : CollatzResearch.WordTrace tailWord_3827774 prefixEnd_3827774 1310325265855474700214263 := by
  unfold tailWord_3827774
  simp only [CollatzResearch.WordTrace]
  refine ⟨17451298404329500574758297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93073591489757336398710917 17451298404329500574758297)
  ·
    refine ⟨13088473803247125431068723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17451298404329500574758297 13088473803247125431068723)
    ·
      refine ⟨19632710704870688146603085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13088473803247125431068723 19632710704870688146603085)
      ·
        refine ⟨7362266514326508054976157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19632710704870688146603085 7362266514326508054976157)
        ·
          refine ⟨2760849942872440520616059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7362266514326508054976157 2760849942872440520616059)
          ·
            refine ⟨4141274914308660780924089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760849942872440520616059 4141274914308660780924089)
            ·
              refine ⟨3105956185731495585693067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141274914308660780924089 3105956185731495585693067)
              ·
                refine ⟨4658934278597243378539601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105956185731495585693067 4658934278597243378539601)
                ·
                  refine ⟨3494200708947932533904701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4658934278597243378539601 3494200708947932533904701)
                  ·
                    refine ⟨1310325265855474700214263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494200708947932533904701 1310325265855474700214263)
                    ·
                      rfl

theorem cell22_3827774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3827774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827774 prefixEnd_3827774 := by exact prefixLift 3827774
  have htrace : WordTrace (prefixWord ++ tailWord_3827774) baseStart_3827774 baseEnd_3827774 := by
    simpa [prefixWord, tailWord_3827774, baseEnd_3827774] using wordTrace_append hprefix tailTrace_3827774
  have hstable : (prefixWord ++ tailWord_3827774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827774).length < 2 ^ (prefixWord ++ tailWord_3827774).sum := by decide
  have hdescent : baseEnd_3827774 < baseStart_3827774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827811 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 1, 4]
def baseStart_3827811 : Nat := 118140960795 + 3827811 * 2 ^ 59
def prefixEnd_3827811 : Nat := 4983230072969 + 3 ^ 40 * 3827811 * 2
def baseEnd_3827811 : Nat := 1310337931711618937039149

theorem tailTrace_3827811 : CollatzResearch.WordTrace tailWord_3827811 prefixEnd_3827811 1310337931711618937039149 := by
  unfold tailWord_3827811
  simp only [CollatzResearch.WordTrace]
  refine ⟨139611736735501959917163287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93074491157001306611442191 139611736735501959917163287)
  ·
    refine ⟨209417605103252939875744931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139611736735501959917163287 209417605103252939875744931)
    ·
      refine ⟨314126407654879409813617397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209417605103252939875744931 314126407654879409813617397)
      ·
        refine ⟨29449350717644944670026631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314126407654879409813617397 29449350717644944670026631)
        ·
          refine ⟨44174026076467417005039947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29449350717644944670026631 44174026076467417005039947)
          ·
            refine ⟨66261039114701125507559921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44174026076467417005039947 66261039114701125507559921)
            ·
              refine ⟨49695779336025844130669941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66261039114701125507559921 49695779336025844130669941)
              ·
                refine ⟨4658979312752422887250307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49695779336025844130669941 4658979312752422887250307)
                ·
                  refine ⟨6988468969128634330875461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4658979312752422887250307 6988468969128634330875461)
                  ·
                    refine ⟨1310337931711618937039149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6988468969128634330875461 1310337931711618937039149)
                    ·
                      rfl

theorem cell22_3827811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 4].length) (baseStart_3827811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827811 prefixEnd_3827811 := by exact prefixLift 3827811
  have htrace : WordTrace (prefixWord ++ tailWord_3827811) baseStart_3827811 baseEnd_3827811 := by
    simpa [prefixWord, tailWord_3827811, baseEnd_3827811] using wordTrace_append hprefix tailTrace_3827811
  have hstable : (prefixWord ++ tailWord_3827811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827811).length < 2 ^ (prefixWord ++ tailWord_3827811).sum := by decide
  have hdescent : baseEnd_3827811 < baseStart_3827811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827858 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3827858 : Nat := 118140960795 + 3827858 * 2 ^ 59
def prefixEnd_3827858 : Nat := 4983230072969 + 3 ^ 40 * 3827858 * 2
def baseEnd_3827858 : Nat := 1310354020772126481114005

theorem tailTrace_3827858 : CollatzResearch.WordTrace tailWord_3827858 prefixEnd_3827858 1310354020772126481114005 := by
  unfold tailWord_3827858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34903362741582921736031057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93075633977554457962749485 34903362741582921736031057)
  ·
    refine ⟨26177522056187191302023293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34903362741582921736031057 26177522056187191302023293)
    ·
      refine ⟨9816570771070196738258735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26177522056187191302023293 9816570771070196738258735)
      ·
        refine ⟨14724856156605295107388103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9816570771070196738258735 14724856156605295107388103)
        ·
          refine ⟨22087284234907942661082155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14724856156605295107388103 22087284234907942661082155)
          ·
            refine ⟨33130926352361913991623233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22087284234907942661082155 33130926352361913991623233)
            ·
              refine ⟨24848194764271435493717425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33130926352361913991623233 24848194764271435493717425)
              ·
                refine ⟨18636146073203576620288069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24848194764271435493717425 18636146073203576620288069)
                ·
                  refine ⟨3494277388725670616304013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18636146073203576620288069 3494277388725670616304013)
                  ·
                    refine ⟨1310354020772126481114005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494277388725670616304013 1310354020772126481114005)
                    ·
                      rfl

theorem cell22_3827858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3827858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827858 prefixEnd_3827858 := by exact prefixLift 3827858
  have htrace : WordTrace (prefixWord ++ tailWord_3827858) baseStart_3827858 baseEnd_3827858 := by
    simpa [prefixWord, tailWord_3827858, baseEnd_3827858] using wordTrace_append hprefix tailTrace_3827858
  have hstable : (prefixWord ++ tailWord_3827858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827858).length < 2 ^ (prefixWord ++ tailWord_3827858).sum := by decide
  have hdescent : baseEnd_3827858 < baseStart_3827858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827871 : List Nat := [1, 1, 2, 6, 1, 2, 9]
def baseStart_3827871 : Nat := 118140960795 + 3827871 * 2 ^ 59
def prefixEnd_3827871 : Nat := 4983230072969 + 3 ^ 40 * 3827871 * 2
def baseEnd_3827871 : Nat := 48531795219918473353295

theorem tailTrace_3827871 : CollatzResearch.WordTrace tailWord_3827871 prefixEnd_3827871 48531795219918473353295 := by
  unfold tailWord_3827871
  simp only [CollatzResearch.WordTrace]
  refine ⟨139613925115284590164347467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93075950076856393442898311 139613925115284590164347467)
  ·
    refine ⟨209420887672926885246521201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139613925115284590164347467 209420887672926885246521201)
    ·
      refine ⟨157065665754695163934890901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209420887672926885246521201 157065665754695163934890901)
      ·
        refine ⟨7362453082251335809448011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157065665754695163934890901 7362453082251335809448011)
        ·
          refine ⟨11043679623377003714172017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362453082251335809448011 11043679623377003714172017)
          ·
            refine ⟨8282759717532752785629013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11043679623377003714172017 8282759717532752785629013)
            ·
              refine ⟨48531795219918473353295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8282759717532752785629013 48531795219918473353295)
              ·
                rfl

theorem cell22_3827871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 9].length) (baseStart_3827871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827871 prefixEnd_3827871 := by exact prefixLift 3827871
  have htrace : WordTrace (prefixWord ++ tailWord_3827871) baseStart_3827871 baseEnd_3827871 := by
    simpa [prefixWord, tailWord_3827871, baseEnd_3827871] using wordTrace_append hprefix tailTrace_3827871
  have hstable : (prefixWord ++ tailWord_3827871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827871).length < 2 ^ (prefixWord ++ tailWord_3827871).sum := by decide
  have hdescent : baseEnd_3827871 < baseStart_3827871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827933 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 7]
def baseStart_3827933 : Nat := 118140960795 + 3827933 * 2 ^ 59
def prefixEnd_3827933 : Nat := 4983230072969 + 3 ^ 40 * 3827933 * 2
def baseEnd_3827933 : Nat := 436793231601617095162925

theorem tailTrace_3827933 : CollatzResearch.WordTrace tailWord_3827933 prefixEnd_3827933 436793231601617095162925 := by
  unfold tailWord_3827933
  simp only [CollatzResearch.WordTrace]
  refine ⟨139616186441059974753104453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93077457627373316502069635 139616186441059974753104453)
  ·
    refine ⟨26178034957698745266207085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139616186441059974753104453 26178034957698745266207085)
    ·
      refine ⟨9816763109137029474827657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26178034957698745266207085 9816763109137029474827657)
      ·
        refine ⟨7362572331852772106120743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9816763109137029474827657 7362572331852772106120743)
        ·
          refine ⟨11043858497779158159181115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362572331852772106120743 11043858497779158159181115)
          ·
            refine ⟨16565787746668737238771673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11043858497779158159181115 16565787746668737238771673)
            ·
              refine ⟨12424340810001552929078755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16565787746668737238771673 12424340810001552929078755)
              ·
                refine ⟨18636511215002329393618133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12424340810001552929078755 18636511215002329393618133)
                ·
                  refine ⟨436793231601617095162925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18636511215002329393618133 436793231601617095162925)
                  ·
                    rfl

theorem cell22_3827933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_3827933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827933 prefixEnd_3827933 := by exact prefixLift 3827933
  have htrace : WordTrace (prefixWord ++ tailWord_3827933) baseStart_3827933 baseEnd_3827933 := by
    simpa [prefixWord, tailWord_3827933, baseEnd_3827933] using wordTrace_append hprefix tailTrace_3827933
  have hstable : (prefixWord ++ tailWord_3827933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827933).length < 2 ^ (prefixWord ++ tailWord_3827933).sum := by decide
  have hdescent : baseEnd_3827933 < baseStart_3827933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827937 : List Nat := [1, 2, 3, 1, 3, 1, 5, 2, 1, 3]
def baseStart_3827937 : Nat := 118140960795 + 3827937 * 2 ^ 59
def prefixEnd_3827937 : Nat := 4983230072969 + 3 ^ 40 * 3827937 * 2
def baseEnd_3827937 : Nat := 1310381064086596608388763

theorem tailTrace_3827937 : CollatzResearch.WordTrace tailWord_3827937 prefixEnd_3827937 1310381064086596608388763 := by
  unfold tailWord_3827937
  simp only [CollatzResearch.WordTrace]
  refine ⟨139616332333045483436250065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93077554888696988957500043 139616332333045483436250065)
  ·
    refine ⟨104712249249784112577187549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139616332333045483436250065 104712249249784112577187549)
    ·
      refine ⟨39267093468669042216445331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104712249249784112577187549 39267093468669042216445331)
      ·
        refine ⟨58900640203003563324667997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39267093468669042216445331 58900640203003563324667997)
        ·
          refine ⟨22087740076126336246750499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58900640203003563324667997 22087740076126336246750499)
          ·
            refine ⟨33131610114189504370125749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22087740076126336246750499 33131610114189504370125749)
            ·
              refine ⟨3106088448205266034699289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33131610114189504370125749 3106088448205266034699289)
              ·
                refine ⟨2329566336153949526024467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106088448205266034699289 2329566336153949526024467)
                ·
                  refine ⟨3494349504230924289036701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329566336153949526024467 3494349504230924289036701)
                  ·
                    refine ⟨1310381064086596608388763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494349504230924289036701 1310381064086596608388763)
                    ·
                      rfl

theorem cell22_3827937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_3827937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827937 prefixEnd_3827937 := by exact prefixLift 3827937
  have htrace : WordTrace (prefixWord ++ tailWord_3827937) baseStart_3827937 baseEnd_3827937 := by
    simpa [prefixWord, tailWord_3827937, baseEnd_3827937] using wordTrace_append hprefix tailTrace_3827937
  have hstable : (prefixWord ++ tailWord_3827937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827937).length < 2 ^ (prefixWord ++ tailWord_3827937).sum := by decide
  have hdescent : baseEnd_3827937 < baseStart_3827937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827980 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_3827980 : Nat := 118140960795 + 3827980 * 2 ^ 59
def prefixEnd_3827980 : Nat := 4983230072969 + 3 ^ 40 * 3827980 * 2
def baseEnd_3827980 : Nat := 1310395783865358829563631

theorem tailTrace_3827980 : CollatzResearch.WordTrace tailWord_3827980 prefixEnd_3827980 1310395783865358829563631 := by
  unfold tailWord_3827980
  simp only [CollatzResearch.WordTrace]
  refine ⟨69808950335944850890032697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93078600447926467853376929 69808950335944850890032697)
  ·
    refine ⟨52356712751958638167524523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69808950335944850890032697 52356712751958638167524523)
    ·
      refine ⟨78535069127937957251286785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52356712751958638167524523 78535069127937957251286785)
      ·
        refine ⟨58901301845953467938465089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78535069127937957251286785 58901301845953467938465089)
        ·
          refine ⟨44175976384465100953848817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58901301845953467938465089 44175976384465100953848817)
          ·
            refine ⟨33131982288348825715386613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44175976384465100953848817 33131982288348825715386613)
            ·
              refine ⟨3106123339532702410817495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33131982288348825715386613 3106123339532702410817495)
              ·
                refine ⟨4659185009299053616226243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106123339532702410817495 4659185009299053616226243)
                ·
                  refine ⟨6988777513948580424339365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659185009299053616226243 6988777513948580424339365)
                  ·
                    refine ⟨1310395783865358829563631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6988777513948580424339365 1310395783865358829563631)
                    ·
                      rfl

theorem cell22_3827980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_3827980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827980 prefixEnd_3827980 := by exact prefixLift 3827980
  have htrace : WordTrace (prefixWord ++ tailWord_3827980) baseStart_3827980 baseEnd_3827980 := by
    simpa [prefixWord, tailWord_3827980, baseEnd_3827980] using wordTrace_append hprefix tailTrace_3827980
  have hstable : (prefixWord ++ tailWord_3827980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827980).length < 2 ^ (prefixWord ++ tailWord_3827980).sum := by decide
  have hdescent : baseEnd_3827980 < baseStart_3827980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3827995 : List Nat := [1, 1, 1, 1, 1, 1, 10, 2, 4]
def baseStart_3827995 : Nat := 118140960795 + 3827995 * 2 ^ 59
def prefixEnd_3827995 : Nat := 4983230072969 + 3 ^ 40 * 3827995 * 2
def baseEnd_3827995 : Nat := 436800306223967930146195

theorem tailTrace_3827995 : CollatzResearch.WordTrace tailWord_3827995 prefixEnd_3827995 436800306223967930146195 := by
  unfold tailWord_3827995
  simp only [CollatzResearch.WordTrace]
  refine ⟨139618447766835359341861439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93078965177890239561240959 139618447766835359341861439)
  ·
    refine ⟨209427671650253039012792159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139618447766835359341861439 209427671650253039012792159)
    ·
      refine ⟨314141507475379558519188239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209427671650253039012792159 314141507475379558519188239)
      ·
        refine ⟨471212261213069337778782359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314141507475379558519188239 471212261213069337778782359)
        ·
          refine ⟨706818391819604006668173539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471212261213069337778782359 706818391819604006668173539)
          ·
            refine ⟨1060227587729406010002260309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706818391819604006668173539 1060227587729406010002260309)
            ·
              refine ⟨3106135510925994169928497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1060227587729406010002260309 3106135510925994169928497)
              ·
                refine ⟨2329601633194495627446373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106135510925994169928497 2329601633194495627446373)
                ·
                  refine ⟨436800306223967930146195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329601633194495627446373 436800306223967930146195)
                  ·
                    rfl

theorem cell22_3827995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 4].length) (baseStart_3827995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3827995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3827995 prefixEnd_3827995 := by exact prefixLift 3827995
  have htrace : WordTrace (prefixWord ++ tailWord_3827995) baseStart_3827995 baseEnd_3827995 := by
    simpa [prefixWord, tailWord_3827995, baseEnd_3827995] using wordTrace_append hprefix tailTrace_3827995
  have hstable : (prefixWord ++ tailWord_3827995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3827995).length < 2 ^ (prefixWord ++ tailWord_3827995).sum := by decide
  have hdescent : baseEnd_3827995 < baseStart_3827995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3827995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828025 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_3828025 : Nat := 118140960795 + 3828025 * 2 ^ 59
def prefixEnd_3828025 : Nat := 4983230072969 + 3 ^ 40 * 3828025 * 2
def baseEnd_3828025 : Nat := 1310411188284993712188493

theorem tailTrace_3828025 : CollatzResearch.WordTrace tailWord_3828025 prefixEnd_3828025 1310411188284993712188493 := by
  unfold tailWord_3828025
  simp only [CollatzResearch.WordTrace]
  refine ⟨139619541956726674465453529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93079694637817782976969019 139619541956726674465453529)
  ·
    refine ⟨104714656467545005849090147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139619541956726674465453529 104714656467545005849090147)
    ·
      refine ⟨157071984701317508773635221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104714656467545005849090147 157071984701317508773635221)
      ·
        refine ⟨7362749282874258223764151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157071984701317508773635221 7362749282874258223764151)
        ·
          refine ⟨11044123924311387335646227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362749282874258223764151 11044123924311387335646227)
          ·
            refine ⟨16566185886467081003469341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11044123924311387335646227 16566185886467081003469341)
            ·
              refine ⟨6212319707425155376301003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16566185886467081003469341 6212319707425155376301003)
              ·
                refine ⟨9318479561137733064451505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212319707425155376301003 9318479561137733064451505)
                ·
                  refine ⟨6988859670853299798338629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9318479561137733064451505 6988859670853299798338629)
                  ·
                    refine ⟨1310411188284993712188493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6988859670853299798338629 1310411188284993712188493)
                    ·
                      rfl

theorem cell22_3828025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_3828025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828025 prefixEnd_3828025 := by exact prefixLift 3828025
  have htrace : WordTrace (prefixWord ++ tailWord_3828025) baseStart_3828025 baseEnd_3828025 := by
    simpa [prefixWord, tailWord_3828025, baseEnd_3828025] using wordTrace_append hprefix tailTrace_3828025
  have hstable : (prefixWord ++ tailWord_3828025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828025).length < 2 ^ (prefixWord ++ tailWord_3828025).sum := by decide
  have hdescent : baseEnd_3828025 < baseStart_3828025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828055 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 3, 3]
def baseStart_3828055 : Nat := 118140960795 + 3828055 * 2 ^ 59
def prefixEnd_3828055 : Nat := 4983230072969 + 3 ^ 40 * 3828055 * 2
def baseEnd_3828055 : Nat := 1310421457898083633938401

theorem tailTrace_3828055 : CollatzResearch.WordTrace tailWord_3828055 prefixEnd_3828055 1310421457898083633938401 := by
  unfold tailWord_3828055
  simp only [CollatzResearch.WordTrace]
  refine ⟨139620636146617989589045619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93080424097745326392697079 139620636146617989589045619)
  ·
    refine ⟨209430954219926984383568429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139620636146617989589045619 209430954219926984383568429)
    ·
      refine ⟨78536607832472619143838161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209430954219926984383568429 78536607832472619143838161)
      ·
        refine ⟨58902455874354464357878621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78536607832472619143838161 58902455874354464357878621)
        ·
          refine ⟨22088420952882924134204483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58902455874354464357878621 22088420952882924134204483)
          ·
            refine ⟨33132631429324386201306725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22088420952882924134204483 33132631429324386201306725)
            ·
              refine ⟨6212368392998322412745011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33132631429324386201306725 6212368392998322412745011)
              ·
                refine ⟨9318552589497483619117517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212368392998322412745011 9318552589497483619117517)
                ·
                  refine ⟨3494457221061556357169069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9318552589497483619117517 3494457221061556357169069)
                  ·
                    refine ⟨1310421457898083633938401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494457221061556357169069 1310421457898083633938401)
                    ·
                      rfl

theorem cell22_3828055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_3828055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828055 prefixEnd_3828055 := by exact prefixLift 3828055
  have htrace : WordTrace (prefixWord ++ tailWord_3828055) baseStart_3828055 baseEnd_3828055 := by
    simpa [prefixWord, tailWord_3828055, baseEnd_3828055] using wordTrace_append hprefix tailTrace_3828055
  have hstable : (prefixWord ++ tailWord_3828055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828055).length < 2 ^ (prefixWord ++ tailWord_3828055).sum := by decide
  have hdescent : baseEnd_3828055 < baseStart_3828055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828106 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_3828106 : Nat := 118140960795 + 3828106 * 2 ^ 59
def prefixEnd_3828106 : Nat := 4983230072969 + 3 ^ 40 * 3828106 * 2
def baseEnd_3828106 : Nat := 1310438916240336500913245

theorem tailTrace_3828106 : CollatzResearch.WordTrace tailWord_3828106 prefixEnd_3828106 1310438916240336500913245 := by
  unfold tailWord_3828106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34905624067358306324788043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93081664179622150199434781 34905624067358306324788043)
  ·
    refine ⟨52358436101037459487182065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34905624067358306324788043 52358436101037459487182065)
    ·
      refine ⟨39268827075778094615386549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52358436101037459487182065 39268827075778094615386549)
      ·
        refine ⟨3681452538354196370192489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39268827075778094615386549 3681452538354196370192489)
        ·
          refine ⟨2761089403765647277644367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3681452538354196370192489 2761089403765647277644367)
          ·
            refine ⟨4141634105648470916466551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761089403765647277644367 4141634105648470916466551)
            ·
              refine ⟨6212451158472706374699827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141634105648470916466551 6212451158472706374699827)
              ·
                refine ⟨9318676737709059562049741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212451158472706374699827 9318676737709059562049741)
                ·
                  refine ⟨3494503776640897335768653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9318676737709059562049741 3494503776640897335768653)
                  ·
                    refine ⟨1310438916240336500913245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494503776640897335768653 1310438916240336500913245)
                    ·
                      rfl

theorem cell22_3828106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_3828106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828106 prefixEnd_3828106 := by exact prefixLift 3828106
  have htrace : WordTrace (prefixWord ++ tailWord_3828106) baseStart_3828106 baseEnd_3828106 := by
    simpa [prefixWord, tailWord_3828106, baseEnd_3828106] using wordTrace_append hprefix tailTrace_3828106
  have hstable : (prefixWord ++ tailWord_3828106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828106).length < 2 ^ (prefixWord ++ tailWord_3828106).sum := by decide
  have hdescent : baseEnd_3828106 < baseStart_3828106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828145 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_3828145 : Nat := 118140960795 + 3828145 * 2 ^ 59
def prefixEnd_3828145 : Nat := 4983230072969 + 3 ^ 40 * 3828145 * 2
def baseEnd_3828145 : Nat := 1310452266737353399188125

theorem tailTrace_3828145 : CollatzResearch.WordTrace tailWord_3828145 prefixEnd_3828145 1310452266737353399188125 := by
  unfold tailWord_3828145
  simp only [CollatzResearch.WordTrace]
  refine ⟨139623918716291934959821889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93082612477527956639881259 139623918716291934959821889)
  ·
    refine ⟨104717939037218951219866417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139623918716291934959821889 104717939037218951219866417)
    ·
      refine ⟨78538454277914213414899813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104717939037218951219866417 78538454277914213414899813)
      ·
        refine ⟨14725960177108915015293715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78538454277914213414899813 14725960177108915015293715)
        ·
          refine ⟨22088940265663372522940573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14725960177108915015293715 22088940265663372522940573)
          ·
            refine ⟨8283352599623764696102715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22088940265663372522940573 8283352599623764696102715)
            ·
              refine ⟨12425028899435647044154073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8283352599623764696102715 12425028899435647044154073)
              ·
                refine ⟨9318771674576735283115555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12425028899435647044154073 9318771674576735283115555)
                ·
                  refine ⟨13978157511865102924673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9318771674576735283115555 13978157511865102924673333)
                  ·
                    refine ⟨1310452266737353399188125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13978157511865102924673333 1310452266737353399188125)
                    ·
                      rfl

theorem cell22_3828145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_3828145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828145 prefixEnd_3828145 := by exact prefixLift 3828145
  have htrace : WordTrace (prefixWord ++ tailWord_3828145) baseStart_3828145 baseEnd_3828145 := by
    simpa [prefixWord, tailWord_3828145, baseEnd_3828145] using wordTrace_append hprefix tailTrace_3828145
  have hstable : (prefixWord ++ tailWord_3828145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828145).length < 2 ^ (prefixWord ++ tailWord_3828145).sum := by decide
  have hdescent : baseEnd_3828145 < baseStart_3828145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828149 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_3828149 : Nat := 118140960795 + 3828149 * 2 ^ 59
def prefixEnd_3828149 : Nat := 4983230072969 + 3 ^ 40 * 3828149 * 2
def baseEnd_3828149 : Nat := 1310453636019098722088113

theorem tailTrace_3828149 : CollatzResearch.WordTrace tailWord_3828149 prefixEnd_3828149 1310453636019098722088113 := by
  unfold tailWord_3828149
  simp only [CollatzResearch.WordTrace]
  refine ⟨139624064608277443642967501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93082709738851629095311667 139624064608277443642967501)
  ·
    refine ⟨52359024228104041366112813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139624064608277443642967501 52359024228104041366112813)
    ·
      refine ⟨19634634085539015512292305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52359024228104041366112813 19634634085539015512292305)
      ·
        refine ⟨14725975564154261634219229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19634634085539015512292305 14725975564154261634219229)
        ·
          refine ⟨5522240836557848112832211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14725975564154261634219229 5522240836557848112832211)
          ·
            refine ⟨8283361254836772169248317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522240836557848112832211 8283361254836772169248317)
            ·
              refine ⟨3106260470563789563468119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8283361254836772169248317 3106260470563789563468119)
              ·
                refine ⟨4659390705845684345202179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106260470563789563468119 4659390705845684345202179)
                ·
                  refine ⟨6989086058768526517803269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659390705845684345202179 6989086058768526517803269)
                  ·
                    refine ⟨1310453636019098722088113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989086058768526517803269 1310453636019098722088113)
                    ·
                      rfl

theorem cell22_3828149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_3828149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828149 prefixEnd_3828149 := by exact prefixLift 3828149
  have htrace : WordTrace (prefixWord ++ tailWord_3828149) baseStart_3828149 baseEnd_3828149 := by
    simpa [prefixWord, tailWord_3828149, baseEnd_3828149] using wordTrace_append hprefix tailTrace_3828149
  have hstable : (prefixWord ++ tailWord_3828149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828149).length < 2 ^ (prefixWord ++ tailWord_3828149).sum := by decide
  have hdescent : baseEnd_3828149 < baseStart_3828149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828164 : List Nat := [2, 3, 3, 2, 2, 1, 1, 4, 4]
def baseStart_3828164 : Nat := 118140960795 + 3828164 * 2 ^ 59
def prefixEnd_3828164 : Nat := 4983230072969 + 3 ^ 40 * 3828164 * 2
def baseEnd_3828164 : Nat := 436819590275214560987689

theorem tailTrace_3828164 : CollatzResearch.WordTrace tailWord_3828164 prefixEnd_3828164 436819590275214560987689 := by
  unfold tailWord_3828164
  simp only [CollatzResearch.WordTrace]
  refine ⟨69812305851611550602381773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93083074468815400803175697 69812305851611550602381773)
  ·
    refine ⟨26179614694354331475893165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69812305851611550602381773 26179614694354331475893165)
    ·
      refine ⟨9817355510382874303459937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26179614694354331475893165 9817355510382874303459937)
      ·
        refine ⟨7363016632787155727594953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9817355510382874303459937 7363016632787155727594953)
        ·
          refine ⟨5522262474590366795696215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7363016632787155727594953 5522262474590366795696215)
          ·
            refine ⟨8283393711885550193544323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522262474590366795696215 8283393711885550193544323)
            ·
              refine ⟨12425090567828325290316485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8283393711885550193544323 12425090567828325290316485)
              ·
                refine ⟨2329704481467810991934341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12425090567828325290316485 2329704481467810991934341)
                ·
                  refine ⟨436819590275214560987689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2329704481467810991934341 436819590275214560987689)
                  ·
                    rfl

theorem cell22_3828164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_3828164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828164 prefixEnd_3828164 := by exact prefixLift 3828164
  have htrace : WordTrace (prefixWord ++ tailWord_3828164) baseStart_3828164 baseEnd_3828164 := by
    simpa [prefixWord, tailWord_3828164, baseEnd_3828164] using wordTrace_append hprefix tailTrace_3828164
  have hstable : (prefixWord ++ tailWord_3828164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828164).length < 2 ^ (prefixWord ++ tailWord_3828164).sum := by decide
  have hdescent : baseEnd_3828164 < baseStart_3828164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828194 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3828194 : Nat := 118140960795 + 3828194 * 2 ^ 59
def prefixEnd_3828194 : Nat := 4983230072969 + 3 ^ 40 * 3828194 * 2
def baseEnd_3828194 : Nat := 1310469040438733604712975

theorem tailTrace_3828194 : CollatzResearch.WordTrace tailWord_3828194 prefixEnd_3828194 1310469040438733604712975 := by
  unfold tailWord_3828194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34906426473278604082088909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93083803928742944218903757 34906426473278604082088909)
  ·
    refine ⟨13089909927479476530783341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34906426473278604082088909 13089909927479476530783341)
    ·
      refine ⟨4908716222804803699043753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13089909927479476530783341 4908716222804803699043753)
      ·
        refine ⟨3681537167103602774282815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4908716222804803699043753 3681537167103602774282815)
        ·
          refine ⟨5522305750655404161424223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681537167103602774282815 5522305750655404161424223)
          ·
            refine ⟨8283458625983106242136335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522305750655404161424223 8283458625983106242136335)
            ·
              refine ⟨12425187938974659363204503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8283458625983106242136335 12425187938974659363204503)
              ·
                refine ⟨18637781908461989044806755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12425187938974659363204503 18637781908461989044806755)
                ·
                  refine ⟨27956672862692983567210133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18637781908461989044806755 27956672862692983567210133)
                  ·
                    refine ⟨1310469040438733604712975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27956672862692983567210133 1310469040438733604712975)
                    ·
                      rfl

theorem cell22_3828194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3828194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828194 prefixEnd_3828194 := by exact prefixLift 3828194
  have htrace : WordTrace (prefixWord ++ tailWord_3828194) baseStart_3828194 baseEnd_3828194 := by
    simpa [prefixWord, tailWord_3828194, baseEnd_3828194] using wordTrace_append hprefix tailTrace_3828194
  have hstable : (prefixWord ++ tailWord_3828194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828194).length < 2 ^ (prefixWord ++ tailWord_3828194).sum := by decide
  have hdescent : baseEnd_3828194 < baseStart_3828194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828203 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 7]
def baseStart_3828203 : Nat := 118140960795 + 3828203 * 2 ^ 59
def prefixEnd_3828203 : Nat := 4983230072969 + 3 ^ 40 * 3828203 * 2
def baseEnd_3828203 : Nat := 436824040440886860412649

theorem tailTrace_3828203 : CollatzResearch.WordTrace tailWord_3828203 prefixEnd_3828203 436824040440886860412649 := by
  unfold tailWord_3828203
  simp only [CollatzResearch.WordTrace]
  refine ⟨139626034150081810865433263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93084022766721207243622175 139626034150081810865433263)
  ·
    refine ⟨209439051225122716298149895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139626034150081810865433263 209439051225122716298149895)
    ·
      refine ⟨314158576837684074447224843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209439051225122716298149895 314158576837684074447224843)
      ·
        refine ⟨471237865256526111670837265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314158576837684074447224843 471237865256526111670837265)
        ·
          refine ⟨353428398942394583753127949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471237865256526111670837265 353428398942394583753127949)
          ·
            refine ⟨132535649603397968907422981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353428398942394583753127949 132535649603397968907422981)
            ·
              refine ⟨24850434300637119170141809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132535649603397968907422981 24850434300637119170141809)
              ·
                refine ⟨18637825725477839377606357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24850434300637119170141809 18637825725477839377606357)
                ·
                  refine ⟨436824040440886860412649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18637825725477839377606357 436824040440886860412649)
                  ·
                    rfl

theorem cell22_3828203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 7].length) (baseStart_3828203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828203 prefixEnd_3828203 := by exact prefixLift 3828203
  have htrace : WordTrace (prefixWord ++ tailWord_3828203) baseStart_3828203 baseEnd_3828203 := by
    simpa [prefixWord, tailWord_3828203, baseEnd_3828203] using wordTrace_append hprefix tailTrace_3828203
  have hstable : (prefixWord ++ tailWord_3828203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828203).length < 2 ^ (prefixWord ++ tailWord_3828203).sum := by decide
  have hdescent : baseEnd_3828203 < baseStart_3828203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828213 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3828213 : Nat := 118140960795 + 3828213 * 2 ^ 59
def prefixEnd_3828213 : Nat := 4983230072969 + 3 ^ 40 * 3828213 * 2
def baseEnd_3828213 : Nat := 1310475544527023888487917

theorem tailTrace_3828213 : CollatzResearch.WordTrace tailWord_3828213 prefixEnd_3828213 1310475544527023888487917 := by
  unfold tailWord_3828213
  simp only [CollatzResearch.WordTrace]
  refine ⟨139626398880045582573297293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93084265920030388382198195 139626398880045582573297293)
  ·
    refine ⟨52359899580017093464986485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139626398880045582573297293 52359899580017093464986485)
    ·
      refine ⟨4908740585626602512342483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52359899580017093464986485 4908740585626602512342483)
      ·
        refine ⟨7363110878439903768513725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4908740585626602512342483 7363110878439903768513725)
        ·
          refine ⟨2761166579414963913192647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7363110878439903768513725 2761166579414963913192647)
          ·
            refine ⟨4141749869122445869788971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761166579414963913192647 4141749869122445869788971)
            ·
              refine ⟨6212624803683668804683457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141749869122445869788971 6212624803683668804683457)
              ·
                refine ⟨4659468602762751603512593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6212624803683668804683457 4659468602762751603512593)
                ·
                  refine ⟨3494601452072063702634445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4659468602762751603512593 3494601452072063702634445)
                  ·
                    refine ⟨1310475544527023888487917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494601452072063702634445 1310475544527023888487917)
                    ·
                      rfl

theorem cell22_3828213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3828213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828213 prefixEnd_3828213 := by exact prefixLift 3828213
  have htrace : WordTrace (prefixWord ++ tailWord_3828213) baseStart_3828213 baseEnd_3828213 := by
    simpa [prefixWord, tailWord_3828213, baseEnd_3828213] using wordTrace_append hprefix tailTrace_3828213
  have hstable : (prefixWord ++ tailWord_3828213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828213).length < 2 ^ (prefixWord ++ tailWord_3828213).sum := by decide
  have hdescent : baseEnd_3828213 < baseStart_3828213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828230 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3828230 : Nat := 118140960795 + 3828230 * 2 ^ 59
def prefixEnd_3828230 : Nat := 4983230072969 + 3 ^ 40 * 3828230 * 2
def baseEnd_3828230 : Nat := 1310481363974441510812865

theorem tailTrace_3828230 : CollatzResearch.WordTrace tailWord_3828230 prefixEnd_3828230 1310481363974441510812865 := by
  unfold tailWord_3828230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4363344341280749827395817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93084679280655996317777429 4363344341280749827395817)
  ·
    refine ⟨3272508255960562370546863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4363344341280749827395817 3272508255960562370546863)
    ·
      refine ⟨4908762383940843555820295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3272508255960562370546863 4908762383940843555820295)
      ·
        refine ⟨7363143575911265333730443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4908762383940843555820295 7363143575911265333730443)
        ·
          refine ⟨11044715363866898000595665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363143575911265333730443 11044715363866898000595665)
          ·
            refine ⟨8283536522900173500446749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11044715363866898000595665 8283536522900173500446749)
            ·
              refine ⟨3106326196087565062667531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8283536522900173500446749 3106326196087565062667531)
              ·
                refine ⟨4659489294131347594001297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106326196087565062667531 4659489294131347594001297)
                ·
                  refine ⟨3494616970598510695500973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4659489294131347594001297 3494616970598510695500973)
                  ·
                    refine ⟨1310481363974441510812865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494616970598510695500973 1310481363974441510812865)
                    ·
                      rfl

theorem cell22_3828230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3828230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828230 prefixEnd_3828230 := by exact prefixLift 3828230
  have htrace : WordTrace (prefixWord ++ tailWord_3828230) baseStart_3828230 baseEnd_3828230 := by
    simpa [prefixWord, tailWord_3828230, baseEnd_3828230] using wordTrace_append hprefix tailTrace_3828230
  have hstable : (prefixWord ++ tailWord_3828230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828230).length < 2 ^ (prefixWord ++ tailWord_3828230).sum := by decide
  have hdescent : baseEnd_3828230 < baseStart_3828230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828233 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_3828233 : Nat := 118140960795 + 3828233 * 2 ^ 59
def prefixEnd_3828233 : Nat := 4983230072969 + 3 ^ 40 * 3828233 * 2
def baseEnd_3828233 : Nat := 1310482390935750502987855

theorem tailTrace_3828233 : CollatzResearch.WordTrace tailWord_3828233 prefixEnd_3828233 1310482390935750502987855 := by
  unfold tailWord_3828233
  simp only [CollatzResearch.WordTrace]
  refine ⟨139627128339973125989025353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93084752226648750659350235 139627128339973125989025353)
  ·
    refine ⟨104720346254979844491769015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139627128339973125989025353 104720346254979844491769015)
    ·
      refine ⟨157080519382469766737653523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104720346254979844491769015 157080519382469766737653523)
      ·
        refine ⟨235620779073704650106480285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157080519382469766737653523 235620779073704650106480285)
        ·
          refine ⟨88357792152639243789930107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235620779073704650106480285 88357792152639243789930107)
          ·
            refine ⟨132536688228958865684895161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88357792152639243789930107 132536688228958865684895161)
            ·
              refine ⟨99402516171719149263671371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132536688228958865684895161 99402516171719149263671371)
              ·
                refine ⟨149103774257578723895507057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99402516171719149263671371 149103774257578723895507057)
                ·
                  refine ⟨111827830693184042921630293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149103774257578723895507057 111827830693184042921630293)
                  ·
                    refine ⟨1310482390935750502987855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111827830693184042921630293 1310482390935750502987855)
                    ·
                      rfl

theorem cell22_3828233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_3828233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828233 prefixEnd_3828233 := by exact prefixLift 3828233
  have htrace : WordTrace (prefixWord ++ tailWord_3828233) baseStart_3828233 baseEnd_3828233 := by
    simpa [prefixWord, tailWord_3828233, baseEnd_3828233] using wordTrace_append hprefix tailTrace_3828233
  have hstable : (prefixWord ++ tailWord_3828233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828233).length < 2 ^ (prefixWord ++ tailWord_3828233).sum := by decide
  have hdescent : baseEnd_3828233 < baseStart_3828233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828235 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 2, 5]
def baseStart_3828235 : Nat := 118140960795 + 3828235 * 2 ^ 59
def prefixEnd_3828235 : Nat := 4983230072969 + 3 ^ 40 * 3828235 * 2
def baseEnd_3828235 : Nat := 1310483075576623164437849

theorem tailTrace_3828235 : CollatzResearch.WordTrace tailWord_3828235 prefixEnd_3828235 1310483075576623164437849 := by
  unfold tailWord_3828235
  simp only [CollatzResearch.WordTrace]
  refine ⟨139627201285965880330598159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93084800857310586887065439 139627201285965880330598159)
  ·
    refine ⟨209440801928948820495897239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139627201285965880330598159 209440801928948820495897239)
    ·
      refine ⟨314161202893423230743845859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209440801928948820495897239 314161202893423230743845859)
      ·
        refine ⟨471241804340134846115768789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314161202893423230743845859 471241804340134846115768789)
        ·
          refine ⟨11044729789221910455838331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 471241804340134846115768789 11044729789221910455838331)
          ·
            refine ⟨16567094683832865683757497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11044729789221910455838331 16567094683832865683757497)
            ·
              refine ⟨12425321012874649262818123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16567094683832865683757497 12425321012874649262818123)
              ·
                refine ⟨18637981519311973894227185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12425321012874649262818123 18637981519311973894227185)
                ·
                  refine ⟨13978486139483980420670389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18637981519311973894227185 13978486139483980420670389)
                  ·
                    refine ⟨1310483075576623164437849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13978486139483980420670389 1310483075576623164437849)
                    ·
                      rfl

theorem cell22_3828235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_3828235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828235 prefixEnd_3828235 := by exact prefixLift 3828235
  have htrace : WordTrace (prefixWord ++ tailWord_3828235) baseStart_3828235 baseEnd_3828235 := by
    simpa [prefixWord, tailWord_3828235, baseEnd_3828235] using wordTrace_append hprefix tailTrace_3828235
  have hstable : (prefixWord ++ tailWord_3828235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828235).length < 2 ^ (prefixWord ++ tailWord_3828235).sum := by decide
  have hdescent : baseEnd_3828235 < baseStart_3828235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828250 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_3828250 : Nat := 118140960795 + 3828250 * 2 ^ 59
def prefixEnd_3828250 : Nat := 4983230072969 + 3 ^ 40 * 3828250 * 2
def baseEnd_3828250 : Nat := 1310488210383168125312803

theorem tailTrace_3828250 : CollatzResearch.WordTrace tailWord_3828250 prefixEnd_3828250 1310488210383168125312803 := by
  unfold tailWord_3828250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34906937095227884473098551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93085165587274358594929469 34906937095227884473098551)
  ·
    refine ⟨52360405642841826709647827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34906937095227884473098551 52360405642841826709647827)
    ·
      refine ⟨78540608464262740064471741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52360405642841826709647827 78540608464262740064471741)
      ·
        refine ⟨29452728174098527524176903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78540608464262740064471741 29452728174098527524176903)
        ·
          refine ⟨44179092261147791286265355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29452728174098527524176903 44179092261147791286265355)
          ·
            refine ⟨66268638391721686929398033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44179092261147791286265355 66268638391721686929398033)
            ·
              refine ⟨49701478793791265197048525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66268638391721686929398033 49701478793791265197048525)
              ·
                refine ⟨18638054547671724448893197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49701478793791265197048525 18638054547671724448893197)
                ·
                  refine ⟨6989270455376896668334949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18638054547671724448893197 6989270455376896668334949)
                  ·
                    refine ⟨1310488210383168125312803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989270455376896668334949 1310488210383168125312803)
                    ·
                      rfl

theorem cell22_3828250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_3828250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828250 prefixEnd_3828250 := by exact prefixLift 3828250
  have htrace : WordTrace (prefixWord ++ tailWord_3828250) baseStart_3828250 baseEnd_3828250 := by
    simpa [prefixWord, tailWord_3828250, baseEnd_3828250] using wordTrace_append hprefix tailTrace_3828250
  have hstable : (prefixWord ++ tailWord_3828250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828250).length < 2 ^ (prefixWord ++ tailWord_3828250).sum := by decide
  have hdescent : baseEnd_3828250 < baseStart_3828250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828282 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_3828282 : Nat := 118140960795 + 3828282 * 2 ^ 59
def prefixEnd_3828282 : Nat := 4983230072969 + 3 ^ 40 * 3828282 * 2
def baseEnd_3828282 : Nat := 436833054879043569504235

theorem tailTrace_3828282 : CollatzResearch.WordTrace tailWord_3828282 prefixEnd_3828282 436833054879043569504235 := by
  unfold tailWord_3828282
  simp only [CollatzResearch.WordTrace]
  refine ⟨34907228879198901839389775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93085943677863738238372733 34907228879198901839389775)
  ·
    refine ⟨52360843318798352759084663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34907228879198901839389775 52360843318798352759084663)
    ·
      refine ⟨78541264978197529138626995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52360843318798352759084663 78541264978197529138626995)
      ·
        refine ⟨117811897467296293707940493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78541264978197529138626995 117811897467296293707940493)
        ·
          refine ⟨44179461550236110140477685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117811897467296293707940493 44179461550236110140477685)
          ·
            refine ⟨4141824520334635325669783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44179461550236110140477685 4141824520334635325669783)
            ·
              refine ⟨6212736780501952988504675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141824520334635325669783 6212736780501952988504675)
              ·
                refine ⟨9319105170752929482757013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212736780501952988504675 9319105170752929482757013)
                ·
                  refine ⟨436833054879043569504235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9319105170752929482757013 436833054879043569504235)
                  ·
                    rfl

theorem cell22_3828282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_3828282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828282 prefixEnd_3828282 := by exact prefixLift 3828282
  have htrace : WordTrace (prefixWord ++ tailWord_3828282) baseStart_3828282 baseEnd_3828282 := by
    simpa [prefixWord, tailWord_3828282, baseEnd_3828282] using wordTrace_append hprefix tailTrace_3828282
  have hstable : (prefixWord ++ tailWord_3828282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828282).length < 2 ^ (prefixWord ++ tailWord_3828282).sum := by decide
  have hdescent : baseEnd_3828282 < baseStart_3828282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828301 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3828301 : Nat := 118140960795 + 3828301 * 2 ^ 59
def prefixEnd_3828301 : Nat := 4983230072969 + 3 ^ 40 * 3828301 * 2
def baseEnd_3828301 : Nat := 1310505668725420992287647

theorem tailTrace_3828301 : CollatzResearch.WordTrace tailWord_3828301 prefixEnd_3828301 1310505668725420992287647 := by
  unfold tailWord_3828301
  simp only [CollatzResearch.WordTrace]
  refine ⟨139629608503726773602500757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93086405669151182401667171 139629608503726773602500757)
  ·
    refine ⟨6545137898612192512617223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139629608503726773602500757 6545137898612192512617223)
    ·
      refine ⟨9817706847918288768925835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6545137898612192512617223 9817706847918288768925835)
      ·
        refine ⟨14726560271877433153388753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9817706847918288768925835 14726560271877433153388753)
        ·
          refine ⟨11044920203908074865041565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14726560271877433153388753 11044920203908074865041565)
          ·
            refine ⟨4141845076465528074390587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11044920203908074865041565 4141845076465528074390587)
            ·
              refine ⟨6212767614698292111585881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141845076465528074390587 6212767614698292111585881)
              ·
                refine ⟨4659575711023719083689411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6212767614698292111585881 4659575711023719083689411)
                ·
                  refine ⟨6989363566535578625534117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659575711023719083689411 6989363566535578625534117)
                  ·
                    refine ⟨1310505668725420992287647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989363566535578625534117 1310505668725420992287647)
                    ·
                      rfl

theorem cell22_3828301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3828301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828301 prefixEnd_3828301 := by exact prefixLift 3828301
  have htrace : WordTrace (prefixWord ++ tailWord_3828301) baseStart_3828301 baseEnd_3828301 := by
    simpa [prefixWord, tailWord_3828301, baseEnd_3828301] using wordTrace_append hprefix tailTrace_3828301
  have hstable : (prefixWord ++ tailWord_3828301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828301).length < 2 ^ (prefixWord ++ tailWord_3828301).sum := by decide
  have hdescent : baseEnd_3828301 < baseStart_3828301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828376 : List Nat := [2, 1, 2, 4, 1, 1, 4, 3, 1, 3]
def baseStart_3828376 : Nat := 118140960795 + 3828376 * 2 ^ 59
def prefixEnd_3828376 : Nat := 4983230072969 + 3 ^ 40 * 3828376 * 2
def baseEnd_3828376 : Nat := 1310531342758145796662417

theorem tailTrace_3828376 : CollatzResearch.WordTrace tailWord_3828376 prefixEnd_3828376 1310531342758145796662417 := by
  unfold tailWord_3828376
  simp only [CollatzResearch.WordTrace]
  refine ⟨69816171989227530705740491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93088229318970040940987321 69816171989227530705740491)
  ·
    refine ⟨104724257983841296058610737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69816171989227530705740491 104724257983841296058610737)
    ·
      refine ⟨78543193487880972043958053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104724257983841296058610737 78543193487880972043958053)
      ·
        refine ⟨14726848778977682258242135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78543193487880972043958053 14726848778977682258242135)
        ·
          refine ⟨22090273168466523387363203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14726848778977682258242135 22090273168466523387363203)
          ·
            refine ⟨33135409752699785081044805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22090273168466523387363203 33135409752699785081044805)
            ·
              refine ⟨6212889328631209702695901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33135409752699785081044805 6212889328631209702695901)
              ·
                refine ⟨2329833498236703638510963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6212889328631209702695901 2329833498236703638510963)
                ·
                  refine ⟨3494750247355055457766445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329833498236703638510963 3494750247355055457766445)
                  ·
                    refine ⟨1310531342758145796662417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494750247355055457766445 1310531342758145796662417)
                    ·
                      rfl

theorem cell22_3828376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_3828376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828376 prefixEnd_3828376 := by exact prefixLift 3828376
  have htrace : WordTrace (prefixWord ++ tailWord_3828376) baseStart_3828376 baseEnd_3828376 := by
    simpa [prefixWord, tailWord_3828376, baseEnd_3828376] using wordTrace_append hprefix tailTrace_3828376
  have hstable : (prefixWord ++ tailWord_3828376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828376).length < 2 ^ (prefixWord ++ tailWord_3828376).sum := by decide
  have hdescent : baseEnd_3828376 < baseStart_3828376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828447 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 4, 4]
def baseStart_3828447 : Nat := 118140960795 + 3828447 * 2 ^ 59
def prefixEnd_3828447 : Nat := 4983230072969 + 3 ^ 40 * 3828447 * 2
def baseEnd_3828447 : Nat := 1310555647509125278137199

theorem tailTrace_3828447 : CollatzResearch.WordTrace tailWord_3828447 prefixEnd_3828447 1310555647509125278137199 := by
  unfold tailWord_3828447
  simp only [CollatzResearch.WordTrace]
  refine ⟨139634933561197840537315595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93089955707465227024877063 139634933561197840537315595)
  ·
    refine ⟨209452400341796760805973393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139634933561197840537315595 209452400341796760805973393)
    ·
      refine ⟨157089300256347570604480045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209452400341796760805973393 157089300256347570604480045)
      ·
        refine ⟨58908487596130338976680017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157089300256347570604480045 58908487596130338976680017)
        ·
          refine ⟨44181365697097754232510013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58908487596130338976680017 44181365697097754232510013)
          ·
            refine ⟨16568012136411657837191255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44181365697097754232510013 16568012136411657837191255)
            ·
              refine ⟨24852018204617486755786883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16568012136411657837191255 24852018204617486755786883)
              ·
                refine ⟨37278027306926230133680325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24852018204617486755786883 37278027306926230133680325)
                ·
                  refine ⟨6989630120048668150065061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37278027306926230133680325 6989630120048668150065061)
                  ·
                    refine ⟨1310555647509125278137199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989630120048668150065061 1310555647509125278137199)
                    ·
                      rfl

theorem cell22_3828447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_3828447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828447 prefixEnd_3828447 := by exact prefixLift 3828447
  have htrace : WordTrace (prefixWord ++ tailWord_3828447) baseStart_3828447 baseEnd_3828447 := by
    simpa [prefixWord, tailWord_3828447, baseEnd_3828447] using wordTrace_append hprefix tailTrace_3828447
  have hstable : (prefixWord ++ tailWord_3828447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828447).length < 2 ^ (prefixWord ++ tailWord_3828447).sum := by decide
  have hdescent : baseEnd_3828447 < baseStart_3828447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828449 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 4, 3]
def baseStart_3828449 : Nat := 118140960795 + 3828449 * 2 ^ 59
def prefixEnd_3828449 : Nat := 4983230072969 + 3 ^ 40 * 3828449 * 2
def baseEnd_3828449 : Nat := 1310556332149997939587193

theorem tailTrace_3828449 : CollatzResearch.WordTrace tailWord_3828449 prefixEnd_3828449 1310556332149997939587193 := by
  unfold tailWord_3828449
  simp only [CollatzResearch.WordTrace]
  refine ⟨139635006507190594878888401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93090004338127063252592267 139635006507190594878888401)
  ·
    refine ⟨104726254880392946159166301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139635006507190594878888401 104726254880392946159166301)
    ·
      refine ⟨39272345580147354809687363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104726254880392946159166301 39272345580147354809687363)
      ·
        refine ⟨58908518370221032214531045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39272345580147354809687363 58908518370221032214531045)
        ·
          refine ⟨11045347194416443540224571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58908518370221032214531045 11045347194416443540224571)
          ·
            refine ⟨16568020791624665310336857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11045347194416443540224571 16568020791624665310336857)
            ·
              refine ⟨12426015593718498982752643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16568020791624665310336857 12426015593718498982752643)
              ·
                refine ⟨18639023390577748474128965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12426015593718498982752643 18639023390577748474128965)
                ·
                  refine ⟨3494816885733327838899181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18639023390577748474128965 3494816885733327838899181)
                  ·
                    refine ⟨1310556332149997939587193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494816885733327838899181 1310556332149997939587193)
                    ·
                      rfl

theorem cell22_3828449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_3828449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828449 prefixEnd_3828449 := by exact prefixLift 3828449
  have htrace : WordTrace (prefixWord ++ tailWord_3828449) baseStart_3828449 baseEnd_3828449 := by
    simpa [prefixWord, tailWord_3828449, baseEnd_3828449] using wordTrace_append hprefix tailTrace_3828449
  have hstable : (prefixWord ++ tailWord_3828449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828449).length < 2 ^ (prefixWord ++ tailWord_3828449).sum := by decide
  have hdescent : baseEnd_3828449 < baseStart_3828449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828462 : List Nat := [4, 1, 2, 1, 1, 3, 1, 9]
def baseStart_3828462 : Nat := 118140960795 + 3828462 * 2 ^ 59
def prefixEnd_3828462 : Nat := 4983230072969 + 3 ^ 40 * 3828462 * 2
def baseEnd_3828462 : Nat := 145617864701741137668017

theorem tailTrace_3828462 : CollatzResearch.WordTrace tailWord_3828462 prefixEnd_3828462 145617864701741137668017 := by
  unfold tailWord_3828462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17454435082017937262388955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93090320437428998732741093 17454435082017937262388955)
  ·
    refine ⟨26181652623026905893583433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17454435082017937262388955 26181652623026905893583433)
    ·
      refine ⟨19636239467270179420187575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26181652623026905893583433 19636239467270179420187575)
      ·
        refine ⟨29454359200905269130281363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19636239467270179420187575 29454359200905269130281363)
        ·
          refine ⟨44181538801357903695422045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29454359200905269130281363 44181538801357903695422045)
          ·
            refine ⟨16568077050509213885783267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44181538801357903695422045 16568077050509213885783267)
            ·
              refine ⟨24852115575763820828674901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16568077050509213885783267 24852115575763820828674901)
              ·
                refine ⟨145617864701741137668017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24852115575763820828674901 145617864701741137668017)
                ·
                  rfl

theorem cell22_3828462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_3828462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828462 prefixEnd_3828462 := by exact prefixLift 3828462
  have htrace : WordTrace (prefixWord ++ tailWord_3828462) baseStart_3828462 baseEnd_3828462 := by
    simpa [prefixWord, tailWord_3828462, baseEnd_3828462] using wordTrace_append hprefix tailTrace_3828462
  have hstable : (prefixWord ++ tailWord_3828462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828462).length < 2 ^ (prefixWord ++ tailWord_3828462).sum := by decide
  have hdescent : baseEnd_3828462 < baseStart_3828462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828466 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_3828466 : Nat := 118140960795 + 3828466 * 2 ^ 59
def prefixEnd_3828466 : Nat := 4983230072969 + 3 ^ 40 * 3828466 * 2
def baseEnd_3828466 : Nat := 1310562151597415561912141

theorem tailTrace_3828466 : CollatzResearch.WordTrace tailWord_3828466 prefixEnd_3828466 1310562151597415561912141 := by
  unfold tailWord_3828466
  simp only [CollatzResearch.WordTrace]
  refine ⟨34908906637032251695564313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93090417698752671188171501 34908906637032251695564313)
  ·
    refine ⟨26181679977774188771673235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34908906637032251695564313 26181679977774188771673235)
    ·
      refine ⟨39272519966661283157509853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26181679977774188771673235 39272519966661283157509853)
      ·
        refine ⟨14727194987497981184066195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39272519966661283157509853 14727194987497981184066195)
        ·
          refine ⟨22090792481246971776099293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14727194987497981184066195 22090792481246971776099293)
          ·
            refine ⟨8284047180467614416037235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22090792481246971776099293 8284047180467614416037235)
            ·
              refine ⟨12426070770701421624055853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284047180467614416037235 12426070770701421624055853)
              ·
                refine ⟨4659776539013033109020945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12426070770701421624055853 4659776539013033109020945)
                ·
                  refine ⟨3494832404259774831765709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4659776539013033109020945 3494832404259774831765709)
                  ·
                    refine ⟨1310562151597415561912141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3494832404259774831765709 1310562151597415561912141)
                    ·
                      rfl

theorem cell22_3828466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_3828466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828466 prefixEnd_3828466 := by exact prefixLift 3828466
  have htrace : WordTrace (prefixWord ++ tailWord_3828466) baseStart_3828466 baseEnd_3828466 := by
    simpa [prefixWord, tailWord_3828466, baseEnd_3828466] using wordTrace_append hprefix tailTrace_3828466
  have hstable : (prefixWord ++ tailWord_3828466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828466).length < 2 ^ (prefixWord ++ tailWord_3828466).sum := by decide
  have hdescent : baseEnd_3828466 < baseStart_3828466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828552 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 8]
def baseStart_3828552 : Nat := 118140960795 + 3828552 * 2 ^ 59
def prefixEnd_3828552 : Nat := 4983230072969 + 3 ^ 40 * 3828552 * 2
def baseEnd_3828552 : Nat := 436863863718313334753959

theorem tailTrace_3828552 : CollatzResearch.WordTrace tailWord_3828552 prefixEnd_3828552 436863863718313334753959 := by
  unfold tailWord_3828552
  simp only [CollatzResearch.WordTrace]
  refine ⟨69819381612908721734943955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93092508817211628979925273 69819381612908721734943955)
  ·
    refine ⟨104729072419363082602415933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69819381612908721734943955 104729072419363082602415933)
    ·
      refine ⟨39273402157261155975905975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104729072419363082602415933 39273402157261155975905975)
      ·
        refine ⟨58910103235891733963858963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39273402157261155975905975 58910103235891733963858963)
        ·
          refine ⟨88365154853837600945788445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58910103235891733963858963 88365154853837600945788445)
          ·
            refine ⟨33136933070189100354670667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88365154853837600945788445 33136933070189100354670667)
            ·
              refine ⟨49705399605283650532006001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33136933070189100354670667 49705399605283650532006001)
              ·
                refine ⟨37279049703962737899004501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49705399605283650532006001 37279049703962737899004501)
                ·
                  refine ⟨436863863718313334753959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37279049703962737899004501 436863863718313334753959)
                  ·
                    rfl

theorem cell22_3828552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_3828552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828552 prefixEnd_3828552 := by exact prefixLift 3828552
  have htrace : WordTrace (prefixWord ++ tailWord_3828552) baseStart_3828552 baseEnd_3828552 := by
    simpa [prefixWord, tailWord_3828552, baseEnd_3828552] using wordTrace_append hprefix tailTrace_3828552
  have hstable : (prefixWord ++ tailWord_3828552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828552).length < 2 ^ (prefixWord ++ tailWord_3828552).sum := by decide
  have hdescent : baseEnd_3828552 < baseStart_3828552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828569 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 6]
def baseStart_3828569 : Nat := 118140960795 + 3828569 * 2 ^ 59
def prefixEnd_3828569 : Nat := 4983230072969 + 3 ^ 40 * 3828569 * 2
def baseEnd_3828569 : Nat := 436865803534119208862275

theorem tailTrace_3828569 : CollatzResearch.WordTrace tailWord_3828569 prefixEnd_3828569 436865803534119208862275 := by
  unfold tailWord_3828569
  simp only [CollatzResearch.WordTrace]
  refine ⟨139639383266755855373256761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93092922177837236915504507 139639383266755855373256761)
  ·
    refine ⟨104729537450066891529942571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139639383266755855373256761 104729537450066891529942571)
    ·
      refine ⟨157094306175100337294913857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104729537450066891529942571 157094306175100337294913857)
      ·
        refine ⟨117820729631325252971185393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157094306175100337294913857 117820729631325252971185393)
        ·
          refine ⟨88365547223493939728389045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117820729631325252971185393 88365547223493939728389045)
          ·
            refine ⟨8284270052202556849536473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88365547223493939728389045 8284270052202556849536473)
            ·
              refine ⟨6213202539151917637152355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8284270052202556849536473 6213202539151917637152355)
              ·
                refine ⟨9319803808727876455728533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213202539151917637152355 9319803808727876455728533)
                ·
                  refine ⟨436865803534119208862275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9319803808727876455728533 436865803534119208862275)
                  ·
                    rfl

theorem cell22_3828569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_3828569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828569 prefixEnd_3828569 := by exact prefixLift 3828569
  have htrace : WordTrace (prefixWord ++ tailWord_3828569) baseStart_3828569 baseEnd_3828569 := by
    simpa [prefixWord, tailWord_3828569, baseEnd_3828569] using wordTrace_append hprefix tailTrace_3828569
  have hstable : (prefixWord ++ tailWord_3828569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828569).length < 2 ^ (prefixWord ++ tailWord_3828569).sum := by decide
  have hdescent : baseEnd_3828569 < baseStart_3828569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828616 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_3828616 : Nat := 118140960795 + 3828616 * 2 ^ 59
def prefixEnd_3828616 : Nat := 4983230072969 + 3 ^ 40 * 3828616 * 2
def baseEnd_3828616 : Nat := 1310613499662865170661681

theorem tailTrace_3828616 : CollatzResearch.WordTrace tailWord_3828616 prefixEnd_3828616 1310613499662865170661681 := by
  unfold tailWord_3828616
  simp only [CollatzResearch.WordTrace]
  refine ⟨69820548748792791200108851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93094064998390388266811801 69820548748792791200108851)
  ·
    refine ⟨104730823123189186800163277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69820548748792791200108851 104730823123189186800163277)
    ·
      refine ⟨39274058671195945050061229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104730823123189186800163277 39274058671195945050061229)
      ·
        refine ⟨14727772001698479393772961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39274058671195945050061229 14727772001698479393772961)
        ·
          refine ⟨11045829001273859545329721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14727772001698479393772961 11045829001273859545329721)
          ·
            refine ⟨8284371750955394658997291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11045829001273859545329721 8284371750955394658997291)
            ·
              refine ⟨12426557626433091988495937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284371750955394658997291 12426557626433091988495937)
              ·
                refine ⟨9319918219824818991371953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12426557626433091988495937 9319918219824818991371953)
                ·
                  refine ⟨6989938664868614243528965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9319918219824818991371953 6989938664868614243528965)
                  ·
                    refine ⟨1310613499662865170661681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6989938664868614243528965 1310613499662865170661681)
                    ·
                      rfl

theorem cell22_3828616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_3828616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828616 prefixEnd_3828616 := by exact prefixLift 3828616
  have htrace : WordTrace (prefixWord ++ tailWord_3828616) baseStart_3828616 baseEnd_3828616 := by
    simpa [prefixWord, tailWord_3828616, baseEnd_3828616] using wordTrace_append hprefix tailTrace_3828616
  have hstable : (prefixWord ++ tailWord_3828616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828616).length < 2 ^ (prefixWord ++ tailWord_3828616).sum := by decide
  have hdescent : baseEnd_3828616 < baseStart_3828616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828680 : List Nat := [2, 1, 3, 1, 5, 1, 1, 4, 1, 3]
def baseStart_3828680 : Nat := 118140960795 + 3828680 * 2 ^ 59
def prefixEnd_3828680 : Nat := 4983230072969 + 3 ^ 40 * 3828680 * 2
def baseEnd_3828680 : Nat := 1310635408170790337061485

theorem tailTrace_3828680 : CollatzResearch.WordTrace tailWord_3828680 prefixEnd_3828680 1310635408170790337061485 := by
  unfold tailWord_3828680
  simp only [CollatzResearch.WordTrace]
  refine ⟨69821715884676860665273747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93095621179569147553698329 69821715884676860665273747)
  ·
    refine ⟨104732573827015290997910621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69821715884676860665273747 104732573827015290997910621)
    ·
      refine ⟨39274715185130734124216483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104732573827015290997910621 39274715185130734124216483)
      ·
        refine ⟨58912072777696101186324725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39274715185130734124216483 58912072777696101186324725)
        ·
          refine ⟨5523006822909009486217943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58912072777696101186324725 5523006822909009486217943)
          ·
            refine ⟨8284510234363514229326915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523006822909009486217943 8284510234363514229326915)
            ·
              refine ⟨12426765351545271343990373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8284510234363514229326915 12426765351545271343990373)
              ·
                refine ⟨2330018503414738376998195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12426765351545271343990373 2330018503414738376998195)
                ·
                  refine ⟨3495027755122107565497293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330018503414738376998195 3495027755122107565497293)
                  ·
                    refine ⟨1310635408170790337061485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3495027755122107565497293 1310635408170790337061485)
                    ·
                      rfl

theorem cell22_3828680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_3828680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828680 prefixEnd_3828680 := by exact prefixLift 3828680
  have htrace : WordTrace (prefixWord ++ tailWord_3828680) baseStart_3828680 baseEnd_3828680 := by
    simpa [prefixWord, tailWord_3828680, baseEnd_3828680] using wordTrace_append hprefix tailTrace_3828680
  have hstable : (prefixWord ++ tailWord_3828680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828680).length < 2 ^ (prefixWord ++ tailWord_3828680).sum := by decide
  have hdescent : baseEnd_3828680 < baseStart_3828680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828689 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_3828689 : Nat := 118140960795 + 3828689 * 2 ^ 59
def prefixEnd_3828689 : Nat := 4983230072969 + 3 ^ 40 * 3828689 * 2
def baseEnd_3828689 : Nat := 1310638489054717313586457

theorem tailTrace_3828689 : CollatzResearch.WordTrace tailWord_3828689 prefixEnd_3828689 1310638489054717313586457 := by
  unfold tailWord_3828689
  simp only [CollatzResearch.WordTrace]
  refine ⟨139643760026321115867625121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93095840017547410578416747 139643760026321115867625121)
  ·
    refine ⟨104732820019740836900718841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139643760026321115867625121 104732820019740836900718841)
    ·
      refine ⟨78549615014805627675539131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104732820019740836900718841 78549615014805627675539131)
      ·
        refine ⟨117824422522208441513308697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78549615014805627675539131 117824422522208441513308697)
        ·
          refine ⟨88368316891656331134981523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117824422522208441513308697 88368316891656331134981523)
          ·
            refine ⟨132552475337484496702472285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88368316891656331134981523 132552475337484496702472285)
            ·
              refine ⟨49707178251556686263427107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132552475337484496702472285 49707178251556686263427107)
              ·
                refine ⟨74560767377335029395140661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49707178251556686263427107 74560767377335029395140661)
                ·
                  refine ⟨6990071941625159005794437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74560767377335029395140661 6990071941625159005794437)
                  ·
                    refine ⟨1310638489054717313586457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990071941625159005794437 1310638489054717313586457)
                    ·
                      rfl

theorem cell22_3828689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_3828689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828689 prefixEnd_3828689 := by exact prefixLift 3828689
  have htrace : WordTrace (prefixWord ++ tailWord_3828689) baseStart_3828689 baseEnd_3828689 := by
    simpa [prefixWord, tailWord_3828689, baseEnd_3828689] using wordTrace_append hprefix tailTrace_3828689
  have hstable : (prefixWord ++ tailWord_3828689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828689).length < 2 ^ (prefixWord ++ tailWord_3828689).sum := by decide
  have hdescent : baseEnd_3828689 < baseStart_3828689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828888 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_3828888 : Nat := 118140960795 + 3828888 * 2 ^ 59
def prefixEnd_3828888 : Nat := 4983230072969 + 3 ^ 40 * 3828888 * 2
def baseEnd_3828888 : Nat := 1310706610821547127860847

theorem tailTrace_3828888 : CollatzResearch.WordTrace tailWord_3828888 prefixEnd_3828888 1310706610821547127860847 := by
  unfold tailWord_3828888
  simp only [CollatzResearch.WordTrace]
  refine ⟨69825509076300086427059659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93100678768400115236079545 69825509076300086427059659)
  ·
    refine ⟨104738263614450129640589489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69825509076300086427059659 104738263614450129640589489)
    ·
      refine ⟨78553697710837597230442117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104738263614450129640589489 78553697710837597230442117)
      ·
        refine ⟨14728818320782049480707897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78553697710837597230442117 14728818320782049480707897)
        ·
          refine ⟨11046613740586537110530923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14728818320782049480707897 11046613740586537110530923)
          ·
            refine ⟨16569920610879805665796385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11046613740586537110530923 16569920610879805665796385)
            ·
              refine ⟨12427440458159854249347289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16569920610879805665796385 12427440458159854249347289)
              ·
                refine ⟨9320580343619890687010467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12427440458159854249347289 9320580343619890687010467)
                ·
                  refine ⟨13980870515429836030515701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9320580343619890687010467 13980870515429836030515701)
                  ·
                    refine ⟨1310706610821547127860847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13980870515429836030515701 1310706610821547127860847)
                    ·
                      rfl

theorem cell22_3828888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_3828888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828888 prefixEnd_3828888 := by exact prefixLift 3828888
  have htrace : WordTrace (prefixWord ++ tailWord_3828888) baseStart_3828888 baseEnd_3828888 := by
    simpa [prefixWord, tailWord_3828888, baseEnd_3828888] using wordTrace_append hprefix tailTrace_3828888
  have hstable : (prefixWord ++ tailWord_3828888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828888).length < 2 ^ (prefixWord ++ tailWord_3828888).sum := by decide
  have hdescent : baseEnd_3828888 < baseStart_3828888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828890 : List Nat := [3, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_3828890 : Nat := 118140960795 + 3828890 * 2 ^ 59
def prefixEnd_3828890 : Nat := 4983230072969 + 3 ^ 40 * 3828890 * 2
def baseEnd_3828890 : Nat := 436902431820806596436947

theorem tailTrace_3828890 : CollatzResearch.WordTrace tailWord_3828890 prefixEnd_3828890 436902431820806596436947 := by
  unfold tailWord_3828890
  simp only [CollatzResearch.WordTrace]
  refine ⟨34912772774648231798923031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93100727399061951463794749 34912772774648231798923031)
  ·
    refine ⟨52369159161972347698384547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34912772774648231798923031 52369159161972347698384547)
    ·
      refine ⟨78553738742958521547576821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52369159161972347698384547 78553738742958521547576821)
      ·
        refine ⟨7364413007152361395085327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78553738742958521547576821 7364413007152361395085327)
        ·
          refine ⟨11046619510728542092627991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7364413007152361395085327 11046619510728542092627991)
          ·
            refine ⟨16569929266092813138941987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11046619510728542092627991 16569929266092813138941987)
            ·
              refine ⟨24854893899139219708412981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16569929266092813138941987 24854893899139219708412981)
              ·
                refine ⟨2330146303044301847663717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24854893899139219708412981 2330146303044301847663717)
                ·
                  refine ⟨436902431820806596436947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330146303044301847663717 436902431820806596436947)
                  ·
                    rfl

theorem cell22_3828890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_3828890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828890 prefixEnd_3828890 := by exact prefixLift 3828890
  have htrace : WordTrace (prefixWord ++ tailWord_3828890) baseStart_3828890 baseEnd_3828890 := by
    simpa [prefixWord, tailWord_3828890, baseEnd_3828890] using wordTrace_append hprefix tailTrace_3828890
  have hstable : (prefixWord ++ tailWord_3828890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828890).length < 2 ^ (prefixWord ++ tailWord_3828890).sum := by decide
  have hdescent : baseEnd_3828890 < baseStart_3828890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828892 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_3828892 : Nat := 118140960795 + 3828892 * 2 ^ 59
def prefixEnd_3828892 : Nat := 4983230072969 + 3 ^ 40 * 3828892 * 2
def baseEnd_3828892 : Nat := 1310707980103292450760835

theorem tailTrace_3828892 : CollatzResearch.WordTrace tailWord_3828892 prefixEnd_3828892 1310707980103292450760835 := by
  unfold tailWord_3828892
  simp only [CollatzResearch.WordTrace]
  refine ⟨69825582022292840768632465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93100776029723787691509953 69825582022292840768632465)
  ·
    refine ⟨52369186516719630576474349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69825582022292840768632465 52369186516719630576474349)
    ·
      refine ⟨19638444943769861466177881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52369186516719630576474349 19638444943769861466177881)
      ·
        refine ⟨14728833707827396099633411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19638444943769861466177881 14728833707827396099633411)
        ·
          refine ⟨22093250561741094149450117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14728833707827396099633411 22093250561741094149450117)
          ·
            refine ⟨4142484480326455153021897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22093250561741094149450117 4142484480326455153021897)
            ·
              refine ⟨3106863360244841364766423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142484480326455153021897 3106863360244841364766423)
              ·
                refine ⟨4660295040367262047149635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106863360244841364766423 4660295040367262047149635)
                ·
                  refine ⟨6990442560550893070724453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660295040367262047149635 6990442560550893070724453)
                  ·
                    refine ⟨1310707980103292450760835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990442560550893070724453 1310707980103292450760835)
                    ·
                      rfl

theorem cell22_3828892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_3828892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828892 prefixEnd_3828892 := by exact prefixLift 3828892
  have htrace : WordTrace (prefixWord ++ tailWord_3828892) baseStart_3828892 baseEnd_3828892 := by
    simpa [prefixWord, tailWord_3828892, baseEnd_3828892] using wordTrace_append hprefix tailTrace_3828892
  have hstable : (prefixWord ++ tailWord_3828892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828892).length < 2 ^ (prefixWord ++ tailWord_3828892).sum := by decide
  have hdescent : baseEnd_3828892 < baseStart_3828892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828901 : List Nat := [1, 3, 1, 2, 1, 5, 9]
def baseStart_3828901 : Nat := 118140960795 + 3828901 * 2 ^ 59
def prefixEnd_3828901 : Nat := 4983230072969 + 3 ^ 40 * 3828901 * 2
def baseEnd_3828901 : Nat := 48544854110637756566141

theorem tailTrace_3828901 : CollatzResearch.WordTrace tailWord_3828901 prefixEnd_3828901 48544854110637756566141 := by
  unfold tailWord_3828901
  simp only [CollatzResearch.WordTrace]
  refine ⟨139651492301553076074342557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93100994867702050716228371 139651492301553076074342557)
  ·
    refine ⟨52369309613082403527878459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139651492301553076074342557 52369309613082403527878459)
    ·
      refine ⟨78553964419623605291817689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52369309613082403527878459 78553964419623605291817689)
      ·
        refine ⟨58915473314717703968863267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78553964419623605291817689 58915473314717703968863267)
        ·
          refine ⟨88373209972076555953294901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58915473314717703968863267 88373209972076555953294901)
          ·
            refine ⟨8284988434882177120621397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88373209972076555953294901 8284988434882177120621397)
            ·
              refine ⟨48544854110637756566141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8284988434882177120621397 48544854110637756566141)
              ·
                rfl

theorem cell22_3828901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 9].length) (baseStart_3828901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828901 prefixEnd_3828901 := by exact prefixLift 3828901
  have htrace : WordTrace (prefixWord ++ tailWord_3828901) baseStart_3828901 baseEnd_3828901 := by
    simpa [prefixWord, tailWord_3828901, baseEnd_3828901] using wordTrace_append hprefix tailTrace_3828901
  have hstable : (prefixWord ++ tailWord_3828901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828901).length < 2 ^ (prefixWord ++ tailWord_3828901).sum := by decide
  have hdescent : baseEnd_3828901 < baseStart_3828901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828941 : List Nat := [1, 6, 2, 2, 1, 2, 1, 3, 4]
def baseStart_3828941 : Nat := 118140960795 + 3828941 * 2 ^ 59
def prefixEnd_3828941 : Nat := 4983230072969 + 3 ^ 40 * 3828941 * 2
def baseEnd_3828941 : Nat := 436908251268224218761895

theorem tailTrace_3828941 : CollatzResearch.WordTrace tailWord_3828941 prefixEnd_3828941 436908251268224218761895 := by
  unfold tailWord_3828941
  simp only [CollatzResearch.WordTrace]
  refine ⟨139652951221408162905798677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93101967480938775270532451 139652951221408162905798677)
  ·
    refine ⟨6546232088503507636209313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139652951221408162905798677 6546232088503507636209313)
    ·
      refine ⟨4909674066377630727156985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6546232088503507636209313 4909674066377630727156985)
      ·
        refine ⟨3682255549783223045367739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4909674066377630727156985 3682255549783223045367739)
        ·
          refine ⟨5523383324674834568051609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682255549783223045367739 5523383324674834568051609)
          ·
            refine ⟨4142537493506125926038707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5523383324674834568051609 4142537493506125926038707)
            ·
              refine ⟨6213806240259188889058061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142537493506125926038707 6213806240259188889058061)
              ·
                refine ⟨2330177340097195833396773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6213806240259188889058061 2330177340097195833396773)
                ·
                  refine ⟨436908251268224218761895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330177340097195833396773 436908251268224218761895)
                  ·
                    rfl

theorem cell22_3828941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_3828941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828941 prefixEnd_3828941 := by exact prefixLift 3828941
  have htrace : WordTrace (prefixWord ++ tailWord_3828941) baseStart_3828941 baseEnd_3828941 := by
    simpa [prefixWord, tailWord_3828941, baseEnd_3828941] using wordTrace_append hprefix tailTrace_3828941
  have hstable : (prefixWord ++ tailWord_3828941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828941).length < 2 ^ (prefixWord ++ tailWord_3828941).sum := by decide
  have hdescent : baseEnd_3828941 < baseStart_3828941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3828976 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_3828976 : Nat := 118140960795 + 3828976 * 2 ^ 59
def prefixEnd_3828976 : Nat := 4983230072969 + 3 ^ 40 * 3828976 * 2
def baseEnd_3828976 : Nat := 1310736735019944231660577

theorem tailTrace_3828976 : CollatzResearch.WordTrace tailWord_3828976 prefixEnd_3828976 1310736735019944231660577 := by
  unfold tailWord_3828976
  simp only [CollatzResearch.WordTrace]
  refine ⟨69827113888140681941661391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93102818517520909255548521 69827113888140681941661391)
  ·
    refine ⟨104740670832211022912492087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69827113888140681941661391 104740670832211022912492087)
    ·
      refine ⟨157111006248316534368738131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104740670832211022912492087 157111006248316534368738131)
      ·
        refine ⟨235666509372474801553107197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157111006248316534368738131 235666509372474801553107197)
        ·
          refine ⟨88374941014678050582415199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235666509372474801553107197 88374941014678050582415199)
          ·
            refine ⟨132562411522017075873622799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88374941014678050582415199 132562411522017075873622799)
            ·
              refine ⟨198843617283025613810434199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132562411522017075873622799 198843617283025613810434199)
              ·
                refine ⟨298265425924538420715651299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198843617283025613810434199 298265425924538420715651299)
                ·
                  refine ⟨447398138886807631073476949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 298265425924538420715651299 447398138886807631073476949)
                  ·
                    refine ⟨1310736735019944231660577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 447398138886807631073476949 1310736735019944231660577)
                    ·
                      rfl

theorem cell22_3828976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_3828976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3828976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3828976 prefixEnd_3828976 := by exact prefixLift 3828976
  have htrace : WordTrace (prefixWord ++ tailWord_3828976) baseStart_3828976 baseEnd_3828976 := by
    simpa [prefixWord, tailWord_3828976, baseEnd_3828976] using wordTrace_append hprefix tailTrace_3828976
  have hstable : (prefixWord ++ tailWord_3828976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3828976).length < 2 ^ (prefixWord ++ tailWord_3828976).sum := by decide
  have hdescent : baseEnd_3828976 < baseStart_3828976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3828976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829040 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 2, 3]
def baseStart_3829040 : Nat := 118140960795 + 3829040 * 2 ^ 59
def prefixEnd_3829040 : Nat := 4983230072969 + 3 ^ 40 * 3829040 * 2
def baseEnd_3829040 : Nat := 1310758643527869398060381

theorem tailTrace_3829040 : CollatzResearch.WordTrace tailWord_3829040 prefixEnd_3829040 1310758643527869398060381 := by
  unfold tailWord_3829040
  simp only [CollatzResearch.WordTrace]
  refine ⟨69828281024024751406826287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93104374698699668542435049 69828281024024751406826287)
  ·
    refine ⟨104742421536037127110239431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69828281024024751406826287 104742421536037127110239431)
    ·
      refine ⟨157113632304055690665359147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104742421536037127110239431 157113632304055690665359147)
      ·
        refine ⟨235670448456083535998038721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157113632304055690665359147 235670448456083535998038721)
        ·
          refine ⟨176752836342062651998529041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235670448456083535998038721 176752836342062651998529041)
          ·
            refine ⟨132564627256546988998896781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176752836342062651998529041 132564627256546988998896781)
            ·
              refine ⟨49711735221205120874586293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132564627256546988998896781 49711735221205120874586293)
              ·
                refine ⟨4660475176987980081992465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49711735221205120874586293 4660475176987980081992465)
                ·
                  refine ⟨3495356382740985061494349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4660475176987980081992465 3495356382740985061494349)
                  ·
                    refine ⟨1310758643527869398060381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3495356382740985061494349 1310758643527869398060381)
                    ·
                      rfl

theorem cell22_3829040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_3829040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829040 prefixEnd_3829040 := by exact prefixLift 3829040
  have htrace : WordTrace (prefixWord ++ tailWord_3829040) baseStart_3829040 baseEnd_3829040 := by
    simpa [prefixWord, tailWord_3829040, baseEnd_3829040] using wordTrace_append hprefix tailTrace_3829040
  have hstable : (prefixWord ++ tailWord_3829040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829040).length < 2 ^ (prefixWord ++ tailWord_3829040).sum := by decide
  have hdescent : baseEnd_3829040 < baseStart_3829040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829055 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 2, 4]
def baseStart_3829055 : Nat := 118140960795 + 3829055 * 2 ^ 59
def prefixEnd_3829055 : Nat := 4983230072969 + 3 ^ 40 * 3829055 * 2
def baseEnd_3829055 : Nat := 1310763778334414358935335

theorem tailTrace_3829055 : CollatzResearch.WordTrace tailWord_3829055 prefixEnd_3829055 1310763778334414358935335 := by
  unfold tailWord_3829055
  simp only [CollatzResearch.WordTrace]
  refine ⟨139657109142995160375448619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93104739428663440250299079 139657109142995160375448619)
  ·
    refine ⟨209485663714492740563172929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139657109142995160375448619 209485663714492740563172929)
    ·
      refine ⟨157114247785869555422379697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209485663714492740563172929 157114247785869555422379697)
      ·
        refine ⟨117835685839402166566784773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157114247785869555422379697 117835685839402166566784773)
        ·
          refine ⟨22094191094887906231272145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117835685839402166566784773 22094191094887906231272145)
          ·
            refine ⟨16570643321165929673454109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22094191094887906231272145 16570643321165929673454109)
            ·
              refine ⟨6213991245437223627545291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16570643321165929673454109 6213991245437223627545291)
              ·
                refine ⟨9320986868155835441317937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213991245437223627545291 9320986868155835441317937)
                ·
                  refine ⟨6990740151116876580988453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9320986868155835441317937 6990740151116876580988453)
                  ·
                    refine ⟨1310763778334414358935335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6990740151116876580988453 1310763778334414358935335)
                    ·
                      rfl

theorem cell22_3829055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_3829055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829055 prefixEnd_3829055 := by exact prefixLift 3829055
  have htrace : WordTrace (prefixWord ++ tailWord_3829055) baseStart_3829055 baseEnd_3829055 := by
    simpa [prefixWord, tailWord_3829055, baseEnd_3829055] using wordTrace_append hprefix tailTrace_3829055
  have hstable : (prefixWord ++ tailWord_3829055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829055).length < 2 ^ (prefixWord ++ tailWord_3829055).sum := by decide
  have hdescent : baseEnd_3829055 < baseStart_3829055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829113 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_3829113 : Nat := 118140960795 + 3829113 * 2 ^ 59
def prefixEnd_3829113 : Nat := 4983230072969 + 3 ^ 40 * 3829113 * 2
def baseEnd_3829113 : Nat := 1310783632919721540985157

theorem tailTrace_3829113 : CollatzResearch.WordTrace tailWord_3829113 prefixEnd_3829113 1310783632919721540985157 := by
  unfold tailWord_3829113
  simp only [CollatzResearch.WordTrace]
  refine ⟨139659224576785036281059993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93106149717856690854039995 139659224576785036281059993)
  ·
    refine ⟨104744418432588777210794995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139659224576785036281059993 104744418432588777210794995)
    ·
      refine ⟨157116627648883165816192493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104744418432588777210794995 157116627648883165816192493)
      ·
        refine ⟨58918735368331187181072185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157116627648883165816192493 58918735368331187181072185)
        ·
          refine ⟨44189051526248390385804139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58918735368331187181072185 44189051526248390385804139)
          ·
            refine ⟨66283577289372585578706209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44189051526248390385804139 66283577289372585578706209)
            ·
              refine ⟨49712682967029439184029657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66283577289372585578706209 49712682967029439184029657)
              ·
                refine ⟨37284512225272079388022243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49712682967029439184029657 37284512225272079388022243)
                ·
                  refine ⟨55926768337908119082033365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37284512225272079388022243 55926768337908119082033365)
                  ·
                    refine ⟨1310783632919721540985157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55926768337908119082033365 1310783632919721540985157)
                    ·
                      rfl

theorem cell22_3829113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_3829113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829113 prefixEnd_3829113 := by exact prefixLift 3829113
  have htrace : WordTrace (prefixWord ++ tailWord_3829113) baseStart_3829113 baseEnd_3829113 := by
    simpa [prefixWord, tailWord_3829113, baseEnd_3829113] using wordTrace_append hprefix tailTrace_3829113
  have hstable : (prefixWord ++ tailWord_3829113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829113).length < 2 ^ (prefixWord ++ tailWord_3829113).sum := by decide
  have hdescent : baseEnd_3829113 < baseStart_3829113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829149 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 5]
def baseStart_3829149 : Nat := 118140960795 + 3829149 * 2 ^ 59
def prefixEnd_3829149 : Nat := 4983230072969 + 3 ^ 40 * 3829149 * 2
def baseEnd_3829149 : Nat := 436931985485143149028349

theorem tailTrace_3829149 : CollatzResearch.WordTrace tailWord_3829149 prefixEnd_3829149 436931985485143149028349 := by
  unfold tailWord_3829149
  simp only [CollatzResearch.WordTrace]
  refine ⟨139660537604654614429370501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93107025069769742952913667 139660537604654614429370501)
  ·
    refine ⟨26186350800872740205506969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139660537604654614429370501 26186350800872740205506969)
    ·
      refine ⟨19639763100654555154130227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26186350800872740205506969 19639763100654555154130227)
      ·
        refine ⟨29459644650981832731195341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19639763100654555154130227 29459644650981832731195341)
        ·
          refine ⟨11047366744118187274198253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29459644650981832731195341 11047366744118187274198253)
          ·
            refine ⟨4142762529044320227824345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11047366744118187274198253 4142762529044320227824345)
            ·
              refine ⟨3107071896783240170868259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142762529044320227824345 3107071896783240170868259)
              ·
                refine ⟨4660607845174860256302389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107071896783240170868259 4660607845174860256302389)
                ·
                  refine ⟨436931985485143149028349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4660607845174860256302389 436931985485143149028349)
                  ·
                    rfl

theorem cell22_3829149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_3829149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829149 prefixEnd_3829149 := by exact prefixLift 3829149
  have htrace : WordTrace (prefixWord ++ tailWord_3829149) baseStart_3829149 baseEnd_3829149 := by
    simpa [prefixWord, tailWord_3829149, baseEnd_3829149] using wordTrace_append hprefix tailTrace_3829149
  have hstable : (prefixWord ++ tailWord_3829149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829149).length < 2 ^ (prefixWord ++ tailWord_3829149).sum := by decide
  have hdescent : baseEnd_3829149 < baseStart_3829149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829175 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 1, 5]
def baseStart_3829175 : Nat := 118140960795 + 3829175 * 2 ^ 59
def prefixEnd_3829175 : Nat := 4983230072969 + 3 ^ 40 * 3829175 * 2
def baseEnd_3829175 : Nat := 1310804856786774045934967

theorem tailTrace_3829175 : CollatzResearch.WordTrace tailWord_3829175 prefixEnd_3829175 1310804856786774045934967 := by
  unfold tailWord_3829175
  simp only [CollatzResearch.WordTrace]
  refine ⟨139661485902560420869816979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93107657268373613913211319 139661485902560420869816979)
  ·
    refine ⟨209492228853840631304725469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139661485902560420869816979 209492228853840631304725469)
    ·
      refine ⟨78559585820190236739272051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209492228853840631304725469 78559585820190236739272051)
      ·
        refine ⟨117839378730285355108908077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78559585820190236739272051 117839378730285355108908077)
        ·
          refine ⟨44189767023857008165840529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117839378730285355108908077 44189767023857008165840529)
          ·
            refine ⟨33142325267892756124380397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44189767023857008165840529 33142325267892756124380397)
            ·
              refine ⟨12428371975459783546642649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33142325267892756124380397 12428371975459783546642649)
              ·
                refine ⟨9321278981594837659981987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12428371975459783546642649 9321278981594837659981987)
                ·
                  refine ⟨13981918472392256489972981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9321278981594837659981987 13981918472392256489972981)
                  ·
                    refine ⟨1310804856786774045934967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13981918472392256489972981 1310804856786774045934967)
                    ·
                      rfl

theorem cell22_3829175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_3829175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829175 prefixEnd_3829175 := by exact prefixLift 3829175
  have htrace : WordTrace (prefixWord ++ tailWord_3829175) baseStart_3829175 baseEnd_3829175 := by
    simpa [prefixWord, tailWord_3829175, baseEnd_3829175] using wordTrace_append hprefix tailTrace_3829175
  have hstable : (prefixWord ++ tailWord_3829175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829175).length < 2 ^ (prefixWord ++ tailWord_3829175).sum := by decide
  have hdescent : baseEnd_3829175 < baseStart_3829175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829194 : List Nat := [3, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_3829194 : Nat := 118140960795 + 3829194 * 2 ^ 59
def prefixEnd_3829194 : Nat := 4983230072969 + 3 ^ 40 * 3829194 * 2
def baseEnd_3829194 : Nat := 436937120291688109903303

theorem tailTrace_3829194 : CollatzResearch.WordTrace tailWord_3829194 prefixEnd_3829194 436937120291688109903303 := by
  unfold tailWord_3829194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34915544722372896778689659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93108119259661058076505757 34915544722372896778689659)
  ·
    refine ⟨52373317083559345168034489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34915544722372896778689659 52373317083559345168034489)
    ·
      refine ⟨39279987812669508876025867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52373317083559345168034489 39279987812669508876025867)
      ·
        refine ⟨58919981719004263314038801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39279987812669508876025867 58919981719004263314038801)
        ·
          refine ⟨44189986289253197485529101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58919981719004263314038801 44189986289253197485529101)
          ·
            refine ⟨16571244858469949057073413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44189986289253197485529101 16571244858469949057073413)
            ·
              refine ⟨3107108410963115448201265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16571244858469949057073413 3107108410963115448201265)
              ·
                refine ⟨2330331308222336586150949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3107108410963115448201265 2330331308222336586150949)
                ·
                  refine ⟨436937120291688109903303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330331308222336586150949 436937120291688109903303)
                  ·
                    rfl

theorem cell22_3829194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_3829194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829194 prefixEnd_3829194 := by exact prefixLift 3829194
  have htrace : WordTrace (prefixWord ++ tailWord_3829194) baseStart_3829194 baseEnd_3829194 := by
    simpa [prefixWord, tailWord_3829194, baseEnd_3829194] using wordTrace_append hprefix tailTrace_3829194
  have hstable : (prefixWord ++ tailWord_3829194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829194).length < 2 ^ (prefixWord ++ tailWord_3829194).sum := by decide
  have hdescent : baseEnd_3829194 < baseStart_3829194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829265 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_3829265 : Nat := 118140960795 + 3829265 * 2 ^ 59
def prefixEnd_3829265 : Nat := 4983230072969 + 3 ^ 40 * 3829265 * 2
def baseEnd_3829265 : Nat := 1310835665626043811184691

theorem tailTrace_3829265 : CollatzResearch.WordTrace tailWord_3829265 prefixEnd_3829265 1310835665626043811184691 := by
  unfold tailWord_3829265
  simp only [CollatzResearch.WordTrace]
  refine ⟨139664768472234366240593249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93109845648156244160395499 139664768472234366240593249)
  ·
    refine ⟨104748576354175774680444937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139664768472234366240593249 104748576354175774680444937)
    ·
      refine ⟨78561432265631831010333703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104748576354175774680444937 78561432265631831010333703)
      ·
        refine ⟨117842148398447746515500555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78561432265631831010333703 117842148398447746515500555)
        ·
          refine ⟨176763222597671619773250833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117842148398447746515500555 176763222597671619773250833)
          ·
            refine ⟨132572416948253714829938125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176763222597671619773250833 132572416948253714829938125)
            ·
              refine ⟨49714656355595143061226797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132572416948253714829938125 49714656355595143061226797)
              ·
                refine ⟨18642996133348178647960049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49714656355595143061226797 18642996133348178647960049)
                ·
                  refine ⟨13982247100011133985970037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18642996133348178647960049 13982247100011133985970037)
                  ·
                    refine ⟨1310835665626043811184691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13982247100011133985970037 1310835665626043811184691)
                    ·
                      rfl

theorem cell22_3829265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_3829265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829265 prefixEnd_3829265 := by exact prefixLift 3829265
  have htrace : WordTrace (prefixWord ++ tailWord_3829265) baseStart_3829265 baseEnd_3829265 := by
    simpa [prefixWord, tailWord_3829265, baseEnd_3829265] using wordTrace_append hprefix tailTrace_3829265
  have hstable : (prefixWord ++ tailWord_3829265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829265).length < 2 ^ (prefixWord ++ tailWord_3829265).sum := by decide
  have hdescent : baseEnd_3829265 < baseStart_3829265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829355 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 4, 7]
def baseStart_3829355 : Nat := 118140960795 + 3829355 * 2 ^ 59
def prefixEnd_3829355 : Nat := 4983230072969 + 3 ^ 40 * 3829355 * 2
def baseEnd_3829355 : Nat := 1310866474465313576434415

theorem tailTrace_3829355 : CollatzResearch.WordTrace tailWord_3829355 prefixEnd_3829355 1310866474465313576434415 := by
  unfold tailWord_3829355
  simp only [CollatzResearch.WordTrace]
  refine ⟨139668051041908311611369519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93112034027938874407579679 139668051041908311611369519)
  ·
    refine ⟨209502076562862467417054279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139668051041908311611369519 209502076562862467417054279)
    ·
      refine ⟨314253114844293701125581419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209502076562862467417054279 314253114844293701125581419)
      ·
        refine ⟨471379672266440551688372129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314253114844293701125581419 471379672266440551688372129)
        ·
          refine ⟨353534754199830413766279097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471379672266440551688372129 353534754199830413766279097)
          ·
            refine ⟨265151065649872810324709323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353534754199830413766279097 265151065649872810324709323)
            ·
              refine ⟨397726598474809215487063985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265151065649872810324709323 397726598474809215487063985)
              ·
                refine ⟨298294948856106911615297989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397726598474809215487063985 298294948856106911615297989)
                ·
                  refine ⟨55930302910520045927868373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298294948856106911615297989 55930302910520045927868373)
                  ·
                    refine ⟨1310866474465313576434415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55930302910520045927868373 1310866474465313576434415)
                    ·
                      rfl

theorem cell22_3829355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_3829355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829355 prefixEnd_3829355 := by exact prefixLift 3829355
  have htrace : WordTrace (prefixWord ++ tailWord_3829355) baseStart_3829355 baseEnd_3829355 := by
    simpa [prefixWord, tailWord_3829355, baseEnd_3829355] using wordTrace_append hprefix tailTrace_3829355
  have hstable : (prefixWord ++ tailWord_3829355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829355).length < 2 ^ (prefixWord ++ tailWord_3829355).sum := by decide
  have hdescent : baseEnd_3829355 < baseStart_3829355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829357 : List Nat := [1, 5, 1, 1, 4, 10]
def baseStart_3829357 : Nat := 118140960795 + 3829357 * 2 ^ 59
def prefixEnd_3829357 : Nat := 4983230072969 + 3 ^ 40 * 3829357 * 2
def baseEnd_3829357 : Nat := 16183545174150447381289

theorem tailTrace_3829357 : CollatzResearch.WordTrace tailWord_3829357 prefixEnd_3829357 16183545174150447381289 := by
  unfold tailWord_3829357
  simp only [CollatzResearch.WordTrace]
  refine ⟨139668123987901065952942325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93112082658600710635294883 139668123987901065952942325)
  ·
    refine ⟨13093886623865724933088343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139668123987901065952942325 13093886623865724933088343)
    ·
      refine ⟨19640829935798587399632515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093886623865724933088343 19640829935798587399632515)
      ·
        refine ⟨29461244903697881099448773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19640829935798587399632515 29461244903697881099448773)
        ·
          refine ⟨5523983419443352706146645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29461244903697881099448773 5523983419443352706146645)
          ·
            refine ⟨16183545174150447381289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5523983419443352706146645 16183545174150447381289)
            ·
              rfl

theorem cell22_3829357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 10].length) (baseStart_3829357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829357 prefixEnd_3829357 := by exact prefixLift 3829357
  have htrace : WordTrace (prefixWord ++ tailWord_3829357) baseStart_3829357 baseEnd_3829357 := by
    simpa [prefixWord, tailWord_3829357, baseEnd_3829357] using wordTrace_append hprefix tailTrace_3829357
  have hstable : (prefixWord ++ tailWord_3829357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829357).length < 2 ^ (prefixWord ++ tailWord_3829357).sum := by decide
  have hdescent : baseEnd_3829357 < baseStart_3829357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829432 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_3829432 : Nat := 118140960795 + 3829432 * 2 ^ 59
def prefixEnd_3829432 : Nat := 4983230072969 + 3 ^ 40 * 3829432 * 2
def baseEnd_3829432 : Nat := 1310892833138911042259179

theorem tailTrace_3829432 : CollatzResearch.WordTrace tailWord_3829432 prefixEnd_3829432 1310892833138911042259179 := by
  unfold tailWord_3829432
  simp only [CollatzResearch.WordTrace]
  refine ⟨69835429731314676880961275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93113906308419569174615033 69835429731314676880961275)
  ·
    refine ⟨104753144596972015321441913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69835429731314676880961275 104753144596972015321441913)
    ·
      refine ⟨78564858447729011491081435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104753144596972015321441913 78564858447729011491081435)
      ·
        refine ⟨117847287671593517236622153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78564858447729011491081435 117847287671593517236622153)
        ·
          refine ⟨88385465753695137927466615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117847287671593517236622153 88385465753695137927466615)
          ·
            refine ⟨132578198630542706891199923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88385465753695137927466615 132578198630542706891199923)
            ·
              refine ⟨198867297945814060336799885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132578198630542706891199923 198867297945814060336799885)
              ·
                refine ⟨74575236729680272626299957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198867297945814060336799885 74575236729680272626299957)
                ·
                  refine ⟨6991428443407525558715621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74575236729680272626299957 6991428443407525558715621)
                  ·
                    refine ⟨1310892833138911042259179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6991428443407525558715621 1310892833138911042259179)
                    ·
                      rfl

theorem cell22_3829432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_3829432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829432 prefixEnd_3829432 := by exact prefixLift 3829432
  have htrace : WordTrace (prefixWord ++ tailWord_3829432) baseStart_3829432 baseEnd_3829432 := by
    simpa [prefixWord, tailWord_3829432, baseEnd_3829432] using wordTrace_append hprefix tailTrace_3829432
  have hstable : (prefixWord ++ tailWord_3829432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829432).length < 2 ^ (prefixWord ++ tailWord_3829432).sum := by decide
  have hdescent : baseEnd_3829432 < baseStart_3829432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829436 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 5]
def baseStart_3829436 : Nat := 118140960795 + 3829436 * 2 ^ 59
def prefixEnd_3829436 : Nat := 4983230072969 + 3 ^ 40 * 3829436 * 2
def baseEnd_3829436 : Nat := 436964734140218788386389

theorem tailTrace_3829436 : CollatzResearch.WordTrace tailWord_3829436 prefixEnd_3829436 436964734140218788386389 := by
  unfold tailWord_3829436
  simp only [CollatzResearch.WordTrace]
  refine ⟨69835502677307431222534081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93114003569743241630045441 69835502677307431222534081)
  ·
    refine ⟨52376627007980573416900561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69835502677307431222534081 52376627007980573416900561)
    ·
      refine ⟨39282470255985430062675421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52376627007980573416900561 39282470255985430062675421)
      ·
        refine ⟨14730926345994536273503283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39282470255985430062675421 14730926345994536273503283)
        ·
          refine ⟨22096389518991804410254925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14730926345994536273503283 22096389518991804410254925)
          ·
            refine ⟨8286146069621926653845597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22096389518991804410254925 8286146069621926653845597)
            ·
              refine ⟨3107304776108222495192099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8286146069621926653845597 3107304776108222495192099)
              ·
                refine ⟨4660957164162333742788149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107304776108222495192099 4660957164162333742788149)
                ·
                  refine ⟨436964734140218788386389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4660957164162333742788149 436964734140218788386389)
                  ·
                    rfl

theorem cell22_3829436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_3829436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829436 prefixEnd_3829436 := by exact prefixLift 3829436
  have htrace : WordTrace (prefixWord ++ tailWord_3829436) baseStart_3829436 baseEnd_3829436 := by
    simpa [prefixWord, tailWord_3829436, baseEnd_3829436] using wordTrace_append hprefix tailTrace_3829436
  have hstable : (prefixWord ++ tailWord_3829436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829436).length < 2 ^ (prefixWord ++ tailWord_3829436).sum := by decide
  have hdescent : baseEnd_3829436 < baseStart_3829436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829442 : List Nat := [3, 5, 1, 2, 2, 1, 2, 6]
def baseStart_3829442 : Nat := 118140960795 + 3829442 * 2 ^ 59
def prefixEnd_3829442 : Nat := 4983230072969 + 3 ^ 40 * 3829442 * 2
def baseEnd_3829442 : Nat := 145655139593697149945461

theorem tailTrace_3829442 : CollatzResearch.WordTrace tailWord_3829442 prefixEnd_3829442 145655139593697149945461 := by
  unfold tailWord_3829442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34917806048148281367446645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93114149461728750313191053 34917806048148281367446645)
  ·
    refine ⟨3273544317013901378198123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34917806048148281367446645 3273544317013901378198123)
    ·
      refine ⟨4910316475520852067297185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3273544317013901378198123 4910316475520852067297185)
      ·
        refine ⟨3682737356640639050472889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4910316475520852067297185 3682737356640639050472889)
        ·
          refine ⟨2762053017480479287854667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682737356640639050472889 2762053017480479287854667)
          ·
            refine ⟨4143079526220718931782001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762053017480479287854667 4143079526220718931782001)
            ·
              refine ⟨3107309644665539198836501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4143079526220718931782001 3107309644665539198836501)
              ·
                refine ⟨145655139593697149945461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3107309644665539198836501 145655139593697149945461)
                ·
                  rfl

theorem cell22_3829442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_3829442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829442 prefixEnd_3829442 := by exact prefixLift 3829442
  have htrace : WordTrace (prefixWord ++ tailWord_3829442) baseStart_3829442 baseEnd_3829442 := by
    simpa [prefixWord, tailWord_3829442, baseEnd_3829442] using wordTrace_append hprefix tailTrace_3829442
  have hstable : (prefixWord ++ tailWord_3829442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829442).length < 2 ^ (prefixWord ++ tailWord_3829442).sum := by decide
  have hdescent : baseEnd_3829442 < baseStart_3829442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829447 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 6]
def baseStart_3829447 : Nat := 118140960795 + 3829447 * 2 ^ 59
def prefixEnd_3829447 : Nat := 4983230072969 + 3 ^ 40 * 3829447 * 2
def baseEnd_3829447 : Nat := 436965989315152001044711

theorem tailTrace_3829447 : CollatzResearch.WordTrace tailWord_3829447 prefixEnd_3829447 436965989315152001044711 := by
  unfold tailWord_3829447
  simp only [CollatzResearch.WordTrace]
  refine ⟨139671406557575011323718595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93114271038383340882479063 139671406557575011323718595)
  ·
    refine ⟨209507109836362516985577893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139671406557575011323718595 209507109836362516985577893)
    ·
      refine ⟨39282583094317971934795855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209507109836362516985577893 39282583094317971934795855)
      ·
        refine ⟨58923874641476957902193783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39282583094317971934795855 58923874641476957902193783)
        ·
          refine ⟨88385811962215436853290675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58923874641476957902193783 88385811962215436853290675)
          ·
            refine ⟨132578717943323155279936013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88385811962215436853290675 132578717943323155279936013)
            ·
              refine ⟨49717019228746183229976005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132578717943323155279936013 49717019228746183229976005)
              ·
                refine ⟨9321941105389909355620501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49717019228746183229976005 9321941105389909355620501)
                ·
                  refine ⟨436965989315152001044711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9321941105389909355620501 436965989315152001044711)
                  ·
                    rfl

theorem cell22_3829447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 6].length) (baseStart_3829447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829447 prefixEnd_3829447 := by exact prefixLift 3829447
  have htrace : WordTrace (prefixWord ++ tailWord_3829447) baseStart_3829447 baseEnd_3829447 := by
    simpa [prefixWord, tailWord_3829447, baseEnd_3829447] using wordTrace_append hprefix tailTrace_3829447
  have hstable : (prefixWord ++ tailWord_3829447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829447).length < 2 ^ (prefixWord ++ tailWord_3829447).sum := by decide
  have hdescent : baseEnd_3829447 < baseStart_3829447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829507 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 2, 7]
def baseStart_3829507 : Nat := 118140960795 + 3829507 * 2 ^ 59
def prefixEnd_3829507 : Nat := 4983230072969 + 3 ^ 40 * 3829507 * 2
def baseEnd_3829507 : Nat := 1310918507171635846633949

theorem tailTrace_3829507 : CollatzResearch.WordTrace tailWord_3829507 prefixEnd_3829507 1310918507171635846633949 := by
  unfold tailWord_3829507
  simp only [CollatzResearch.WordTrace]
  refine ⟨139673594937357641570902775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93115729958238427713935183 139673594937357641570902775)
  ·
    refine ⟨209510392406036462356354163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139673594937357641570902775 209510392406036462356354163)
    ·
      refine ⟨314265588609054693534531245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209510392406036462356354163 314265588609054693534531245)
      ·
        refine ⟨117849595728395510075449217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314265588609054693534531245 117849595728395510075449217)
        ·
          refine ⟨88387196796296632556586913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117849595728395510075449217 88387196796296632556586913)
          ·
            refine ⟨66290397597222474417440185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88387196796296632556586913 66290397597222474417440185)
            ·
              refine ⟨49717798197916855813080139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66290397597222474417440185 49717798197916855813080139)
              ·
                refine ⟨74576697296875283719620209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49717798197916855813080139 74576697296875283719620209)
                ·
                  refine ⟨55932522972656462789715157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74576697296875283719620209 55932522972656462789715157)
                  ·
                    refine ⟨1310918507171635846633949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55932522972656462789715157 1310918507171635846633949)
                    ·
                      rfl

theorem cell22_3829507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_3829507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829507 prefixEnd_3829507 := by exact prefixLift 3829507
  have htrace : WordTrace (prefixWord ++ tailWord_3829507) baseStart_3829507 baseEnd_3829507 := by
    simpa [prefixWord, tailWord_3829507, baseEnd_3829507] using wordTrace_append hprefix tailTrace_3829507
  have hstable : (prefixWord ++ tailWord_3829507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829507).length < 2 ^ (prefixWord ++ tailWord_3829507).sum := by decide
  have hdescent : baseEnd_3829507 < baseStart_3829507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829558 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3829558 : Nat := 118140960795 + 3829558 * 2 ^ 59
def prefixEnd_3829558 : Nat := 4983230072969 + 3 ^ 40 * 3829558 * 2
def baseEnd_3829558 : Nat := 1310935965513888713608793

theorem tailTrace_3829558 : CollatzResearch.WordTrace tailWord_3829558 prefixEnd_3829558 1310935965513888713608793 := by
  unfold tailWord_3829558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8729715941260804830063083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93116970040115251520672885 8729715941260804830063083)
  ·
    refine ⟨13094573911891207245094625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8729715941260804830063083 13094573911891207245094625)
    ·
      refine ⟨9820930433918405433820969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13094573911891207245094625 9820930433918405433820969)
      ·
        refine ⟨7365697825438804075365727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9820930433918405433820969 7365697825438804075365727)
        ·
          refine ⟨11048546738158206113048591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7365697825438804075365727 11048546738158206113048591)
          ·
            refine ⟨16572820107237309169572887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11048546738158206113048591 16572820107237309169572887)
            ·
              refine ⟨24859230160855963754359331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16572820107237309169572887 24859230160855963754359331)
              ·
                refine ⟨37288845241283945631538997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24859230160855963754359331 37288845241283945631538997)
                ·
                  refine ⟨3495829241370369902956781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37288845241283945631538997 3495829241370369902956781)
                  ·
                    refine ⟨1310935965513888713608793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3495829241370369902956781 1310935965513888713608793)
                    ·
                      rfl

theorem cell22_3829558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3829558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829558 prefixEnd_3829558 := by exact prefixLift 3829558
  have htrace : WordTrace (prefixWord ++ tailWord_3829558) baseStart_3829558 baseEnd_3829558 := by
    simpa [prefixWord, tailWord_3829558, baseEnd_3829558] using wordTrace_append hprefix tailTrace_3829558
  have hstable : (prefixWord ++ tailWord_3829558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829558).length < 2 ^ (prefixWord ++ tailWord_3829558).sum := by decide
  have hdescent : baseEnd_3829558 < baseStart_3829558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829588 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 5]
def baseStart_3829588 : Nat := 118140960795 + 3829588 * 2 ^ 59
def prefixEnd_3829588 : Nat := 4983230072969 + 3 ^ 40 * 3829588 * 2
def baseEnd_3829588 : Nat := 436982078375659545119567

theorem tailTrace_3829588 : CollatzResearch.WordTrace tailWord_3829588 prefixEnd_3829588 436982078375659545119567 := by
  unfold tailWord_3829588
  simp only [CollatzResearch.WordTrace]
  refine ⟨69838274625032096202300709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93117699500042794936400945 69838274625032096202300709)
  ·
    refine ⟨13094676492193518037931383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69838274625032096202300709 13094676492193518037931383)
    ·
      refine ⟨19642014738290277056897075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13094676492193518037931383 19642014738290277056897075)
      ·
        refine ⟨29463022107435415585345613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19642014738290277056897075 29463022107435415585345613)
        ·
          refine ⟨11048633290288280844504605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29463022107435415585345613 11048633290288280844504605)
          ·
            refine ⟨4143237483858105316689227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11048633290288280844504605 4143237483858105316689227)
            ·
              refine ⟨6214856225787157975033841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143237483858105316689227 6214856225787157975033841)
              ·
                refine ⟨4661142169340368481275381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6214856225787157975033841 4661142169340368481275381)
                ·
                  refine ⟨436982078375659545119567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4661142169340368481275381 436982078375659545119567)
                  ·
                    rfl

theorem cell22_3829588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_3829588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829588 prefixEnd_3829588 := by exact prefixLift 3829588
  have htrace : WordTrace (prefixWord ++ tailWord_3829588) baseStart_3829588 baseEnd_3829588 := by
    simpa [prefixWord, tailWord_3829588, baseEnd_3829588] using wordTrace_append hprefix tailTrace_3829588
  have hstable : (prefixWord ++ tailWord_3829588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829588).length < 2 ^ (prefixWord ++ tailWord_3829588).sum := by decide
  have hdescent : baseEnd_3829588 < baseStart_3829588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829599 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 6]
def baseStart_3829599 : Nat := 118140960795 + 3829599 * 2 ^ 59
def prefixEnd_3829599 : Nat := 4983230072969 + 3 ^ 40 * 3829599 * 2
def baseEnd_3829599 : Nat := 436983333550592757777889

theorem tailTrace_3829599 : CollatzResearch.WordTrace tailWord_3829599 prefixEnd_3829599 436983333550592757777889 := by
  unfold tailWord_3829599
  simp only [CollatzResearch.WordTrace]
  refine ⟨139676950453024341283251851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93117966968682894188834567 139676950453024341283251851)
  ·
    refine ⟨209515425679536511924877777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139676950453024341283251851 209515425679536511924877777)
    ·
      refine ⟨157136569259652383943658333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209515425679536511924877777 157136569259652383943658333)
      ·
        refine ⟨58926213472369643978871875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157136569259652383943658333 58926213472369643978871875)
        ·
          refine ⟨88389320208554465968307813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58926213472369643978871875 88389320208554465968307813)
          ·
            refine ⟨16572997539103962369057715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88389320208554465968307813 16572997539103962369057715)
            ·
              refine ⟨24859496308655943553586573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16572997539103962369057715 24859496308655943553586573)
              ·
                refine ⟨9322311115745978832594965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24859496308655943553586573 9322311115745978832594965)
                ·
                  refine ⟨436983333550592757777889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9322311115745978832594965 436983333550592757777889)
                  ·
                    rfl

theorem cell22_3829599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 6].length) (baseStart_3829599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829599 prefixEnd_3829599 := by exact prefixLift 3829599
  have htrace : WordTrace (prefixWord ++ tailWord_3829599) baseStart_3829599 baseEnd_3829599 := by
    simpa [prefixWord, tailWord_3829599, baseEnd_3829599] using wordTrace_append hprefix tailTrace_3829599
  have hstable : (prefixWord ++ tailWord_3829599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829599).length < 2 ^ (prefixWord ++ tailWord_3829599).sum := by decide
  have hdescent : baseEnd_3829599 < baseStart_3829599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829661 : List Nat := [1, 4, 2, 1, 2, 3, 2, 7]
def baseStart_3829661 : Nat := 118140960795 + 3829661 * 2 ^ 59
def prefixEnd_3829661 : Nat := 4983230072969 + 3 ^ 40 * 3829661 * 2
def baseEnd_3829661 : Nat := 145663469390981197587053

theorem tailTrace_3829661 : CollatzResearch.WordTrace tailWord_3829661 prefixEnd_3829661 145663469390981197587053 := by
  unfold tailWord_3829661
  simp only [CollatzResearch.WordTrace]
  refine ⟨139679211778799725872008837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93119474519199817248005891 139679211778799725872008837)
  ·
    refine ⟨26189852208524948601001657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139679211778799725872008837 26189852208524948601001657)
    ·
      refine ⟨19642389156393711450751243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26189852208524948601001657 19642389156393711450751243)
      ·
        refine ⟨29463583734590567176126865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19642389156393711450751243 29463583734590567176126865)
        ·
          refine ⟨22097687800942925382095149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29463583734590567176126865 22097687800942925382095149)
          ·
            refine ⟨8286632925353597018285681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22097687800942925382095149 8286632925353597018285681)
            ·
              refine ⟨6214974694015197763714261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8286632925353597018285681 6214974694015197763714261)
              ·
                refine ⟨145663469390981197587053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6214974694015197763714261 145663469390981197587053)
                ·
                  rfl

theorem cell22_3829661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 7].length) (baseStart_3829661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829661 prefixEnd_3829661 := by exact prefixLift 3829661
  have htrace : WordTrace (prefixWord ++ tailWord_3829661) baseStart_3829661 baseEnd_3829661 := by
    simpa [prefixWord, tailWord_3829661, baseEnd_3829661] using wordTrace_append hprefix tailTrace_3829661
  have hstable : (prefixWord ++ tailWord_3829661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829661).length < 2 ^ (prefixWord ++ tailWord_3829661).sum := by decide
  have hdescent : baseEnd_3829661 < baseStart_3829661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829665 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 2, 3]
def baseStart_3829665 : Nat := 118140960795 + 3829665 * 2 ^ 59
def prefixEnd_3829665 : Nat := 4983230072969 + 3 ^ 40 * 3829665 * 2
def baseEnd_3829665 : Nat := 1310972593800576101183465

theorem tailTrace_3829665 : CollatzResearch.WordTrace tailWord_3829665 prefixEnd_3829665 1310972593800576101183465 := by
  unfold tailWord_3829665
  simp only [CollatzResearch.WordTrace]
  refine ⟨139679357670785234555154449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93119571780523489703436299 139679357670785234555154449)
  ·
    refine ⟨104759518253088925916365837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139679357670785234555154449 104759518253088925916365837)
    ·
      refine ⟨39284819344908347218637189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104759518253088925916365837 39284819344908347218637189)
      ·
        refine ⟨7365903627170315103494473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39284819344908347218637189 7365903627170315103494473)
        ·
          refine ⟨5524427720377736327620855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7365903627170315103494473 5524427720377736327620855)
          ·
            refine ⟨8286641580566604491431283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5524427720377736327620855 8286641580566604491431283)
            ·
              refine ⟨12429962370849906737146925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8286641580566604491431283 12429962370849906737146925)
              ·
                refine ⟨4661235889068715026430097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12429962370849906737146925 4661235889068715026430097)
                ·
                  refine ⟨3495926916801536269822573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661235889068715026430097 3495926916801536269822573)
                  ·
                    refine ⟨1310972593800576101183465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3495926916801536269822573 1310972593800576101183465)
                    ·
                      rfl

theorem cell22_3829665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_3829665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829665 prefixEnd_3829665 := by exact prefixLift 3829665
  have htrace : WordTrace (prefixWord ++ tailWord_3829665) baseStart_3829665 baseEnd_3829665 := by
    simpa [prefixWord, tailWord_3829665, baseEnd_3829665] using wordTrace_append hprefix tailTrace_3829665
  have hstable : (prefixWord ++ tailWord_3829665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829665).length < 2 ^ (prefixWord ++ tailWord_3829665).sum := by decide
  have hdescent : baseEnd_3829665 < baseStart_3829665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829706 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_3829706 : Nat := 118140960795 + 3829706 * 2 ^ 59
def prefixEnd_3829706 : Nat := 4983230072969 + 3 ^ 40 * 3829706 * 2
def baseEnd_3829706 : Nat := 436995542979488553636113

theorem tailTrace_3829706 : CollatzResearch.WordTrace tailWord_3829706 prefixEnd_3829706 436995542979488553636113 := by
  unfold tailWord_3829706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34920213265909174639349243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93120568709091132371597981 34920213265909174639349243)
  ·
    refine ⟨52380319898863761959023865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34920213265909174639349243 52380319898863761959023865)
    ·
      refine ⟨39285239924147821469267899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52380319898863761959023865 39285239924147821469267899)
      ·
        refine ⟨58927859886221732203901849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39285239924147821469267899 58927859886221732203901849)
        ·
          refine ⟨44195894914666299152926387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58927859886221732203901849 44195894914666299152926387)
          ·
            refine ⟨66293842371999448729389581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44195894914666299152926387 66293842371999448729389581)
            ·
              refine ⟨24860190889499793273521093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66293842371999448729389581 24860190889499793273521093)
              ·
                refine ⟨4661285791781211238785205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24860190889499793273521093 4661285791781211238785205)
                ·
                  refine ⟨436995542979488553636113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4661285791781211238785205 436995542979488553636113)
                  ·
                    rfl

theorem cell22_3829706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_3829706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829706 prefixEnd_3829706 := by exact prefixLift 3829706
  have htrace : WordTrace (prefixWord ++ tailWord_3829706) baseStart_3829706 baseEnd_3829706 := by
    simpa [prefixWord, tailWord_3829706, baseEnd_3829706] using wordTrace_append hprefix tailTrace_3829706
  have hstable : (prefixWord ++ tailWord_3829706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829706).length < 2 ^ (prefixWord ++ tailWord_3829706).sum := by decide
  have hdescent : baseEnd_3829706 < baseStart_3829706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829710 : List Nat := [4, 1, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_3829710 : Nat := 118140960795 + 3829710 * 2 ^ 59
def prefixEnd_3829710 : Nat := 4983230072969 + 3 ^ 40 * 3829710 * 2
def baseEnd_3829710 : Nat := 1310987998220210983808327

theorem tailTrace_3829710 : CollatzResearch.WordTrace tailWord_3829710 prefixEnd_3829710 1310987998220210983808327 := by
  unfold tailWord_3829710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17460124869452775905067823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93120665970414804827028389 17460124869452775905067823)
  ·
    refine ⟨26190187304179163857601735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17460124869452775905067823 26190187304179163857601735)
    ·
      refine ⟨39285280956268745786402603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26190187304179163857601735 39285280956268745786402603)
      ·
        refine ⟨58927921434403118679603905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39285280956268745786402603 58927921434403118679603905)
        ·
          refine ⟨44195941075802339009702929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58927921434403118679603905 44195941075802339009702929)
          ·
            refine ⟨33146955806851754257277197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44195941075802339009702929 33146955806851754257277197)
            ·
              refine ⟨12430108427569407846478949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33146955806851754257277197 12430108427569407846478949)
              ·
                refine ⟨2330645330169263971214803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12430108427569407846478949 2330645330169263971214803)
                ·
                  refine ⟨3495967995253895956822205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330645330169263971214803 3495967995253895956822205)
                  ·
                    refine ⟨1310987998220210983808327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3495967995253895956822205 1310987998220210983808327)
                    ·
                      rfl

theorem cell22_3829710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_3829710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829710 prefixEnd_3829710 := by exact prefixLift 3829710
  have htrace : WordTrace (prefixWord ++ tailWord_3829710) baseStart_3829710 baseEnd_3829710 := by
    simpa [prefixWord, tailWord_3829710, baseEnd_3829710] using wordTrace_append hprefix tailTrace_3829710
  have hstable : (prefixWord ++ tailWord_3829710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829710).length < 2 ^ (prefixWord ++ tailWord_3829710).sum := by decide
  have hdescent : baseEnd_3829710 < baseStart_3829710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829753 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_3829753 : Nat := 118140960795 + 3829753 * 2 ^ 59
def prefixEnd_3829753 : Nat := 4983230072969 + 3 ^ 40 * 3829753 * 2
def baseEnd_3829753 : Nat := 1311002717998973204983195

theorem tailTrace_3829753 : CollatzResearch.WordTrace tailWord_3829753 prefixEnd_3829753 1311002717998973204983195 := by
  unfold tailWord_3829753
  simp only [CollatzResearch.WordTrace]
  refine ⟨139682567294466425584357913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93121711529644283722905275 139682567294466425584357913)
  ·
    refine ⟨104761925470849819188268435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139682567294466425584357913 104761925470849819188268435)
    ·
      refine ⟨157142888206274728782402653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104761925470849819188268435 157142888206274728782402653)
      ·
        refine ⟨58928583077353023293400995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157142888206274728782402653 58928583077353023293400995)
        ·
          refine ⟨88392874616029534940101493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58928583077353023293400995 88392874616029534940101493)
          ·
            refine ⟨8286831995252768900634515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88392874616029534940101493 8286831995252768900634515)
            ·
              refine ⟨12430247992879153350951773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8286831995252768900634515 12430247992879153350951773)
              ·
                refine ⟨4661342997329682506606915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12430247992879153350951773 4661342997329682506606915)
                ·
                  refine ⟨6992014495994523759910373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661342997329682506606915 6992014495994523759910373)
                  ·
                    refine ⟨1311002717998973204983195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6992014495994523759910373 1311002717998973204983195)
                    ·
                      rfl

theorem cell22_3829753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_3829753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829753 prefixEnd_3829753 := by exact prefixLift 3829753
  have htrace : WordTrace (prefixWord ++ tailWord_3829753) baseStart_3829753 baseEnd_3829753 := by
    simpa [prefixWord, tailWord_3829753, baseEnd_3829753] using wordTrace_append hprefix tailTrace_3829753
  have hstable : (prefixWord ++ tailWord_3829753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829753).length < 2 ^ (prefixWord ++ tailWord_3829753).sum := by decide
  have hdescent : baseEnd_3829753 < baseStart_3829753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829768 : List Nat := [2, 1, 3, 2, 1, 2, 1, 6, 4]
def baseStart_3829768 : Nat := 118140960795 + 3829768 * 2 ^ 59
def prefixEnd_3829768 : Nat := 4983230072969 + 3 ^ 40 * 3829768 * 2
def baseEnd_3829768 : Nat := 437002617601839388619383

theorem tailTrace_3829768 : CollatzResearch.WordTrace tailWord_3829768 prefixEnd_3829768 437002617601839388619383 := by
  unfold tailWord_3829768
  simp only [CollatzResearch.WordTrace]
  refine ⟨69841557194706041573076979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93122076259608055430769305 69841557194706041573076979)
  ·
    refine ⟨104762335792059062359615469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69841557194706041573076979 104762335792059062359615469)
    ·
      refine ⟨39285875922022148384855801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104762335792059062359615469 39285875922022148384855801)
      ·
        refine ⟨29464406941516611288641851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39285875922022148384855801 29464406941516611288641851)
        ·
          refine ⟨44196610412274916932962777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29464406941516611288641851 44196610412274916932962777)
          ·
            refine ⟨33147457809206187699722083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44196610412274916932962777 33147457809206187699722083)
            ·
              refine ⟨49721186713809281549583125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33147457809206187699722083 49721186713809281549583125)
              ·
                refine ⟨2330680627209810072636709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49721186713809281549583125 2330680627209810072636709)
                ·
                  refine ⟨437002617601839388619383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330680627209810072636709 437002617601839388619383)
                  ·
                    rfl

theorem cell22_3829768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 4].length) (baseStart_3829768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829768 prefixEnd_3829768 := by exact prefixLift 3829768
  have htrace : WordTrace (prefixWord ++ tailWord_3829768) baseStart_3829768 baseEnd_3829768 := by
    simpa [prefixWord, tailWord_3829768, baseEnd_3829768] using wordTrace_append hprefix tailTrace_3829768
  have hstable : (prefixWord ++ tailWord_3829768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829768).length < 2 ^ (prefixWord ++ tailWord_3829768).sum := by decide
  have hdescent : baseEnd_3829768 < baseStart_3829768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829802 : List Nat := [3, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_3829802 : Nat := 118140960795 + 3829802 * 2 ^ 59
def prefixEnd_3829802 : Nat := 4983230072969 + 3 ^ 40 * 3829802 * 2
def baseEnd_3829802 : Nat := 437006497233451136836015

theorem tailTrace_3829802 : CollatzResearch.WordTrace tailWord_3829802 prefixEnd_3829802 437006497233451136836015 := by
  unfold tailWord_3829802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34921088617822226738222915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93122902980859271301927773 34921088617822226738222915)
  ·
    refine ⟨52381632926733340107334373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34921088617822226738222915 52381632926733340107334373)
    ·
      refine ⟨9821556173762501270125195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52381632926733340107334373 9821556173762501270125195)
      ·
        refine ⟨14732334260643751905187793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9821556173762501270125195 14732334260643751905187793)
        ·
          refine ⟨11049250695482813928890845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14732334260643751905187793 11049250695482813928890845)
          ·
            refine ⟨4143469010806055223334067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11049250695482813928890845 4143469010806055223334067)
            ·
              refine ⟨6215203516209082835001101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143469010806055223334067 6215203516209082835001101)
              ·
                refine ⟨2330701318578406063125413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6215203516209082835001101 2330701318578406063125413)
                ·
                  refine ⟨437006497233451136836015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330701318578406063125413 437006497233451136836015)
                  ·
                    rfl

theorem cell22_3829802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_3829802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829802 prefixEnd_3829802 := by exact prefixLift 3829802
  have htrace : WordTrace (prefixWord ++ tailWord_3829802) baseStart_3829802 baseEnd_3829802 := by
    simpa [prefixWord, tailWord_3829802, baseEnd_3829802] using wordTrace_append hprefix tailTrace_3829802
  have hstable : (prefixWord ++ tailWord_3829802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829802).length < 2 ^ (prefixWord ++ tailWord_3829802).sum := by decide
  have hdescent : baseEnd_3829802 < baseStart_3829802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829830 : List Nat := [6, 1, 1, 1, 1, 1, 4, 7]
def baseStart_3829830 : Nat := 118140960795 + 3829830 * 2 ^ 59
def prefixEnd_3829830 : Nat := 4983230072969 + 3 ^ 40 * 3829830 * 2
def baseEnd_3829830 : Nat := 145669897408063407867551

theorem tailTrace_3829830 : CollatzResearch.WordTrace tailWord_3829830 prefixEnd_3829830 145669897408063407867551 := by
  unfold tailWord_3829830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365167991099608366715967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93123583810124978489940629 4365167991099608366715967)
  ·
    refine ⟨6547751986649412550073951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4365167991099608366715967 6547751986649412550073951)
    ·
      refine ⟨9821627979974118825110927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6547751986649412550073951 9821627979974118825110927)
      ·
        refine ⟨14732441969961178237666391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9821627979974118825110927 14732441969961178237666391)
        ·
          refine ⟨22098662954941767356499587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14732441969961178237666391 22098662954941767356499587)
          ·
            refine ⟨33147994432412651034749381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22098662954941767356499587 33147994432412651034749381)
            ·
              refine ⟨6215248956077372069015509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33147994432412651034749381 6215248956077372069015509)
              ·
                refine ⟨145669897408063407867551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6215248956077372069015509 145669897408063407867551)
                ·
                  rfl

theorem cell22_3829830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_3829830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829830 prefixEnd_3829830 := by exact prefixLift 3829830
  have htrace : WordTrace (prefixWord ++ tailWord_3829830) baseStart_3829830 baseEnd_3829830 := by
    simpa [prefixWord, tailWord_3829830, baseEnd_3829830] using wordTrace_append hprefix tailTrace_3829830
  have hstable : (prefixWord ++ tailWord_3829830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829830).length < 2 ^ (prefixWord ++ tailWord_3829830).sum := by decide
  have hdescent : baseEnd_3829830 < baseStart_3829830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829879 : List Nat := [1, 1, 3, 1, 1, 7, 2, 2, 1, 3]
def baseStart_3829879 : Nat := 118140960795 + 3829879 * 2 ^ 59
def prefixEnd_3829879 : Nat := 4983230072969 + 3 ^ 40 * 3829879 * 2
def baseEnd_3829879 : Nat := 1311045850373950876332809

theorem tailTrace_3829879 : CollatzResearch.WordTrace tailWord_3829879 prefixEnd_3829879 1311045850373950876332809 := by
  unfold tailWord_3829879
  simp only [CollatzResearch.WordTrace]
  refine ⟨139687162892009949103444691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93124775261339966068963127 139687162892009949103444691)
  ·
    refine ⟨209530744338014923655167037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139687162892009949103444691 209530744338014923655167037)
    ·
      refine ⟨78574029126755596370687639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209530744338014923655167037 78574029126755596370687639)
      ·
        refine ⟨117861043690133394556031459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78574029126755596370687639 117861043690133394556031459)
        ·
          refine ⟨176791565535200091834047189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117861043690133394556031459 176791565535200091834047189)
          ·
            refine ⟨4143552317231252152360481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 176791565535200091834047189 4143552317231252152360481)
            ·
              refine ⟨3107664237923439114270361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4143552317231252152360481 3107664237923439114270361)
              ·
                refine ⟨2330748178442579335702771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3107664237923439114270361 2330748178442579335702771)
                ·
                  refine ⟨3496122267663869003554157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330748178442579335702771 3496122267663869003554157)
                  ·
                    refine ⟨1311045850373950876332809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496122267663869003554157 1311045850373950876332809)
                    ·
                      rfl

theorem cell22_3829879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_3829879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829879 prefixEnd_3829879 := by exact prefixLift 3829879
  have htrace : WordTrace (prefixWord ++ tailWord_3829879) baseStart_3829879 baseEnd_3829879 := by
    simpa [prefixWord, tailWord_3829879, baseEnd_3829879] using wordTrace_append hprefix tailTrace_3829879
  have hstable : (prefixWord ++ tailWord_3829879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829879).length < 2 ^ (prefixWord ++ tailWord_3829879).sum := by decide
  have hdescent : baseEnd_3829879 < baseStart_3829879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829920 : List Nat := [2, 1, 1, 4, 2, 2, 1, 5, 4]
def baseStart_3829920 : Nat := 118140960795 + 3829920 * 2 ^ 59
def prefixEnd_3829920 : Nat := 4983230072969 + 3 ^ 40 * 3829920 * 2
def baseEnd_3829920 : Nat := 437019961837280145352561

theorem tailTrace_3829920 : CollatzResearch.WordTrace tailWord_3829920 prefixEnd_3829920 437019961837280145352561 := by
  unfold tailWord_3829920
  simp only [CollatzResearch.WordTrace]
  refine ⟨69844329142430706552843607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93125772189907608737124809 69844329142430706552843607)
  ·
    refine ⟨104766493713646059829265411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69844329142430706552843607 104766493713646059829265411)
    ·
      refine ⟨157149740570469089743898117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104766493713646059829265411 157149740570469089743898117)
      ·
        refine ⟨29465576356962954326980897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157149740570469089743898117 29465576356962954326980897)
        ·
          refine ⟨22099182267722215745235673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29465576356962954326980897 22099182267722215745235673)
          ·
            refine ⟨16574386700791661808926755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22099182267722215745235673 16574386700791661808926755)
            ·
              refine ⟨24861580051187492713390133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16574386700791661808926755 24861580051187492713390133)
              ·
                refine ⟨2330773129798827441880325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24861580051187492713390133 2330773129798827441880325)
                ·
                  refine ⟨437019961837280145352561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2330773129798827441880325 437019961837280145352561)
                  ·
                    rfl

theorem cell22_3829920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 4].length) (baseStart_3829920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829920 prefixEnd_3829920 := by exact prefixLift 3829920
  have htrace : WordTrace (prefixWord ++ tailWord_3829920) baseStart_3829920 baseEnd_3829920 := by
    simpa [prefixWord, tailWord_3829920, baseEnd_3829920] using wordTrace_append hprefix tailTrace_3829920
  have hstable : (prefixWord ++ tailWord_3829920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829920).length < 2 ^ (prefixWord ++ tailWord_3829920).sum := by decide
  have hdescent : baseEnd_3829920 < baseStart_3829920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3829922 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3829922 : Nat := 118140960795 + 3829922 * 2 ^ 59
def prefixEnd_3829922 : Nat := 4983230072969 + 3 ^ 40 * 3829922 * 2
def baseEnd_3829922 : Nat := 1311060570152713097507677

theorem tailTrace_3829922 : CollatzResearch.WordTrace tailWord_3829922 prefixEnd_3829922 1311060570152713097507677 := by
  unfold tailWord_3829922
  simp only [CollatzResearch.WordTrace]
  refine ⟨34922182807713541861815005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93125820820569444964840013 34922182807713541861815005)
  ·
    refine ⟨13095818552892578198180627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34922182807713541861815005 13095818552892578198180627)
    ·
      refine ⟨19643727829338867297270941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095818552892578198180627 19643727829338867297270941)
      ·
        refine ⟨7366397936002075236476603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19643727829338867297270941 7366397936002075236476603)
        ·
          refine ⟨11049596904003112854714905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7366397936002075236476603 11049596904003112854714905)
          ·
            refine ⟨8287197678002334641036179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11049596904003112854714905 8287197678002334641036179)
            ·
              refine ⟨12430796517003501961554269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287197678002334641036179 12430796517003501961554269)
              ·
                refine ⟨4661548693876313235582851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12430796517003501961554269 4661548693876313235582851)
                ·
                  refine ⟨6992323040814469853374277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661548693876313235582851 6992323040814469853374277)
                  ·
                    refine ⟨1311060570152713097507677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6992323040814469853374277 1311060570152713097507677)
                    ·
                      rfl

theorem cell22_3829922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3829922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3829922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3829922 prefixEnd_3829922 := by exact prefixLift 3829922
  have htrace : WordTrace (prefixWord ++ tailWord_3829922) baseStart_3829922 baseEnd_3829922 := by
    simpa [prefixWord, tailWord_3829922, baseEnd_3829922] using wordTrace_append hprefix tailTrace_3829922
  have hstable : (prefixWord ++ tailWord_3829922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3829922).length < 2 ^ (prefixWord ++ tailWord_3829922).sum := by decide
  have hdescent : baseEnd_3829922 < baseStart_3829922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3829922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830008 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_3830008 : Nat := 118140960795 + 3830008 * 2 ^ 59
def prefixEnd_3830008 : Nat := 4983230072969 + 3 ^ 40 * 3830008 * 2
def baseEnd_3830008 : Nat := 1311090009710237539857413

theorem tailTrace_3830008 : CollatzResearch.WordTrace tailWord_3830008 prefixEnd_3830008 1311090009710237539857413 := by
  unfold tailWord_3830008
  simp only [CollatzResearch.WordTrace]
  refine ⟨69845933954271302067445339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93127911939028402756593785 69845933954271302067445339)
  ·
    refine ⟨104768900931406953101168009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69845933954271302067445339 104768900931406953101168009)
    ·
      refine ⟨78576675698555214825876007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104768900931406953101168009 78576675698555214825876007)
      ·
        refine ⟨117865013547832822238814011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78576675698555214825876007 117865013547832822238814011)
        ·
          refine ⟨176797520321749233358221017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117865013547832822238814011 176797520321749233358221017)
          ·
            refine ⟨132598140241311925018665763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176797520321749233358221017 132598140241311925018665763)
            ·
              refine ⟨198897210361967887527998645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132598140241311925018665763 198897210361967887527998645)
              ·
                refine ⟨18646613471434489455749873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198897210361967887527998645 18646613471434489455749873)
                ·
                  refine ⟨13984960103575867091812405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18646613471434489455749873 13984960103575867091812405)
                  ·
                    refine ⟨1311090009710237539857413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13984960103575867091812405 1311090009710237539857413)
                    ·
                      rfl

theorem cell22_3830008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_3830008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830008 prefixEnd_3830008 := by exact prefixLift 3830008
  have htrace : WordTrace (prefixWord ++ tailWord_3830008) baseStart_3830008 baseEnd_3830008 := by
    simpa [prefixWord, tailWord_3830008, baseEnd_3830008] using wordTrace_append hprefix tailTrace_3830008
  have hstable : (prefixWord ++ tailWord_3830008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830008).length < 2 ^ (prefixWord ++ tailWord_3830008).sum := by decide
  have hdescent : baseEnd_3830008 < baseStart_3830008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830010 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_3830010 : Nat := 118140960795 + 3830010 * 2 ^ 59
def prefixEnd_3830010 : Nat := 4983230072969 + 3 ^ 40 * 3830010 * 2
def baseEnd_3830010 : Nat := 437030231450370067102469

theorem tailTrace_3830010 : CollatzResearch.WordTrace tailWord_3830010 prefixEnd_3830010 437030231450370067102469 := by
  unfold tailWord_3830010
  simp only [CollatzResearch.WordTrace]
  refine ⟨34922985213633839619115871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93127960569690238984308989 34922985213633839619115871)
  ·
    refine ⟨52384477820450759428673807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34922985213633839619115871 52384477820450759428673807)
    ·
      refine ⟨78576716730676139143010711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52384477820450759428673807 78576716730676139143010711)
      ·
        refine ⟨117865075096014208714516067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78576716730676139143010711 117865075096014208714516067)
        ·
          refine ⟨176797612644021313071774101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117865075096014208714516067 176797612644021313071774101)
          ·
            refine ⟨8287388092688499050239411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176797612644021313071774101 8287388092688499050239411)
            ·
              refine ⟨12431082139032748575359117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287388092688499050239411 12431082139032748575359117)
              ·
                refine ⟨4661655802137280715759669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12431082139032748575359117 4661655802137280715759669)
                ·
                  refine ⟨437030231450370067102469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4661655802137280715759669 437030231450370067102469)
                  ·
                    rfl

theorem cell22_3830010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_3830010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830010 prefixEnd_3830010 := by exact prefixLift 3830010
  have htrace : WordTrace (prefixWord ++ tailWord_3830010) baseStart_3830010 baseEnd_3830010 := by
    simpa [prefixWord, tailWord_3830010, baseEnd_3830010] using wordTrace_append hprefix tailTrace_3830010
  have hstable : (prefixWord ++ tailWord_3830010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830010).length < 2 ^ (prefixWord ++ tailWord_3830010).sum := by decide
  have hdescent : baseEnd_3830010 < baseStart_3830010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830083 : List Nat := [1, 1, 1, 3, 1, 3, 2, 10]
def baseStart_3830083 : Nat := 118140960795 + 3830083 * 2 ^ 59
def prefixEnd_3830083 : Nat := 4983230072969 + 3 ^ 40 * 3830083 * 2
def baseEnd_3830083 : Nat := 145679520415884704914687

theorem tailTrace_3830083 : CollatzResearch.WordTrace tailWord_3830083 prefixEnd_3830083 145679520415884704914687 := by
  unfold tailWord_3830083
  simp only [CollatzResearch.WordTrace]
  refine ⟨139694603383270891943870903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93129735588847261295913935 139694603383270891943870903)
  ·
    refine ⟨209541905074906337915806355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139694603383270891943870903 209541905074906337915806355)
    ·
      refine ⟨314312857612359506873709533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209541905074906337915806355 314312857612359506873709533)
      ·
        refine ⟨117867321604634815077641075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314312857612359506873709533 117867321604634815077641075)
        ·
          refine ⟨176800982406952222616461613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117867321604634815077641075 176800982406952222616461613)
          ·
            refine ⟨66300368402607083481173105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176800982406952222616461613 66300368402607083481173105)
            ·
              refine ⟨49725276301955312610879829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66300368402607083481173105 49725276301955312610879829)
              ·
                refine ⟨145679520415884704914687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49725276301955312610879829 145679520415884704914687)
                ·
                  rfl

theorem cell22_3830083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 10].length) (baseStart_3830083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830083 prefixEnd_3830083 := by exact prefixLift 3830083
  have htrace : WordTrace (prefixWord ++ tailWord_3830083) baseStart_3830083 baseEnd_3830083 := by
    simpa [prefixWord, tailWord_3830083, baseEnd_3830083] using wordTrace_append hprefix tailTrace_3830083
  have hstable : (prefixWord ++ tailWord_3830083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830083).length < 2 ^ (prefixWord ++ tailWord_3830083).sum := by decide
  have hdescent : baseEnd_3830083 < baseStart_3830083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830100 : List Nat := [2, 4, 1, 1, 2, 3, 9]
def baseStart_3830100 : Nat := 118140960795 + 3830100 * 2 ^ 59
def prefixEnd_3830100 : Nat := 4983230072969 + 3 ^ 40 * 3830100 * 2
def baseEnd_3830100 : Nat := 48560055673717776539153

theorem tailTrace_3830100 : CollatzResearch.WordTrace tailWord_3830100 prefixEnd_3830100 48560055673717776539153 := by
  unfold tailWord_3830100
  simp only [CollatzResearch.WordTrace]
  refine ⟨69847611712104651923619877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93130148949472869231493169 69847611712104651923619877)
  ·
    refine ⟨13096427196019622235678727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69847611712104651923619877 13096427196019622235678727)
    ·
      refine ⟨19644640794029433353518091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13096427196019622235678727 19644640794029433353518091)
      ·
        refine ⟨29466961191044150030277137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19644640794029433353518091 29466961191044150030277137)
        ·
          refine ⟨22100220893283112522707853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29466961191044150030277137 22100220893283112522707853)
          ·
            refine ⟨8287582834981167196015445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22100220893283112522707853 8287582834981167196015445)
            ·
              refine ⟨48560055673717776539153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8287582834981167196015445 48560055673717776539153)
              ·
                rfl

theorem cell22_3830100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 9].length) (baseStart_3830100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830100 prefixEnd_3830100 := by exact prefixLift 3830100
  have htrace : WordTrace (prefixWord ++ tailWord_3830100) baseStart_3830100 baseEnd_3830100 := by
    simpa [prefixWord, tailWord_3830100, baseEnd_3830100] using wordTrace_append hprefix tailTrace_3830100
  have hstable : (prefixWord ++ tailWord_3830100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830100).length < 2 ^ (prefixWord ++ tailWord_3830100).sum := by decide
  have hdescent : baseEnd_3830100 < baseStart_3830100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830134 : List Nat := [5, 1, 1, 4, 1, 1, 1, 8]
def baseStart_3830134 : Nat := 118140960795 + 3830134 * 2 ^ 59
def prefixEnd_3830134 : Nat := 4983230072969 + 3 ^ 40 * 3830134 * 2
def baseEnd_3830134 : Nat := 145681460231690579023003

theorem tailTrace_3830134 : CollatzResearch.WordTrace tailWord_3830134 prefixEnd_3830134 145681460231690579023003 := by
  unfold tailWord_3830134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731028969130382978373591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93130975670724085102651637 8731028969130382978373591)
  ·
    refine ⟨13096543453695574467560387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8731028969130382978373591 13096543453695574467560387)
    ·
      refine ⟨19644815180543361701340581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13096543453695574467560387 19644815180543361701340581)
      ·
        refine ⟨3683402846351880319001359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19644815180543361701340581 3683402846351880319001359)
        ·
          refine ⟨5525104269527820478502039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683402846351880319001359 5525104269527820478502039)
          ·
            refine ⟨8287656404291730717753059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525104269527820478502039 8287656404291730717753059)
            ·
              refine ⟨12431484606437596076629589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8287656404291730717753059 12431484606437596076629589)
              ·
                refine ⟨145681460231690579023003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12431484606437596076629589 145681460231690579023003)
                ·
                  rfl

theorem cell22_3830134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_3830134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830134 prefixEnd_3830134 := by exact prefixLift 3830134
  have htrace : WordTrace (prefixWord ++ tailWord_3830134) baseStart_3830134 baseEnd_3830134 := by
    simpa [prefixWord, tailWord_3830134, baseEnd_3830134] using wordTrace_append hprefix tailTrace_3830134
  have hstable : (prefixWord ++ tailWord_3830134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830134).length < 2 ^ (prefixWord ++ tailWord_3830134).sum := by decide
  have hdescent : baseEnd_3830134 < baseStart_3830134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830179 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 5]
def baseStart_3830179 : Nat := 118140960795 + 3830179 * 2 ^ 59
def prefixEnd_3830179 : Nat := 4983230072969 + 3 ^ 40 * 3830179 * 2
def baseEnd_3830179 : Nat := 437049515501616697943963

theorem tailTrace_3830179 : CollatzResearch.WordTrace tailWord_3830179 prefixEnd_3830179 437049515501616697943963 := by
  unfold tailWord_3830179
  simp only [CollatzResearch.WordTrace]
  refine ⟨139698104790923100339365591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93132069860615400226243727 139698104790923100339365591)
  ·
    refine ⟨209547157186384650509048387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139698104790923100339365591 209547157186384650509048387)
    ·
      refine ⟨314320735779576975763572581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209547157186384650509048387 314320735779576975763572581)
      ·
        refine ⟨58935137958670682955669859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 314320735779576975763572581 58935137958670682955669859)
        ·
          refine ⟨88402706938006024433504789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58935137958670682955669859 88402706938006024433504789)
          ·
            refine ⟨4143876887719032395320537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88402706938006024433504789 4143876887719032395320537)
            ·
              refine ⟨3107907665789274296490403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4143876887719032395320537 3107907665789274296490403)
              ·
                refine ⟨4661861498683911444735605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107907665789274296490403 4661861498683911444735605)
                ·
                  refine ⟨437049515501616697943963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4661861498683911444735605 437049515501616697943963)
                  ·
                    rfl

theorem cell22_3830179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 5].length) (baseStart_3830179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830179 prefixEnd_3830179 := by exact prefixLift 3830179
  have htrace : WordTrace (prefixWord ++ tailWord_3830179) baseStart_3830179 baseEnd_3830179 := by
    simpa [prefixWord, tailWord_3830179, baseEnd_3830179] using wordTrace_append hprefix tailTrace_3830179
  have hstable : (prefixWord ++ tailWord_3830179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830179).length < 2 ^ (prefixWord ++ tailWord_3830179).sum := by decide
  have hdescent : baseEnd_3830179 < baseStart_3830179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830237 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3830237 : Nat := 118140960795 + 3830237 * 2 ^ 59
def prefixEnd_3830237 : Nat := 4983230072969 + 3 ^ 40 * 3830237 * 2
def baseEnd_3830237 : Nat := 1311168401090157275881711

theorem tailTrace_3830237 : CollatzResearch.WordTrace tailWord_3830237 prefixEnd_3830237 1311168401090157275881711 := by
  unfold tailWord_3830237
  simp only [CollatzResearch.WordTrace]
  refine ⟨139700220224712976244976965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93133480149808650829984643 139700220224712976244976965)
  ·
    refine ⟨26193791292133683045933181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139700220224712976244976965 26193791292133683045933181)
    ·
      refine ⟨9822671734550131142224943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26193791292133683045933181 9822671734550131142224943)
      ·
        refine ⟨14734007601825196713337415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9822671734550131142224943 14734007601825196713337415)
        ·
          refine ⟨22101011402737795070006123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14734007601825196713337415 22101011402737795070006123)
          ·
            refine ⟨33151517104106692605009185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22101011402737795070006123 33151517104106692605009185)
            ·
              refine ⟨24863637828080019453756889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33151517104106692605009185 24863637828080019453756889)
              ·
                refine ⟨18647728371060014590317667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24863637828080019453756889 18647728371060014590317667)
                ·
                  refine ⟨27971592556590021885476501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18647728371060014590317667 27971592556590021885476501)
                  ·
                    refine ⟨1311168401090157275881711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27971592556590021885476501 1311168401090157275881711)
                    ·
                      rfl

theorem cell22_3830237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3830237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830237 prefixEnd_3830237 := by exact prefixLift 3830237
  have htrace : WordTrace (prefixWord ++ tailWord_3830237) baseStart_3830237 baseEnd_3830237 := by
    simpa [prefixWord, tailWord_3830237, baseEnd_3830237] using wordTrace_append hprefix tailTrace_3830237
  have hstable : (prefixWord ++ tailWord_3830237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830237).length < 2 ^ (prefixWord ++ tailWord_3830237).sum := by decide
  have hdescent : baseEnd_3830237 < baseStart_3830237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830239 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 2, 3]
def baseStart_3830239 : Nat := 118140960795 + 3830239 * 2 ^ 59
def prefixEnd_3830239 : Nat := 4983230072969 + 3 ^ 40 * 3830239 * 2
def baseEnd_3830239 : Nat := 1311169085731029937331705

theorem tailTrace_3830239 : CollatzResearch.WordTrace tailWord_3830239 prefixEnd_3830239 1311169085731029937331705 := by
  unfold tailWord_3830239
  simp only [CollatzResearch.WordTrace]
  refine ⟨139700293170705730586549771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93133528780470487057699847 139700293170705730586549771)
  ·
    refine ⟨209550439756058595879824657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139700293170705730586549771 209550439756058595879824657)
    ·
      refine ⟨157162829817043946909868493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209550439756058595879824657 157162829817043946909868493)
      ·
        refine ⟨58936061181391480091200685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157162829817043946909868493 58936061181391480091200685)
        ·
          refine ⟨22101022943021805034200257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58936061181391480091200685 22101022943021805034200257)
          ·
            refine ⟨16575767207266353775650193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22101022943021805034200257 16575767207266353775650193)
            ·
              refine ⟨12431825405449765331737645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16575767207266353775650193 12431825405449765331737645)
              ·
                refine ⟨4661934527043661999401617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12431825405449765331737645 4661934527043661999401617)
                ·
                  refine ⟨3496450895282746499551213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661934527043661999401617 3496450895282746499551213)
                  ·
                    refine ⟨1311169085731029937331705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496450895282746499551213 1311169085731029937331705)
                    ·
                      rfl

theorem cell22_3830239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_3830239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830239 prefixEnd_3830239 := by exact prefixLift 3830239
  have htrace : WordTrace (prefixWord ++ tailWord_3830239) baseStart_3830239 baseEnd_3830239 := by
    simpa [prefixWord, tailWord_3830239, baseEnd_3830239] using wordTrace_append hprefix tailTrace_3830239
  have hstable : (prefixWord ++ tailWord_3830239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830239).length < 2 ^ (prefixWord ++ tailWord_3830239).sum := by decide
  have hdescent : baseEnd_3830239 < baseStart_3830239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830252 : List Nat := [2, 2, 1, 1, 2, 1, 7, 6]
def baseStart_3830252 : Nat := 118140960795 + 3830252 * 2 ^ 59
def prefixEnd_3830252 : Nat := 4983230072969 + 3 ^ 40 * 3830252 * 2
def baseEnd_3830252 : Nat := 145685948432966915195185

theorem tailTrace_3830252 : CollatzResearch.WordTrace tailWord_3830252 prefixEnd_3830252 145685948432966915195185 := by
  unfold tailWord_3830252
  simp only [CollatzResearch.WordTrace]
  refine ⟨69850383659829316903386505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93133844879772422537848673 69850383659829316903386505)
  ·
    refine ⟨52387787744871987677539879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69850383659829316903386505 52387787744871987677539879)
    ·
      refine ⟨78581681617307981516309819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52387787744871987677539879 78581681617307981516309819)
      ·
        refine ⟨117872522425961972274464729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78581681617307981516309819 117872522425961972274464729)
        ·
          refine ⟨88404391819471479205848547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117872522425961972274464729 88404391819471479205848547)
          ·
            refine ⟨132606587729207218808772821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88404391819471479205848547 132606587729207218808772821)
            ·
              refine ⟨3107966899903294190830613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132606587729207218808772821 3107966899903294190830613)
              ·
                refine ⟨145685948432966915195185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3107966899903294190830613 145685948432966915195185)
                ·
                  rfl

theorem cell22_3830252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 6].length) (baseStart_3830252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830252 prefixEnd_3830252 := by exact prefixLift 3830252
  have htrace : WordTrace (prefixWord ++ tailWord_3830252) baseStart_3830252 baseEnd_3830252 := by
    simpa [prefixWord, tailWord_3830252, baseEnd_3830252] using wordTrace_append hprefix tailTrace_3830252
  have hstable : (prefixWord ++ tailWord_3830252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830252).length < 2 ^ (prefixWord ++ tailWord_3830252).sum := by decide
  have hdescent : baseEnd_3830252 < baseStart_3830252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830254 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3830254 : Nat := 118140960795 + 3830254 * 2 ^ 59
def prefixEnd_3830254 : Nat := 4983230072969 + 3 ^ 40 * 3830254 * 2
def baseEnd_3830254 : Nat := 1311174220537574898206659

theorem tailTrace_3830254 : CollatzResearch.WordTrace tailWord_3830254 prefixEnd_3830254 1311174220537574898206659 := by
  unfold tailWord_3830254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17462605033206423518543227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93133893510434258765563877 17462605033206423518543227)
  ·
    refine ⟨26193907549809635277814841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17462605033206423518543227 26193907549809635277814841)
    ·
      refine ⟨19645430662357226458361131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26193907549809635277814841 19645430662357226458361131)
      ·
        refine ⟨29468145993535839687541697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19645430662357226458361131 29468145993535839687541697)
        ·
          refine ⟨22101109495151879765656273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29468145993535839687541697 22101109495151879765656273)
          ·
            refine ⟨16575832121363909824242205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22101109495151879765656273 16575832121363909824242205)
            ·
              refine ⟨6215937045511466184090827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16575832121363909824242205 6215937045511466184090827)
              ·
                refine ⟨9323905568267199276136241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215937045511466184090827 9323905568267199276136241)
                ·
                  refine ⟨6992929176200399457102181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9323905568267199276136241 6992929176200399457102181)
                  ·
                    refine ⟨1311174220537574898206659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6992929176200399457102181 1311174220537574898206659)
                    ·
                      rfl

theorem cell22_3830254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3830254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830254 prefixEnd_3830254 := by exact prefixLift 3830254
  have htrace : WordTrace (prefixWord ++ tailWord_3830254) baseStart_3830254 baseEnd_3830254 := by
    simpa [prefixWord, tailWord_3830254, baseEnd_3830254] using wordTrace_append hprefix tailTrace_3830254
  have hstable : (prefixWord ++ tailWord_3830254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830254).length < 2 ^ (prefixWord ++ tailWord_3830254).sum := by decide
  have hdescent : baseEnd_3830254 < baseStart_3830254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830284 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_3830284 : Nat := 118140960795 + 3830284 * 2 ^ 59
def prefixEnd_3830284 : Nat := 4983230072969 + 3 ^ 40 * 3830284 * 2
def baseEnd_3830284 : Nat := 1311184490150664819956567

theorem tailTrace_3830284 : CollatzResearch.WordTrace tailWord_3830284 prefixEnd_3830284 1311184490150664819956567 := by
  unfold tailWord_3830284
  simp only [CollatzResearch.WordTrace]
  refine ⟨69850967227771351635968953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93134622970361802181291937 69850967227771351635968953)
  ·
    refine ⟨52388225420828513726976715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69850967227771351635968953 52388225420828513726976715)
    ·
      refine ⟨78582338131242770590465073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52388225420828513726976715 78582338131242770590465073)
      ·
        refine ⟨58936753598432077942848805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78582338131242770590465073 58936753598432077942848805)
        ·
          refine ⟨11050641299706014614284151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58936753598432077942848805 11050641299706014614284151)
          ·
            refine ⟨16575961949559021921426227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11050641299706014614284151 16575961949559021921426227)
            ·
              refine ⟨24863942924338532882139341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575961949559021921426227 24863942924338532882139341)
              ·
                refine ⟨9323978596626949830802253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24863942924338532882139341 9323978596626949830802253)
                ·
                  refine ⟨3496491973735106186550845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9323978596626949830802253 3496491973735106186550845)
                  ·
                    refine ⟨1311184490150664819956567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496491973735106186550845 1311184490150664819956567)
                    ·
                      rfl

theorem cell22_3830284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_3830284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830284 prefixEnd_3830284 := by exact prefixLift 3830284
  have htrace : WordTrace (prefixWord ++ tailWord_3830284) baseStart_3830284 baseEnd_3830284 := by
    simpa [prefixWord, tailWord_3830284, baseEnd_3830284] using wordTrace_append hprefix tailTrace_3830284
  have hstable : (prefixWord ++ tailWord_3830284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830284).length < 2 ^ (prefixWord ++ tailWord_3830284).sum := by decide
  have hdescent : baseEnd_3830284 < baseStart_3830284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830393 : List Nat := [1, 2, 1, 3, 3, 4, 2, 2, 4]
def baseStart_3830393 : Nat := 118140960795 + 3830393 * 2 ^ 59
def prefixEnd_3830393 : Nat := 4983230072969 + 3 ^ 40 * 3830393 * 2
def baseEnd_3830393 : Nat := 437073934359408289660411

theorem tailTrace_3830393 : CollatzResearch.WordTrace tailWord_3830393 prefixEnd_3830393 437073934359408289660411 := by
  unfold tailWord_3830393
  simp only [CollatzResearch.WordTrace]
  refine ⟨139705910012147814887655833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93137273341431876591770555 139705910012147814887655833)
  ·
    refine ⟨104779432509110861165741875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139705910012147814887655833 104779432509110861165741875)
    ·
      refine ⟨157169148763666291748612813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104779432509110861165741875 157169148763666291748612813)
      ·
        refine ⟨58938430786374859405729805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157169148763666291748612813 58938430786374859405729805)
        ·
          refine ⟨22101911544890572277148677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58938430786374859405729805 22101911544890572277148677)
          ·
            refine ⟨4144108414666982301965377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22101911544890572277148677 4144108414666982301965377)
            ·
              refine ⟨3108081311000236726474033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4144108414666982301965377 3108081311000236726474033)
              ·
                refine ⟨2331060983250177544855525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3108081311000236726474033 2331060983250177544855525)
                ·
                  refine ⟨437073934359408289660411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2331060983250177544855525 437073934359408289660411)
                  ·
                    rfl

theorem cell22_3830393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 4].length) (baseStart_3830393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830393 prefixEnd_3830393 := by exact prefixLift 3830393
  have htrace : WordTrace (prefixWord ++ tailWord_3830393) baseStart_3830393 baseEnd_3830393 := by
    simpa [prefixWord, tailWord_3830393, baseEnd_3830393] using wordTrace_append hprefix tailTrace_3830393
  have hstable : (prefixWord ++ tailWord_3830393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830393).length < 2 ^ (prefixWord ++ tailWord_3830393).sum := by decide
  have hdescent : baseEnd_3830393 < baseStart_3830393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830404 : List Nat := [2, 3, 2, 1, 3, 1, 3, 7]
def baseStart_3830404 : Nat := 118140960795 + 3830404 * 2 ^ 59
def prefixEnd_3830404 : Nat := 4983230072969 + 3 ^ 40 * 3830404 * 2
def baseEnd_3830404 : Nat := 145691729844780500772911

theorem tailTrace_3830404 : CollatzResearch.WordTrace tailWord_3830404 prefixEnd_3830404 145691729844780500772911 := by
  unfold tailWord_3830404
  simp only [CollatzResearch.WordTrace]
  refine ⟨69853155607553981883153133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93137540810071975844204177 69853155607553981883153133)
  ·
    refine ⟨26194933352832743206182425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69853155607553981883153133 26194933352832743206182425)
    ·
      refine ⟨19646200014624557404636819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26194933352832743206182425 19646200014624557404636819)
      ·
        refine ⟨29469300021936836106955229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19646200014624557404636819 29469300021936836106955229)
        ·
          refine ⟨11050987508226313540108211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29469300021936836106955229 11050987508226313540108211)
          ·
            refine ⟨16576481262339470310162317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11050987508226313540108211 16576481262339470310162317)
            ·
              refine ⟨6216180473377301366310869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16576481262339470310162317 6216180473377301366310869)
              ·
                refine ⟨145691729844780500772911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6216180473377301366310869 145691729844780500772911)
                ·
                  rfl

theorem cell22_3830404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 7].length) (baseStart_3830404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830404 prefixEnd_3830404 := by exact prefixLift 3830404
  have htrace : WordTrace (prefixWord ++ tailWord_3830404) baseStart_3830404 baseEnd_3830404 := by
    simpa [prefixWord, tailWord_3830404, baseEnd_3830404] using wordTrace_append hprefix tailTrace_3830404
  have hstable : (prefixWord ++ tailWord_3830404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830404).length < 2 ^ (prefixWord ++ tailWord_3830404).sum := by decide
  have hdescent : baseEnd_3830404 < baseStart_3830404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830419 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 3, 3]
def baseStart_3830419 : Nat := 118140960795 + 3830419 * 2 ^ 59
def prefixEnd_3830419 : Nat := 4983230072969 + 3 ^ 40 * 3830419 * 2
def baseEnd_3830419 : Nat := 1311230703409569467831153

theorem tailTrace_3830419 : CollatzResearch.WordTrace tailWord_3830419 prefixEnd_3830419 1311230703409569467831153 := by
  unfold tailWord_3830419
  simp only [CollatzResearch.WordTrace]
  refine ⟨139706858310053621328102311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93137905540035747552068207 139706858310053621328102311)
  ·
    refine ⟨209560287465080431992153467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139706858310053621328102311 209560287465080431992153467)
    ·
      refine ⟨314340431197620647988230201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209560287465080431992153467 314340431197620647988230201)
      ·
        refine ⟨235755323398215485991172651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314340431197620647988230201 235755323398215485991172651)
        ·
          refine ⟨353632985097323228986758977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235755323398215485991172651 353632985097323228986758977)
          ·
            refine ⟨265224738822992421740069233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353632985097323228986758977 265224738822992421740069233)
            ·
              refine ⟨198918554117244316305051925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265224738822992421740069233 198918554117244316305051925)
              ·
                refine ⟨9324307224245827326799309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198918554117244316305051925 9324307224245827326799309)
                ·
                  refine ⟨3496615209092185247549741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9324307224245827326799309 3496615209092185247549741)
                  ·
                    refine ⟨1311230703409569467831153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496615209092185247549741 1311230703409569467831153)
                    ·
                      rfl

theorem cell22_3830419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 3].length) (baseStart_3830419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830419 prefixEnd_3830419 := by exact prefixLift 3830419
  have htrace : WordTrace (prefixWord ++ tailWord_3830419) baseStart_3830419 baseEnd_3830419 := by
    simpa [prefixWord, tailWord_3830419, baseEnd_3830419] using wordTrace_append hprefix tailTrace_3830419
  have hstable : (prefixWord ++ tailWord_3830419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830419).length < 2 ^ (prefixWord ++ tailWord_3830419).sum := by decide
  have hdescent : baseEnd_3830419 < baseStart_3830419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830442 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3830442 : Nat := 118140960795 + 3830442 * 2 ^ 59
def prefixEnd_3830442 : Nat := 4983230072969 + 3 ^ 40 * 3830442 * 2
def baseEnd_3830442 : Nat := 1311238576779605074506083

theorem tailTrace_3830442 : CollatzResearch.WordTrace tailWord_3830442 prefixEnd_3830442 1311238576779605074506083 := by
  unfold tailWord_3830442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34926924297242574064047395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93138464792646864170793053 34926924297242574064047395)
  ·
    refine ⟨52390386445863861096071093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34926924297242574064047395 52390386445863861096071093)
    ·
      refine ⟨4911598729299736977756665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52390386445863861096071093 4911598729299736977756665)
      ·
        refine ⟨3683699046974802733317499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4911598729299736977756665 3683699046974802733317499)
        ·
          refine ⟨5525548570462204099976249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683699046974802733317499 5525548570462204099976249)
          ·
            refine ⟨4144161427846653074982187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5525548570462204099976249 4144161427846653074982187)
            ·
              refine ⟨6216242141769979612473281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144161427846653074982187 6216242141769979612473281)
              ·
                refine ⟨4662181606327484709354961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6216242141769979612473281 4662181606327484709354961)
                ·
                  refine ⟨3496636204745613532016221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4662181606327484709354961 3496636204745613532016221)
                  ·
                    refine ⟨1311238576779605074506083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496636204745613532016221 1311238576779605074506083)
                    ·
                      rfl

theorem cell22_3830442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3830442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830442 prefixEnd_3830442 := by exact prefixLift 3830442
  have htrace : WordTrace (prefixWord ++ tailWord_3830442) baseStart_3830442 baseEnd_3830442 := by
    simpa [prefixWord, tailWord_3830442, baseEnd_3830442] using wordTrace_append hprefix tailTrace_3830442
  have hstable : (prefixWord ++ tailWord_3830442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830442).length < 2 ^ (prefixWord ++ tailWord_3830442).sum := by decide
  have hdescent : baseEnd_3830442 < baseStart_3830442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830453 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_3830453 : Nat := 118140960795 + 3830453 * 2 ^ 59
def prefixEnd_3830453 : Nat := 4983230072969 + 3 ^ 40 * 3830453 * 2
def baseEnd_3830453 : Nat := 1311242342304404712481049

theorem tailTrace_3830453 : CollatzResearch.WordTrace tailWord_3830453 prefixEnd_3830453 1311242342304404712481049 := by
  unfold tailWord_3830453
  simp only [CollatzResearch.WordTrace]
  refine ⟨139708098391930445134840013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93138732261286963423226675 139708098391930445134840013)
  ·
    refine ⟨52390536896973916925565005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139708098391930445134840013 52390536896973916925565005)
    ·
      refine ⟨19646451336365218847086877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52390536896973916925565005 19646451336365218847086877)
      ·
        refine ⟨7367419251136957067657579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19646451336365218847086877 7367419251136957067657579)
        ·
          refine ⟨11051128876705435601486369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7367419251136957067657579 11051128876705435601486369)
          ·
            refine ⟨8288346657529076701114777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11051128876705435601486369 8288346657529076701114777)
            ·
              refine ⟨6216259993146807525836083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8288346657529076701114777 6216259993146807525836083)
              ·
                refine ⟨9324389989720211288754125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216259993146807525836083 9324389989720211288754125)
                ·
                  refine ⟨3496646246145079233282797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9324389989720211288754125 3496646246145079233282797)
                  ·
                    refine ⟨1311242342304404712481049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496646246145079233282797 1311242342304404712481049)
                    ·
                      rfl

theorem cell22_3830453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_3830453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830453 prefixEnd_3830453 := by exact prefixLift 3830453
  have htrace : WordTrace (prefixWord ++ tailWord_3830453) baseStart_3830453 baseEnd_3830453 := by
    simpa [prefixWord, tailWord_3830453, baseEnd_3830453] using wordTrace_append hprefix tailTrace_3830453
  have hstable : (prefixWord ++ tailWord_3830453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830453).length < 2 ^ (prefixWord ++ tailWord_3830453).sum := by decide
  have hdescent : baseEnd_3830453 < baseStart_3830453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830464 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_3830464 : Nat := 118140960795 + 3830464 * 2 ^ 59
def prefixEnd_3830464 : Nat := 4983230072969 + 3 ^ 40 * 3830464 * 2
def baseEnd_3830464 : Nat := 1311246107829204350456015

theorem tailTrace_3830464 : CollatzResearch.WordTrace tailWord_3830464 prefixEnd_3830464 1311246107829204350456015 := by
  unfold tailWord_3830464
  simp only [CollatzResearch.WordTrace]
  refine ⟨69854249797445297006745223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93138999729927062675660297 69854249797445297006745223)
  ·
    refine ⟨104781374696167945510117835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69854249797445297006745223 104781374696167945510117835)
    ·
      refine ⟨157172062044251918265176753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104781374696167945510117835 157172062044251918265176753)
      ·
        refine ⟨117879046533188938698882565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157172062044251918265176753 117879046533188938698882565)
        ·
          refine ⟨22102321224972926006040481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117879046533188938698882565 22102321224972926006040481)
          ·
            refine ⟨16576740918729694504530361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22102321224972926006040481 16576740918729694504530361)
            ·
              refine ⟨12432555689047270878397771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16576740918729694504530361 12432555689047270878397771)
              ·
                refine ⟨18648833533570906317596657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12432555689047270878397771 18648833533570906317596657)
                ·
                  refine ⟨13986625150178179738197493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18648833533570906317596657 13986625150178179738197493)
                  ·
                    refine ⟨1311246107829204350456015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13986625150178179738197493 1311246107829204350456015)
                    ·
                      rfl

theorem cell22_3830464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_3830464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830464 prefixEnd_3830464 := by exact prefixLift 3830464
  have htrace : WordTrace (prefixWord ++ tailWord_3830464) baseStart_3830464 baseEnd_3830464 := by
    simpa [prefixWord, tailWord_3830464, baseEnd_3830464] using wordTrace_append hprefix tailTrace_3830464
  have hstable : (prefixWord ++ tailWord_3830464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830464).length < 2 ^ (prefixWord ++ tailWord_3830464).sum := by decide
  have hdescent : baseEnd_3830464 < baseStart_3830464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830511 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 6]
def baseStart_3830511 : Nat := 118140960795 + 3830511 * 2 ^ 59
def prefixEnd_3830511 : Nat := 4983230072969 + 3 ^ 40 * 3830511 * 2
def baseEnd_3830511 : Nat := 437087398963237298176957

theorem tailTrace_3830511 : CollatzResearch.WordTrace tailWord_3830511 prefixEnd_3830511 437087398963237298176957 := by
  unfold tailWord_3830511
  simp only [CollatzResearch.WordTrace]
  refine ⟨139710213825720321040451387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93140142550480214026967591 139710213825720321040451387)
  ·
    refine ⟨209565320738580481560677081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139710213825720321040451387 209565320738580481560677081)
    ·
      refine ⟨157173990553935361170507811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209565320738580481560677081 157173990553935361170507811)
      ·
        refine ⟨235760985830903041755761717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157173990553935361170507811 235760985830903041755761717)
        ·
          refine ⟨22102592421647160164602661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235760985830903041755761717 22102592421647160164602661)
          ·
            refine ⟨4144236079058842530862999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22102592421647160164602661 4144236079058842530862999)
            ·
              refine ⟨6216354118588263796294499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144236079058842530862999 6216354118588263796294499)
              ·
                refine ⟨9324531177882395694441749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216354118588263796294499 9324531177882395694441749)
                ·
                  refine ⟨437087398963237298176957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9324531177882395694441749 437087398963237298176957)
                  ·
                    rfl

theorem cell22_3830511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 6].length) (baseStart_3830511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830511 prefixEnd_3830511 := by exact prefixLift 3830511
  have htrace : WordTrace (prefixWord ++ tailWord_3830511) baseStart_3830511 baseEnd_3830511 := by
    simpa [prefixWord, tailWord_3830511, baseEnd_3830511] using wordTrace_append hprefix tailTrace_3830511
  have hstable : (prefixWord ++ tailWord_3830511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830511).length < 2 ^ (prefixWord ++ tailWord_3830511).sum := by decide
  have hdescent : baseEnd_3830511 < baseStart_3830511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830530 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3830530 : Nat := 118140960795 + 3830530 * 2 ^ 59
def prefixEnd_3830530 : Nat := 4983230072969 + 3 ^ 40 * 3830530 * 2
def baseEnd_3830530 : Nat := 1311268700978002178305813

theorem tailTrace_3830530 : CollatzResearch.WordTrace tailWord_3830530 prefixEnd_3830530 1311268700978002178305813 := by
  unfold tailWord_3830530
  simp only [CollatzResearch.WordTrace]
  refine ⟨34927726703162871821348261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93140604541767658190262029 34927726703162871821348261)
  ·
    refine ⟨6548948756843038466502799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34927726703162871821348261 6548948756843038466502799)
    ·
      refine ⟨9823423135264557699754199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6548948756843038466502799 9823423135264557699754199)
      ·
        refine ⟨14735134702896836549631299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9823423135264557699754199 14735134702896836549631299)
        ·
          refine ⟨22102702054345254824446949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14735134702896836549631299 22102702054345254824446949)
          ·
            refine ⟨4144256635189735279583803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22102702054345254824446949 4144256635189735279583803)
            ·
              refine ⟨6216384952784602919375705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144256635189735279583803 6216384952784602919375705)
              ·
                refine ⟨4662288714588452189531779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6216384952784602919375705 4662288714588452189531779)
                ·
                  refine ⟨6993433071882678284297669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4662288714588452189531779 6993433071882678284297669)
                  ·
                    refine ⟨1311268700978002178305813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6993433071882678284297669 1311268700978002178305813)
                    ·
                      rfl

theorem cell22_3830530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3830530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830530 prefixEnd_3830530 := by exact prefixLift 3830530
  have htrace : WordTrace (prefixWord ++ tailWord_3830530) baseStart_3830530 baseEnd_3830530 := by
    simpa [prefixWord, tailWord_3830530, baseEnd_3830530] using wordTrace_append hprefix tailTrace_3830530
  have hstable : (prefixWord ++ tailWord_3830530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830530).length < 2 ^ (prefixWord ++ tailWord_3830530).sum := by decide
  have hdescent : baseEnd_3830530 < baseStart_3830530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830599 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3830599 : Nat := 118140960795 + 3830599 * 2 ^ 59
def prefixEnd_3830599 : Nat := 4983230072969 + 3 ^ 40 * 3830599 * 2
def baseEnd_3830599 : Nat := 1311292321088108998330601

theorem tailTrace_3830599 : CollatzResearch.WordTrace tailWord_3830599 prefixEnd_3830599 1311292321088108998330601 := by
  unfold tailWord_3830599
  simp only [CollatzResearch.WordTrace]
  refine ⟨139713423449401512069654851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93142282299601008046436567 139713423449401512069654851)
  ·
    refine ⟨209570135174102268104482277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139713423449401512069654851 209570135174102268104482277)
    ·
      refine ⟨39294400345144175269590427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209570135174102268104482277 39294400345144175269590427)
      ·
        refine ⟨58941600517716262904385641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39294400345144175269590427 58941600517716262904385641)
        ·
          refine ⟨44206200388287197178289231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58941600517716262904385641 44206200388287197178289231)
          ·
            refine ⟨66309300582430795767433847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44206200388287197178289231 66309300582430795767433847)
            ·
              refine ⟨99463950873646193651150771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66309300582430795767433847 99463950873646193651150771)
              ·
                refine ⟨149195926310469290476726157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99463950873646193651150771 149195926310469290476726157)
                ·
                  refine ⟨55948472366425983928772309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149195926310469290476726157 55948472366425983928772309)
                  ·
                    refine ⟨1311292321088108998330601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55948472366425983928772309 1311292321088108998330601)
                    ·
                      rfl

theorem cell22_3830599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3830599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830599 prefixEnd_3830599 := by exact prefixLift 3830599
  have htrace : WordTrace (prefixWord ++ tailWord_3830599) baseStart_3830599 baseEnd_3830599 := by
    simpa [prefixWord, tailWord_3830599, baseEnd_3830599] using wordTrace_append hprefix tailTrace_3830599
  have hstable : (prefixWord ++ tailWord_3830599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830599).length < 2 ^ (prefixWord ++ tailWord_3830599).sum := by decide
  have hdescent : baseEnd_3830599 < baseStart_3830599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830618 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_3830618 : Nat := 118140960795 + 3830618 * 2 ^ 59
def prefixEnd_3830618 : Nat := 4983230072969 + 3 ^ 40 * 3830618 * 2
def baseEnd_3830618 : Nat := 437099608392133094035181

theorem tailTrace_3830618 : CollatzResearch.WordTrace tailWord_3830618 prefixEnd_3830618 437099608392133094035181 := by
  unfold tailWord_3830618
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928529109083169578649127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93142744290888452209731005 34928529109083169578649127)
  ·
    refine ⟨52392793663624754367973691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34928529109083169578649127 52392793663624754367973691)
    ·
      refine ⟨78589190495437131551960537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52392793663624754367973691 78589190495437131551960537)
      ·
        refine ⟨58941892871577848663970403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78589190495437131551960537 58941892871577848663970403)
        ·
          refine ⟨88412839307366772995955605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58941892871577848663970403 88412839307366772995955605)
          ·
            refine ⟨4144351842532817484185419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88412839307366772995955605 4144351842532817484185419)
            ·
              refine ⟨6216527763799226226278129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144351842532817484185419 6216527763799226226278129)
              ·
                refine ⟨4662395822849419669708597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6216527763799226226278129 4662395822849419669708597)
                ·
                  refine ⟨437099608392133094035181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4662395822849419669708597 437099608392133094035181)
                  ·
                    rfl

theorem cell22_3830618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_3830618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830618 prefixEnd_3830618 := by exact prefixLift 3830618
  have htrace : WordTrace (prefixWord ++ tailWord_3830618) baseStart_3830618 baseEnd_3830618 := by
    simpa [prefixWord, tailWord_3830618, baseEnd_3830618] using wordTrace_append hprefix tailTrace_3830618
  have hstable : (prefixWord ++ tailWord_3830618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830618).length < 2 ^ (prefixWord ++ tailWord_3830618).sum := by decide
  have hdescent : baseEnd_3830618 < baseStart_3830618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830738 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3830738 : Nat := 118140960795 + 3830738 * 2 ^ 59
def prefixEnd_3830738 : Nat := 4983230072969 + 3 ^ 40 * 3830738 * 2
def baseEnd_3830738 : Nat := 1311339903628758969105175

theorem tailTrace_3830738 : CollatzResearch.WordTrace tailWord_3830738 prefixEnd_3830738 1311339903628758969105175 := by
  unfold tailWord_3830738
  simp only [CollatzResearch.WordTrace]
  refine ⟨34929623298974484702241217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93145662130598625872643245 34929623298974484702241217)
  ·
    refine ⟨26197217474230863526680913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34929623298974484702241217 26197217474230863526680913)
    ·
      refine ⟨19647913105673147645010685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26197217474230863526680913 19647913105673147645010685)
      ·
        refine ⟨7367967414627430366879007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19647913105673147645010685 7367967414627430366879007)
        ·
          refine ⟨11051951121941145550318511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7367967414627430366879007 11051951121941145550318511)
          ·
            refine ⟨16577926682911718325477767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11051951121941145550318511 16577926682911718325477767)
            ·
              refine ⟨24866890024367577488216651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16577926682911718325477767 24866890024367577488216651)
              ·
                refine ⟨37300335036551366232324977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24866890024367577488216651 37300335036551366232324977)
                ·
                  refine ⟨27975251277413524674243733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37300335036551366232324977 27975251277413524674243733)
                  ·
                    refine ⟨1311339903628758969105175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27975251277413524674243733 1311339903628758969105175)
                    ·
                      rfl

theorem cell22_3830738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3830738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830738 prefixEnd_3830738 := by exact prefixLift 3830738
  have htrace : WordTrace (prefixWord ++ tailWord_3830738) baseStart_3830738 baseEnd_3830738 := by
    simpa [prefixWord, tailWord_3830738, baseEnd_3830738] using wordTrace_append hprefix tailTrace_3830738
  have hstable : (prefixWord ++ tailWord_3830738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830738).length < 2 ^ (prefixWord ++ tailWord_3830738).sum := by decide
  have hdescent : baseEnd_3830738 < baseStart_3830738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830757 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_3830757 : Nat := 118140960795 + 3830757 * 2 ^ 59
def prefixEnd_3830757 : Nat := 4983230072969 + 3 ^ 40 * 3830757 * 2
def baseEnd_3830757 : Nat := 1311346407717049252880117

theorem tailTrace_3830757 : CollatzResearch.WordTrace tailWord_3830757 prefixEnd_3830757 1311346407717049252880117 := by
  unfold tailWord_3830757
  simp only [CollatzResearch.WordTrace]
  refine ⟨139719186182829105053906525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93146124121886070035937683 139719186182829105053906525)
  ·
    refine ⟨52394694818560914395214947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139719186182829105053906525 52394694818560914395214947)
    ·
      refine ⟨78592042227841371592822421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52394694818560914395214947 78592042227841371592822421)
      ·
        refine ⟨3684001979430064293413551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78592042227841371592822421 3684001979430064293413551)
        ·
          refine ⟨5526002969145096440120327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684001979430064293413551 5526002969145096440120327)
          ·
            refine ⟨8289004453717644660180491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526002969145096440120327 8289004453717644660180491)
            ·
              refine ⟨12433506680576466990270737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8289004453717644660180491 12433506680576466990270737)
              ·
                refine ⟨9325130010432350242703053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12433506680576466990270737 9325130010432350242703053)
                ·
                  refine ⟨3496923753912131341013645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9325130010432350242703053 3496923753912131341013645)
                  ·
                    refine ⟨1311346407717049252880117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496923753912131341013645 1311346407717049252880117)
                    ·
                      rfl

theorem cell22_3830757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_3830757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830757 prefixEnd_3830757 := by exact prefixLift 3830757
  have htrace : WordTrace (prefixWord ++ tailWord_3830757) baseStart_3830757 baseEnd_3830757 := by
    simpa [prefixWord, tailWord_3830757, baseEnd_3830757] using wordTrace_append hprefix tailTrace_3830757
  have hstable : (prefixWord ++ tailWord_3830757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830757).length < 2 ^ (prefixWord ++ tailWord_3830757).sum := by decide
  have hdescent : baseEnd_3830757 < baseStart_3830757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830774 : List Nat := [5, 1, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_3830774 : Nat := 118140960795 + 3830774 * 2 ^ 59
def prefixEnd_3830774 : Nat := 4983230072969 + 3 ^ 40 * 3830774 * 2
def baseEnd_3830774 : Nat := 1311352227164466875205065

theorem tailTrace_3830774 : CollatzResearch.WordTrace tailWord_3830774 prefixEnd_3830774 1311352227164466875205065 := by
  unfold tailWord_3830774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8732487888985469809829711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93146537482511677971516917 8732487888985469809829711)
  ·
    refine ⟨13098731833478204714744567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8732487888985469809829711 13098731833478204714744567)
    ·
      refine ⟨19648097750217307072116851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13098731833478204714744567 19648097750217307072116851)
      ·
        refine ⟨29472146625325960608175277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19648097750217307072116851 29472146625325960608175277)
        ·
          refine ⟨11052054984497235228065729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29472146625325960608175277 11052054984497235228065729)
          ·
            refine ⟨8289041238372926421049297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11052054984497235228065729 8289041238372926421049297)
            ·
              refine ⟨6216780928779694815786973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8289041238372926421049297 6216780928779694815786973)
              ·
                refine ⟨2331292848292385555920115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6216780928779694815786973 2331292848292385555920115)
                ·
                  refine ⟨3496939272438578333880173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331292848292385555920115 3496939272438578333880173)
                  ·
                    refine ⟨1311352227164466875205065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496939272438578333880173 1311352227164466875205065)
                    ·
                      rfl

theorem cell22_3830774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_3830774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830774 prefixEnd_3830774 := by exact prefixLift 3830774
  have htrace : WordTrace (prefixWord ++ tailWord_3830774) baseStart_3830774 baseEnd_3830774 := by
    simpa [prefixWord, tailWord_3830774, baseEnd_3830774] using wordTrace_append hprefix tailTrace_3830774
  have hstable : (prefixWord ++ tailWord_3830774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830774).length < 2 ^ (prefixWord ++ tailWord_3830774).sum := by decide
  have hdescent : baseEnd_3830774 < baseStart_3830774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830781 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 10]
def baseStart_3830781 : Nat := 118140960795 + 3830781 * 2 ^ 59
def prefixEnd_3830781 : Nat := 4983230072969 + 3 ^ 40 * 3830781 * 2
def baseEnd_3830781 : Nat := 437118207802507063426681

theorem tailTrace_3830781 : CollatzResearch.WordTrace tailWord_3830781 prefixEnd_3830781 437118207802507063426681 := by
  unfold tailWord_3830781
  simp only [CollatzResearch.WordTrace]
  refine ⟨139720061534742157152780197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93146707689828104768520131 139720061534742157152780197)
  ·
    refine ⟨26197511537764154466146287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139720061534742157152780197 26197511537764154466146287)
    ·
      refine ⟨39296267306646231699219431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26197511537764154466146287 39296267306646231699219431)
      ·
        refine ⟨58944400959969347548829147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39296267306646231699219431 58944400959969347548829147)
        ·
          refine ⟨88416601439954021323243721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58944400959969347548829147 88416601439954021323243721)
          ·
            refine ⟨66312451079965515992432791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88416601439954021323243721 66312451079965515992432791)
            ·
              refine ⟨99468676619948273988649187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66312451079965515992432791 99468676619948273988649187)
              ·
                refine ⟨149203014929922410982973781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99468676619948273988649187 149203014929922410982973781)
                ·
                  refine ⟨437118207802507063426681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149203014929922410982973781 437118207802507063426681)
                  ·
                    rfl

theorem cell22_3830781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_3830781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830781 prefixEnd_3830781 := by exact prefixLift 3830781
  have htrace : WordTrace (prefixWord ++ tailWord_3830781) baseStart_3830781 baseEnd_3830781 := by
    simpa [prefixWord, tailWord_3830781, baseEnd_3830781] using wordTrace_append hprefix tailTrace_3830781
  have hstable : (prefixWord ++ tailWord_3830781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830781).length < 2 ^ (prefixWord ++ tailWord_3830781).sum := by decide
  have hdescent : baseEnd_3830781 < baseStart_3830781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830798 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_3830798 : Nat := 118140960795 + 3830798 * 2 ^ 59
def prefixEnd_3830798 : Nat := 4983230072969 + 3 ^ 40 * 3830798 * 2
def baseEnd_3830798 : Nat := 437120147618312937534997

theorem tailTrace_3830798 : CollatzResearch.WordTrace tailWord_3830798 prefixEnd_3830798 437120147618312937534997 := by
  unfold tailWord_3830798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17465085196960071132018631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93147121050453712704099365 17465085196960071132018631)
  ·
    refine ⟨26197627795440106698027947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17465085196960071132018631 26197627795440106698027947)
    ·
      refine ⟨39296441693160160047041921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26197627795440106698027947 39296441693160160047041921)
      ·
        refine ⟨29472331269870120035281441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39296441693160160047041921 29472331269870120035281441)
        ·
          refine ⟨22104248452402590026461081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29472331269870120035281441 22104248452402590026461081)
          ·
            refine ⟨16578186339301942519845811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22104248452402590026461081 16578186339301942519845811)
            ·
              refine ⟨24867279508952913779768717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16578186339301942519845811 24867279508952913779768717)
              ·
                refine ⟨9325229815857342667413269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24867279508952913779768717 9325229815857342667413269)
                ·
                  refine ⟨437120147618312937534997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9325229815857342667413269 437120147618312937534997)
                  ·
                    rfl

theorem cell22_3830798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_3830798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830798 prefixEnd_3830798 := by exact prefixLift 3830798
  have htrace : WordTrace (prefixWord ++ tailWord_3830798) baseStart_3830798 baseEnd_3830798 := by
    simpa [prefixWord, tailWord_3830798, baseEnd_3830798] using wordTrace_append hprefix tailTrace_3830798
  have hstable : (prefixWord ++ tailWord_3830798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830798).length < 2 ^ (prefixWord ++ tailWord_3830798).sum := by decide
  have hdescent : baseEnd_3830798 < baseStart_3830798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830828 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_3830828 : Nat := 118140960795 + 3830828 * 2 ^ 59
def prefixEnd_3830828 : Nat := 4983230072969 + 3 ^ 40 * 3830828 * 2
def baseEnd_3830828 : Nat := 1311370712468028734354899

theorem tailTrace_3830828 : CollatzResearch.WordTrace tailWord_3830828 prefixEnd_3830828 1311370712468028734354899 := by
  unfold tailWord_3830828
  simp only [CollatzResearch.WordTrace]
  refine ⟨69860887882785942089870569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93147850510381256119827425 69860887882785942089870569)
  ·
    refine ⟨52395665912089456567402927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69860887882785942089870569 52395665912089456567402927)
    ·
      refine ⟨78593498868134184851104391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52395665912089456567402927 78593498868134184851104391)
      ·
        refine ⟨117890248302201277276656587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78593498868134184851104391 117890248302201277276656587)
        ·
          refine ⟨176835372453301915914984881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117890248302201277276656587 176835372453301915914984881)
          ·
            refine ⟨132626529339976436936238661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176835372453301915914984881 132626529339976436936238661)
            ·
              refine ⟨24867474251245581925544749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132626529339976436936238661 24867474251245581925544749)
              ·
                refine ⟨9325302844217093222079281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24867474251245581925544749 9325302844217093222079281)
                ·
                  refine ⟨6993977133162819916559461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9325302844217093222079281 6993977133162819916559461)
                  ·
                    refine ⟨1311370712468028734354899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6993977133162819916559461 1311370712468028734354899)
                    ·
                      rfl

theorem cell22_3830828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_3830828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830828 prefixEnd_3830828 := by exact prefixLift 3830828
  have htrace : WordTrace (prefixWord ++ tailWord_3830828) baseStart_3830828 baseEnd_3830828 := by
    simpa [prefixWord, tailWord_3830828, baseEnd_3830828] using wordTrace_append hprefix tailTrace_3830828
  have hstable : (prefixWord ++ tailWord_3830828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830828).length < 2 ^ (prefixWord ++ tailWord_3830828).sum := by decide
  have hdescent : baseEnd_3830828 < baseStart_3830828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830830 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3830830 : Nat := 118140960795 + 3830830 * 2 ^ 59
def prefixEnd_3830830 : Nat := 4983230072969 + 3 ^ 40 * 3830830 * 2
def baseEnd_3830830 : Nat := 1311371397108901395804893

theorem tailTrace_3830830 : CollatzResearch.WordTrace tailWord_3830830 prefixEnd_3830830 1311371397108901395804893 := by
  unfold tailWord_3830830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17465231088945579815164243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93147899141043092347542629 17465231088945579815164243)
  ·
    refine ⟨26197846633418369722746365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17465231088945579815164243 26197846633418369722746365)
    ·
      refine ⟨9824192487531888646029887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26197846633418369722746365 9824192487531888646029887)
      ·
        refine ⟨14736288731297832969044831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9824192487531888646029887 14736288731297832969044831)
        ·
          refine ⟨22104433096946749453567247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14736288731297832969044831 22104433096946749453567247)
          ·
            refine ⟨33156649645420124180350871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22104433096946749453567247 33156649645420124180350871)
            ·
              refine ⟨49734974468130186270526307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33156649645420124180350871 49734974468130186270526307)
              ·
                refine ⟨74602461702195279405789461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49734974468130186270526307 74602461702195279405789461)
                ·
                  refine ⟨3496990392290403722146381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74602461702195279405789461 3496990392290403722146381)
                  ·
                    refine ⟨1311371397108901395804893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3496990392290403722146381 1311371397108901395804893)
                    ·
                      rfl

theorem cell22_3830830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3830830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830830 prefixEnd_3830830 := by exact prefixLift 3830830
  have htrace : WordTrace (prefixWord ++ tailWord_3830830) baseStart_3830830 baseEnd_3830830 := by
    simpa [prefixWord, tailWord_3830830, baseEnd_3830830] using wordTrace_append hprefix tailTrace_3830830
  have hstable : (prefixWord ++ tailWord_3830830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830830).length < 2 ^ (prefixWord ++ tailWord_3830830).sum := by decide
  have hdescent : baseEnd_3830830 < baseStart_3830830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830845 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3830845 : Nat := 118140960795 + 3830845 * 2 ^ 59
def prefixEnd_3830845 : Nat := 4983230072969 + 3 ^ 40 * 3830845 * 2
def baseEnd_3830845 : Nat := 1311376531915446356679847

theorem tailTrace_3830845 : CollatzResearch.WordTrace tailWord_3830845 prefixEnd_3830845 1311376531915446356679847 := by
  unfold tailWord_3830845
  simp only [CollatzResearch.WordTrace]
  refine ⟨139722395806510296083109989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93148263871006864055406659 139722395806510296083109989)
  ·
    refine ⟨26197949213720680515583123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139722395806510296083109989 26197949213720680515583123)
    ·
      refine ⟨39296923820581020773374685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26197949213720680515583123 39296923820581020773374685)
      ·
        refine ⟨14736346432717882790015507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39296923820581020773374685 14736346432717882790015507)
        ·
          refine ⟨22104519649076824185023261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14736346432717882790015507 22104519649076824185023261)
          ·
            refine ⟨8289194868403809069383723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22104519649076824185023261 8289194868403809069383723)
            ·
              refine ⟨12433792302605713604075585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8289194868403809069383723 12433792302605713604075585)
              ·
                refine ⟨9325344226954285203056689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12433792302605713604075585 9325344226954285203056689)
                ·
                  refine ⟨6994008170215713902292517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9325344226954285203056689 6994008170215713902292517)
                  ·
                    refine ⟨1311376531915446356679847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6994008170215713902292517 1311376531915446356679847)
                    ·
                      rfl

theorem cell22_3830845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3830845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830845 prefixEnd_3830845 := by exact prefixLift 3830845
  have htrace : WordTrace (prefixWord ++ tailWord_3830845) baseStart_3830845 baseEnd_3830845 := by
    simpa [prefixWord, tailWord_3830845, baseEnd_3830845] using wordTrace_append hprefix tailTrace_3830845
  have hstable : (prefixWord ++ tailWord_3830845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830845).length < 2 ^ (prefixWord ++ tailWord_3830845).sum := by decide
  have hdescent : baseEnd_3830845 < baseStart_3830845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830849 : List Nat := [1, 2, 5, 1, 3, 1, 3, 2, 4]
def baseStart_3830849 : Nat := 118140960795 + 3830849 * 2 ^ 59
def prefixEnd_3830849 : Nat := 4983230072969 + 3 ^ 40 * 3830849 * 2
def baseEnd_3830849 : Nat := 437125967065730559859945

theorem tailTrace_3830849 : CollatzResearch.WordTrace tailWord_3830849 prefixEnd_3830849 437125967065730559859945 := by
  unfold tailWord_3830849
  simp only [CollatzResearch.WordTrace]
  refine ⟨139722541698495804766255601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93148361132330536510837067 139722541698495804766255601)
  ·
    refine ⟨104791906273871853574691701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139722541698495804766255601 104791906273871853574691701)
    ·
      refine ⟨9824241213175486272627347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104791906273871853574691701 9824241213175486272627347)
      ·
        refine ⟨14736361819763229408941021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9824241213175486272627347 14736361819763229408941021)
        ·
          refine ⟨5526135682411211028352883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14736361819763229408941021 5526135682411211028352883)
          ·
            refine ⟨8289203523616816542529325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526135682411211028352883 8289203523616816542529325)
            ·
              refine ⟨3108451321356306203448497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8289203523616816542529325 3108451321356306203448497)
              ·
                refine ⟨2331338491017229652586373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3108451321356306203448497 2331338491017229652586373)
                ·
                  refine ⟨437125967065730559859945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2331338491017229652586373 437125967065730559859945)
                  ·
                    rfl

theorem cell22_3830849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 4].length) (baseStart_3830849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830849 prefixEnd_3830849 := by exact prefixLift 3830849
  have htrace : WordTrace (prefixWord ++ tailWord_3830849) baseStart_3830849 baseEnd_3830849 := by
    simpa [prefixWord, tailWord_3830849, baseEnd_3830849] using wordTrace_append hprefix tailTrace_3830849
  have hstable : (prefixWord ++ tailWord_3830849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830849).length < 2 ^ (prefixWord ++ tailWord_3830849).sum := by decide
  have hdescent : baseEnd_3830849 < baseStart_3830849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830892 : List Nat := [2, 2, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_3830892 : Nat := 118140960795 + 3830892 * 2 ^ 59
def prefixEnd_3830892 : Nat := 4983230072969 + 3 ^ 40 * 3830892 * 2
def baseEnd_3830892 : Nat := 1311392620975953900754703

theorem tailTrace_3830892 : CollatzResearch.WordTrace tailWord_3830892 prefixEnd_3830892 1311392620975953900754703 := by
  unfold tailWord_3830892
  simp only [CollatzResearch.WordTrace]
  refine ⟨69862055018670011555035465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93149406691560015406713953 69862055018670011555035465)
  ·
    refine ⟨52396541264002508666276599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69862055018670011555035465 52396541264002508666276599)
    ·
      refine ⟨78594811896003762999414899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52396541264002508666276599 78594811896003762999414899)
      ·
        refine ⟨117892217844005644499122349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78594811896003762999414899 117892217844005644499122349)
        ·
          refine ⟨44209581691502116687170881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117892217844005644499122349 44209581691502116687170881)
          ·
            refine ⟨33157186268626587515378161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44209581691502116687170881 33157186268626587515378161)
            ·
              refine ⟨24867889701469940636533621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33157186268626587515378161 24867889701469940636533621)
              ·
                refine ⟨2331364659512806934675027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24867889701469940636533621 2331364659512806934675027)
                ·
                  refine ⟨3497046989269210402012541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331364659512806934675027 3497046989269210402012541)
                  ·
                    refine ⟨1311392620975953900754703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3497046989269210402012541 1311392620975953900754703)
                    ·
                      rfl

theorem cell22_3830892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_3830892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830892 prefixEnd_3830892 := by exact prefixLift 3830892
  have htrace : WordTrace (prefixWord ++ tailWord_3830892) baseStart_3830892 baseEnd_3830892 := by
    simpa [prefixWord, tailWord_3830892, baseEnd_3830892] using wordTrace_append hprefix tailTrace_3830892
  have hstable : (prefixWord ++ tailWord_3830892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830892).length < 2 ^ (prefixWord ++ tailWord_3830892).sum := by decide
  have hdescent : baseEnd_3830892 < baseStart_3830892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830903 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 2, 5]
def baseStart_3830903 : Nat := 118140960795 + 3830903 * 2 ^ 59
def prefixEnd_3830903 : Nat := 4983230072969 + 3 ^ 40 * 3830903 * 2
def baseEnd_3830903 : Nat := 1311396386500753538729669

theorem tailTrace_3830903 : CollatzResearch.WordTrace tailWord_3830903 prefixEnd_3830903 1311396386500753538729669 := by
  unfold tailWord_3830903
  simp only [CollatzResearch.WordTrace]
  refine ⟨139724511240300171988721363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93149674160200114659147575 139724511240300171988721363)
  ·
    refine ⟨209586766860450257983082045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139724511240300171988721363 209586766860450257983082045)
    ·
      refine ⟨78595037572668846743655767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209586766860450257983082045 78595037572668846743655767)
      ·
        refine ⟨117892556359003270115483651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78595037572668846743655767 117892556359003270115483651)
        ·
          refine ⟨176838834538504905173225477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117892556359003270115483651 176838834538504905173225477)
          ·
            refine ⟨33157281475969669719979777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176838834538504905173225477 33157281475969669719979777)
            ·
              refine ⟨24867961106977252289984833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33157281475969669719979777 24867961106977252289984833)
              ·
                refine ⟨18650970830232939217488625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24867961106977252289984833 18650970830232939217488625)
                ·
                  refine ⟨13988228122674704413116469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18650970830232939217488625 13988228122674704413116469)
                  ·
                    refine ⟨1311396386500753538729669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13988228122674704413116469 1311396386500753538729669)
                    ·
                      rfl

theorem cell22_3830903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_3830903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830903 prefixEnd_3830903 := by exact prefixLift 3830903
  have htrace : WordTrace (prefixWord ++ tailWord_3830903) baseStart_3830903 baseEnd_3830903 := by
    simpa [prefixWord, tailWord_3830903, baseEnd_3830903] using wordTrace_append hprefix tailTrace_3830903
  have hstable : (prefixWord ++ tailWord_3830903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830903).length < 2 ^ (prefixWord ++ tailWord_3830903).sum := by decide
  have hdescent : baseEnd_3830903 < baseStart_3830903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830935 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 3, 4]
def baseStart_3830935 : Nat := 118140960795 + 3830935 * 2 ^ 59
def prefixEnd_3830935 : Nat := 4983230072969 + 3 ^ 40 * 3830935 * 2
def baseEnd_3830935 : Nat := 1311407340754716121929571

theorem tailTrace_3830935 : CollatzResearch.WordTrace tailWord_3830935 prefixEnd_3830935 1311407340754716121929571 := by
  unfold tailWord_3830935
  simp only [CollatzResearch.WordTrace]
  refine ⟨139725678376184241453886259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93150452250789494302590839 139725678376184241453886259)
  ·
    refine ⟨209588517564276362180829389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139725678376184241453886259 209588517564276362180829389)
    ·
      refine ⟨78595694086603635817811021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209588517564276362180829389 78595694086603635817811021)
      ·
        refine ⟨29473385282476363431679133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78595694086603635817811021 29473385282476363431679133)
        ·
          refine ⟨11052519480928636286879675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29473385282476363431679133 11052519480928636286879675)
          ·
            refine ⟨16578779221392954430319513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11052519480928636286879675 16578779221392954430319513)
            ·
              refine ⟨12434084416044715822739635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16578779221392954430319513 12434084416044715822739635)
              ·
                refine ⟨18651126624067073734109453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12434084416044715822739635 18651126624067073734109453)
                ·
                  refine ⟨6994172484025152650291045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18651126624067073734109453 6994172484025152650291045)
                  ·
                    refine ⟨1311407340754716121929571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6994172484025152650291045 1311407340754716121929571)
                    ·
                      rfl

theorem cell22_3830935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_3830935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830935 prefixEnd_3830935 := by exact prefixLift 3830935
  have htrace : WordTrace (prefixWord ++ tailWord_3830935) baseStart_3830935 baseEnd_3830935 := by
    simpa [prefixWord, tailWord_3830935, baseEnd_3830935] using wordTrace_append hprefix tailTrace_3830935
  have hstable : (prefixWord ++ tailWord_3830935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830935).length < 2 ^ (prefixWord ++ tailWord_3830935).sum := by decide
  have hdescent : baseEnd_3830935 < baseStart_3830935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3830993 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_3830993 : Nat := 118140960795 + 3830993 * 2 ^ 59
def prefixEnd_3830993 : Nat := 4983230072969 + 3 ^ 40 * 3830993 * 2
def baseEnd_3830993 : Nat := 1311427195340023303979393

theorem tailTrace_3830993 : CollatzResearch.WordTrace tailWord_3830993 prefixEnd_3830993 1311427195340023303979393 := by
  unfold tailWord_3830993
  simp only [CollatzResearch.WordTrace]
  refine ⟨139727793809974117359497633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93151862539982744906331755 139727793809974117359497633)
  ·
    refine ⟨104795845357480588019623225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139727793809974117359497633 104795845357480588019623225)
    ·
      refine ⟨78596884018110441014717419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104795845357480588019623225 78596884018110441014717419)
      ·
        refine ⟨117895326027165661522076129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78596884018110441014717419 117895326027165661522076129)
        ·
          refine ⟨88421494520374246141557097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117895326027165661522076129 88421494520374246141557097)
          ·
            refine ⟨66316120890280684606167823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88421494520374246141557097 66316120890280684606167823)
            ·
              refine ⟨99474181335421026909251735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66316120890280684606167823 99474181335421026909251735)
              ·
                refine ⟨149211272003131540363877603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99474181335421026909251735 149211272003131540363877603)
                ·
                  refine ⟨223816908004697310545816405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149211272003131540363877603 223816908004697310545816405)
                  ·
                    refine ⟨1311427195340023303979393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 223816908004697310545816405 1311427195340023303979393)
                    ·
                      rfl

theorem cell22_3830993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_3830993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3830993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3830993 prefixEnd_3830993 := by exact prefixLift 3830993
  have htrace : WordTrace (prefixWord ++ tailWord_3830993) baseStart_3830993 baseEnd_3830993 := by
    simpa [prefixWord, tailWord_3830993, baseEnd_3830993] using wordTrace_append hprefix tailTrace_3830993
  have hstable : (prefixWord ++ tailWord_3830993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3830993).length < 2 ^ (prefixWord ++ tailWord_3830993).sum := by decide
  have hdescent : baseEnd_3830993 < baseStart_3830993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3830993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831027 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 3, 3]
def baseStart_3831027 : Nat := 118140960795 + 3831027 * 2 ^ 59
def prefixEnd_3831027 : Nat := 4983230072969 + 3 ^ 40 * 3831027 * 2
def baseEnd_3831027 : Nat := 1311438834234858548629289

theorem tailTrace_3831027 : CollatzResearch.WordTrace tailWord_3831027 prefixEnd_3831027 1311438834234858548629289 := by
  unfold tailWord_3831027
  simp only [CollatzResearch.WordTrace]
  refine ⟨139729033891850941166235335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93152689261233960777490223 139729033891850941166235335)
  ·
    refine ⟨209593550837776411749353003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139729033891850941166235335 209593550837776411749353003)
    ·
      refine ⟨314390326256664617624029505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209593550837776411749353003 314390326256664617624029505)
      ·
        refine ⟨235792744692498463218022129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314390326256664617624029505 235792744692498463218022129)
        ·
          refine ⟨176844558519373847413516597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235792744692498463218022129 176844558519373847413516597)
          ·
            refine ⟨16579177361191298195017181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176844558519373847413516597 16579177361191298195017181)
            ·
              refine ⟨6217191510446736823131443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16579177361191298195017181 6217191510446736823131443)
              ·
                refine ⟨9325787265670105234697165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6217191510446736823131443 9325787265670105234697165)
                ·
                  refine ⟨3497170224626289463011437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9325787265670105234697165 3497170224626289463011437)
                  ·
                    refine ⟨1311438834234858548629289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3497170224626289463011437 1311438834234858548629289)
                    ·
                      rfl

theorem cell22_3831027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 3].length) (baseStart_3831027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831027 prefixEnd_3831027 := by exact prefixLift 3831027
  have htrace : WordTrace (prefixWord ++ tailWord_3831027) baseStart_3831027 baseEnd_3831027 := by
    simpa [prefixWord, tailWord_3831027, baseEnd_3831027] using wordTrace_append hprefix tailTrace_3831027
  have hstable : (prefixWord ++ tailWord_3831027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831027).length < 2 ^ (prefixWord ++ tailWord_3831027).sum := by decide
  have hdescent : baseEnd_3831027 < baseStart_3831027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831074 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_3831074 : Nat := 118140960795 + 3831074 * 2 ^ 59
def prefixEnd_3831074 : Nat := 4983230072969 + 3 ^ 40 * 3831074 * 2
def baseEnd_3831074 : Nat := 437151641098455364234715

theorem tailTrace_3831074 : CollatzResearch.WordTrace tailWord_3831074 prefixEnd_3831074 437151641098455364234715 := by
  unfold tailWord_3831074
  simp only [CollatzResearch.WordTrace]
  refine ⟨34932687030670167048299069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93153832081787112128797517 34932687030670167048299069)
  ·
    refine ⟨13099757636501312643112151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34932687030670167048299069 13099757636501312643112151)
    ·
      refine ⟨19649636454751968964668227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13099757636501312643112151 19649636454751968964668227)
      ·
        refine ⟨29474454682127953447002341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19649636454751968964668227 29474454682127953447002341)
        ·
          refine ⟨5526460252898991271312939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29474454682127953447002341 5526460252898991271312939)
          ·
            refine ⟨8289690379348486906969409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526460252898991271312939 8289690379348486906969409)
            ·
              refine ⟨6217267784511365180227057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8289690379348486906969409 6217267784511365180227057)
              ·
                refine ⟨4662950838383523885170293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6217267784511365180227057 4662950838383523885170293)
                ·
                  refine ⟨437151641098455364234715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4662950838383523885170293 437151641098455364234715)
                  ·
                    rfl

theorem cell22_3831074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_3831074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831074 prefixEnd_3831074 := by exact prefixLift 3831074
  have htrace : WordTrace (prefixWord ++ tailWord_3831074) baseStart_3831074 baseEnd_3831074 := by
    simpa [prefixWord, tailWord_3831074, baseEnd_3831074] using wordTrace_append hprefix tailTrace_3831074
  have hstable : (prefixWord ++ tailWord_3831074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831074).length < 2 ^ (prefixWord ++ tailWord_3831074).sum := by decide
  have hdescent : baseEnd_3831074 < baseStart_3831074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831102 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_3831102 : Nat := 118140960795 + 3831102 * 2 ^ 59
def prefixEnd_3831102 : Nat := 4983230072969 + 3 ^ 40 * 3831102 * 2
def baseEnd_3831102 : Nat := 437154836089194451001353

theorem tailTrace_3831102 : CollatzResearch.WordTrace tailWord_3831102 prefixEnd_3831102 437154836089194451001353 := by
  unfold tailWord_3831102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17466471170822403621901945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93154512911052819316810373 17466471170822403621901945)
  ·
    refine ⟨13099853378116802716426459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17466471170822403621901945 13099853378116802716426459)
    ·
      refine ⟨19649780067175204074639689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13099853378116802716426459 19649780067175204074639689)
      ·
        refine ⟨14737335050381403055979767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19649780067175204074639689 14737335050381403055979767)
        ·
          refine ⟨22106002575572104583969651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14737335050381403055979767 22106002575572104583969651)
          ·
            refine ⟨33159003863358156875954477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22106002575572104583969651 33159003863358156875954477)
            ·
              refine ⟨12434626448759308828482929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33159003863358156875954477 12434626448759308828482929)
              ·
                refine ⟨9325969836569481621362197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12434626448759308828482929 9325969836569481621362197)
                ·
                  refine ⟨437154836089194451001353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9325969836569481621362197 437154836089194451001353)
                  ·
                    rfl

theorem cell22_3831102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_3831102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831102 prefixEnd_3831102 := by exact prefixLift 3831102
  have htrace : WordTrace (prefixWord ++ tailWord_3831102) baseStart_3831102 baseEnd_3831102 := by
    simpa [prefixWord, tailWord_3831102, baseEnd_3831102] using wordTrace_append hprefix tailTrace_3831102
  have hstable : (prefixWord ++ tailWord_3831102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831102).length < 2 ^ (prefixWord ++ tailWord_3831102).sum := by decide
  have hdescent : baseEnd_3831102 < baseStart_3831102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831207 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3831207 : Nat := 118140960795 + 3831207 * 2 ^ 59
def prefixEnd_3831207 : Nat := 4983230072969 + 3 ^ 40 * 3831207 * 2
def baseEnd_3831207 : Nat := 1311500451913398079128737

theorem tailTrace_3831207 : CollatzResearch.WordTrace tailWord_3831207 prefixEnd_3831207 1311500451913398079128737 := by
  unfold tailWord_3831207
  simp only [CollatzResearch.WordTrace]
  refine ⟨139735599031198831907787875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93157066020799221271858583 139735599031198831907787875)
  ·
    refine ⟨209603398546798247861681813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139735599031198831907787875 209603398546798247861681813)
    ·
      refine ⟨9825159306881167868516335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209603398546798247861681813 9825159306881167868516335)
      ·
        refine ⟨14737738960321751802774503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9825159306881167868516335 14737738960321751802774503)
        ·
          refine ⟨22106608440482627704161755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14737738960321751802774503 22106608440482627704161755)
          ·
            refine ⟨33159912660723941556242633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22106608440482627704161755 33159912660723941556242633)
            ·
              refine ⟨24869934495542956167181975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33159912660723941556242633 24869934495542956167181975)
              ·
                refine ⟨37304901743314434250772963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24869934495542956167181975 37304901743314434250772963)
                ·
                  refine ⟨55957352614971651376159445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37304901743314434250772963 55957352614971651376159445)
                  ·
                    refine ⟨1311500451913398079128737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55957352614971651376159445 1311500451913398079128737)
                    ·
                      rfl

theorem cell22_3831207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3831207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831207 prefixEnd_3831207 := by exact prefixLift 3831207
  have htrace : WordTrace (prefixWord ++ tailWord_3831207) baseStart_3831207 baseEnd_3831207 := by
    simpa [prefixWord, tailWord_3831207, baseEnd_3831207] using wordTrace_append hprefix tailTrace_3831207
  have hstable : (prefixWord ++ tailWord_3831207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831207).length < 2 ^ (prefixWord ++ tailWord_3831207).sum := by decide
  have hdescent : baseEnd_3831207 < baseStart_3831207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831269 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_3831269 : Nat := 118140960795 + 3831269 * 2 ^ 59
def prefixEnd_3831269 : Nat := 4983230072969 + 3 ^ 40 * 3831269 * 2
def baseEnd_3831269 : Nat := 1311521675780450584078547

theorem tailTrace_3831269 : CollatzResearch.WordTrace tailWord_3831269 prefixEnd_3831269 1311521675780450584078547 := by
  unfold tailWord_3831269
  simp only [CollatzResearch.WordTrace]
  refine ⟨139737860356974216496544861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93158573571316144331029907 139737860356974216496544861)
  ·
    refine ⟨52401697633865331186204323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139737860356974216496544861 52401697633865331186204323)
    ·
      refine ⟨78602546450797996779306485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52401697633865331186204323 78602546450797996779306485)
      ·
        refine ⟨7368988729762312198059983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78602546450797996779306485 7368988729762312198059983)
        ·
          refine ⟨11053483094643468297089975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368988729762312198059983 11053483094643468297089975)
          ·
            refine ⟨16580224641965202445634963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11053483094643468297089975 16580224641965202445634963)
            ·
              refine ⟨24870336962947803668452445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16580224641965202445634963 24870336962947803668452445)
              ·
                refine ⟨9326376361105426375669667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24870336962947803668452445 9326376361105426375669667)
                ·
                  refine ⟨13989564541658139563504501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9326376361105426375669667 13989564541658139563504501)
                  ·
                    refine ⟨1311521675780450584078547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13989564541658139563504501 1311521675780450584078547)
                    ·
                      rfl

theorem cell22_3831269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_3831269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831269 prefixEnd_3831269 := by exact prefixLift 3831269
  have htrace : WordTrace (prefixWord ++ tailWord_3831269) baseStart_3831269 baseEnd_3831269 := by
    simpa [prefixWord, tailWord_3831269, baseEnd_3831269] using wordTrace_append hprefix tailTrace_3831269
  have hstable : (prefixWord ++ tailWord_3831269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831269).length < 2 ^ (prefixWord ++ tailWord_3831269).sum := by decide
  have hdescent : baseEnd_3831269 < baseStart_3831269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831303 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 2, 3]
def baseStart_3831303 : Nat := 118140960795 + 3831303 * 2 ^ 59
def prefixEnd_3831303 : Nat := 4983230072969 + 3 ^ 40 * 3831303 * 2
def baseEnd_3831303 : Nat := 1311533314675285828728443

theorem tailTrace_3831303 : CollatzResearch.WordTrace tailWord_3831303 prefixEnd_3831303 1311533314675285828728443 := by
  unfold tailWord_3831303
  simp only [CollatzResearch.WordTrace]
  refine ⟨139739100438851040303282563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93159400292567360202188375 139739100438851040303282563)
  ·
    refine ⟨209608650658276560454923845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139739100438851040303282563 209608650658276560454923845)
    ·
      refine ⟨39301621998426855085298221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209608650658276560454923845 39301621998426855085298221)
      ·
        refine ⟨14738108249410070656986833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39301621998426855085298221 14738108249410070656986833)
        ·
          refine ⟨11053581187057552992740125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14738108249410070656986833 11053581187057552992740125)
          ·
            refine ⟨4145092945146582372277547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11053581187057552992740125 4145092945146582372277547)
            ·
              refine ⟨6217639417719873558416321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145092945146582372277547 6217639417719873558416321)
              ·
                refine ⟨4663229563289905168812241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6217639417719873558416321 4663229563289905168812241)
                ·
                  refine ⟨3497422172467428876609181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4663229563289905168812241 3497422172467428876609181)
                  ·
                    refine ⟨1311533314675285828728443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3497422172467428876609181 1311533314675285828728443)
                    ·
                      rfl

theorem cell22_3831303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_3831303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831303 prefixEnd_3831303 := by exact prefixLift 3831303
  have htrace : WordTrace (prefixWord ++ tailWord_3831303) baseStart_3831303 baseEnd_3831303 := by
    simpa [prefixWord, tailWord_3831303, baseEnd_3831303] using wordTrace_append hprefix tailTrace_3831303
  have hstable : (prefixWord ++ tailWord_3831303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831303).length < 2 ^ (prefixWord ++ tailWord_3831303).sum := by decide
  have hdescent : baseEnd_3831303 < baseStart_3831303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831374 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_3831374 : Nat := 118140960795 + 3831374 * 2 ^ 59
def prefixEnd_3831374 : Nat := 4983230072969 + 3 ^ 40 * 3831374 * 2
def baseEnd_3831374 : Nat := 1311557619426265310203225

theorem tailTrace_3831374 : CollatzResearch.WordTrace tailWord_3831374 prefixEnd_3831374 1311557619426265310203225 := by
  unfold tailWord_3831374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17467711252699227428639647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93161126681062546286078117 17467711252699227428639647)
  ·
    refine ⟨26201566879048841142959471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17467711252699227428639647 26201566879048841142959471)
    ·
      refine ⟨39302350318573261714439207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26201566879048841142959471 39302350318573261714439207)
      ·
        refine ⟨58953525477859892571658811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39302350318573261714439207 58953525477859892571658811)
        ·
          refine ⟨88430288216789838857488217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58953525477859892571658811 88430288216789838857488217)
          ·
            refine ⟨66322716162592379143116163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88430288216789838857488217 66322716162592379143116163)
            ·
              refine ⟨99484074243888568714674245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66322716162592379143116163 99484074243888568714674245)
              ·
                refine ⟨18653263920729106634001421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99484074243888568714674245 18653263920729106634001421)
                ·
                  refine ⟨6994973970273414987750533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18653263920729106634001421 6994973970273414987750533)
                  ·
                    refine ⟨1311557619426265310203225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6994973970273414987750533 1311557619426265310203225)
                    ·
                      rfl

theorem cell22_3831374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_3831374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831374 prefixEnd_3831374 := by exact prefixLift 3831374
  have htrace : WordTrace (prefixWord ++ tailWord_3831374) baseStart_3831374 baseEnd_3831374 := by
    simpa [prefixWord, tailWord_3831374, baseEnd_3831374] using wordTrace_append hprefix tailTrace_3831374
  have hstable : (prefixWord ++ tailWord_3831374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831374).length < 2 ^ (prefixWord ++ tailWord_3831374).sum := by decide
  have hdescent : baseEnd_3831374 < baseStart_3831374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831378 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_3831378 : Nat := 118140960795 + 3831378 * 2 ^ 59
def prefixEnd_3831378 : Nat := 4983230072969 + 3 ^ 40 * 3831378 * 2
def baseEnd_3831378 : Nat := 437186329569336877701071

theorem tailTrace_3831378 : CollatzResearch.WordTrace tailWord_3831378 prefixEnd_3831378 437186329569336877701071 := by
  unfold tailWord_3831378
  simp only [CollatzResearch.WordTrace]
  refine ⟨34935458978394832028065697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93161223942386218741508525 34935458978394832028065697)
  ·
    refine ⟨26201594233796124021049273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34935458978394832028065697 26201594233796124021049273)
    ·
      refine ⟨19651195675347093015786955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26201594233796124021049273 19651195675347093015786955)
      ·
        refine ⟨29476793513020639523680433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19651195675347093015786955 29476793513020639523680433)
        ·
          refine ⟨22107595134765479642760325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29476793513020639523680433 22107595134765479642760325)
          ·
            refine ⟨4145174087768527433017561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22107595134765479642760325 4145174087768527433017561)
            ·
              refine ⟨3108880565826395574763171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4145174087768527433017561 3108880565826395574763171)
              ·
                refine ⟨4663320848739593362144757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108880565826395574763171 4663320848739593362144757)
                ·
                  refine ⟨437186329569336877701071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4663320848739593362144757 437186329569336877701071)
                  ·
                    rfl

theorem cell22_3831378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_3831378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831378 prefixEnd_3831378 := by exact prefixLift 3831378
  have htrace : WordTrace (prefixWord ++ tailWord_3831378) baseStart_3831378 baseEnd_3831378 := by
    simpa [prefixWord, tailWord_3831378, baseEnd_3831378] using wordTrace_append hprefix tailTrace_3831378
  have hstable : (prefixWord ++ tailWord_3831378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831378).length < 2 ^ (prefixWord ++ tailWord_3831378).sum := by decide
  have hdescent : baseEnd_3831378 < baseStart_3831378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831408 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 1, 4]
def baseStart_3831408 : Nat := 118140960795 + 3831408 * 2 ^ 59
def prefixEnd_3831408 : Nat := 4983230072969 + 3 ^ 40 * 3831408 * 2
def baseEnd_3831408 : Nat := 1311569258321100554853121

theorem tailTrace_3831408 : CollatzResearch.WordTrace tailWord_3831408 prefixEnd_3831408 1311569258321100554853121 := by
  unfold tailWord_3831408
  simp only [CollatzResearch.WordTrace]
  refine ⟨69871465051735321617927439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93161953402313762157236585 69871465051735321617927439)
  ·
    refine ⟨104807197577602982426891159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69871465051735321617927439 104807197577602982426891159)
    ·
      refine ⟨157210796366404473640336739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104807197577602982426891159 157210796366404473640336739)
      ·
        refine ⟨235816194549606710460505109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157210796366404473640336739 235816194549606710460505109)
        ·
          refine ⟨11053884119512814552836177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235816194549606710460505109 11053884119512814552836177)
          ·
            refine ⟨8290413089634610914627133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11053884119512814552836177 8290413089634610914627133)
            ·
              refine ⟨3108904908612979092985175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8290413089634610914627133 3108904908612979092985175)
              ·
                refine ⟨4663357362919468639477763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108904908612979092985175 4663357362919468639477763)
                ·
                  refine ⟨6995036044379202959216645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663357362919468639477763 6995036044379202959216645)
                  ·
                    refine ⟨1311569258321100554853121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995036044379202959216645 1311569258321100554853121)
                    ·
                      rfl

theorem cell22_3831408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 4].length) (baseStart_3831408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831408 prefixEnd_3831408 := by exact prefixLift 3831408
  have htrace : WordTrace (prefixWord ++ tailWord_3831408) baseStart_3831408 baseEnd_3831408 := by
    simpa [prefixWord, tailWord_3831408, baseEnd_3831408] using wordTrace_append hprefix tailTrace_3831408
  have hstable : (prefixWord ++ tailWord_3831408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831408).length < 2 ^ (prefixWord ++ tailWord_3831408).sum := by decide
  have hdescent : baseEnd_3831408 < baseStart_3831408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831419 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 2, 4]
def baseStart_3831419 : Nat := 118140960795 + 3831419 * 2 ^ 59
def prefixEnd_3831419 : Nat := 4983230072969 + 3 ^ 40 * 3831419 * 2
def baseEnd_3831419 : Nat := 1311573023845900192828087

theorem tailTrace_3831419 : CollatzResearch.WordTrace tailWord_3831419 prefixEnd_3831419 1311573023845900192828087 := by
  unfold tailWord_3831419
  simp only [CollatzResearch.WordTrace]
  refine ⟨139743331306430792114505311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93162220870953861409670207 139743331306430792114505311)
  ·
    refine ⟨209614996959646188171757967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139743331306430792114505311 209614996959646188171757967)
    ·
      refine ⟨314422495439469282257636951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209614996959646188171757967 314422495439469282257636951)
      ·
        refine ⟨471633743159203923386455427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314422495439469282257636951 471633743159203923386455427)
        ·
          refine ⟨707450614738805885079683141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471633743159203923386455427 707450614738805885079683141)
          ·
            refine ⟨132646990263526103452440589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 707450614738805885079683141 132646990263526103452440589)
            ·
              refine ⟨49742621348822288794665221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132646990263526103452440589 49742621348822288794665221)
              ·
                refine ⟨9326741502904179148999729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49742621348822288794665221 9326741502904179148999729)
                ·
                  refine ⟨6995056127178134361749797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9326741502904179148999729 6995056127178134361749797)
                  ·
                    refine ⟨1311573023845900192828087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995056127178134361749797 1311573023845900192828087)
                    ·
                      rfl

theorem cell22_3831419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 4].length) (baseStart_3831419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831419 prefixEnd_3831419 := by exact prefixLift 3831419
  have htrace : WordTrace (prefixWord ++ tailWord_3831419) baseStart_3831419 baseEnd_3831419 := by
    simpa [prefixWord, tailWord_3831419, baseEnd_3831419] using wordTrace_append hprefix tailTrace_3831419
  have hstable : (prefixWord ++ tailWord_3831419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831419).length < 2 ^ (prefixWord ++ tailWord_3831419).sum := by decide
  have hdescent : baseEnd_3831419 < baseStart_3831419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831438 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_3831438 : Nat := 118140960795 + 3831438 * 2 ^ 59
def prefixEnd_3831438 : Nat := 4983230072969 + 3 ^ 40 * 3831438 * 2
def baseEnd_3831438 : Nat := 1311579527934190476603029

theorem tailTrace_3831438 : CollatzResearch.WordTrace tailWord_3831438 prefixEnd_3831438 1311579527934190476603029 := by
  unfold tailWord_3831438
  simp only [CollatzResearch.WordTrace]
  refine ⟨17468003036670244794930871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93162682862241305572964645 17468003036670244794930871)
  ·
    refine ⟨26202004555005367192396307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17468003036670244794930871 26202004555005367192396307)
    ·
      refine ⟨39303006832508050788594461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26202004555005367192396307 39303006832508050788594461)
      ·
        refine ⟨14738627562190519045722923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39303006832508050788594461 14738627562190519045722923)
        ·
          refine ⟨22107941343285778568584385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14738627562190519045722923 22107941343285778568584385)
          ·
            refine ⟨16580956007464333926438289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22107941343285778568584385 16580956007464333926438289)
            ·
              refine ⟨12435717005598250444828717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16580956007464333926438289 12435717005598250444828717)
              ·
                refine ⟨4663393877099343916810769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12435717005598250444828717 4663393877099343916810769)
                ·
                  refine ⟨3497545407824507937608077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4663393877099343916810769 3497545407824507937608077)
                  ·
                    refine ⟨1311579527934190476603029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3497545407824507937608077 1311579527934190476603029)
                    ·
                      rfl

theorem cell22_3831438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_3831438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831438 prefixEnd_3831438 := by exact prefixLift 3831438
  have htrace : WordTrace (prefixWord ++ tailWord_3831438) baseStart_3831438 baseEnd_3831438 := by
    simpa [prefixWord, tailWord_3831438, baseEnd_3831438] using wordTrace_append hprefix tailTrace_3831438
  have hstable : (prefixWord ++ tailWord_3831438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831438).length < 2 ^ (prefixWord ++ tailWord_3831438).sum := by decide
  have hdescent : baseEnd_3831438 < baseStart_3831438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831588 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_3831588 : Nat := 118140960795 + 3831588 * 2 ^ 59
def prefixEnd_3831588 : Nat := 4983230072969 + 3 ^ 40 * 3831588 * 2
def baseEnd_3831588 : Nat := 1311630875999640085352569

theorem tailTrace_3831588 : CollatzResearch.WordTrace tailWord_3831588 prefixEnd_3831588 1311630875999640085352569 := by
  unfold tailWord_3831588
  simp only [CollatzResearch.WordTrace]
  refine ⟨69874747621409266988703709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93166330161879022651604945 69874747621409266988703709)
  ·
    refine ⟨26203030358028475120763891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69874747621409266988703709 26203030358028475120763891)
    ·
      refine ⟨39304545537042712681145837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26203030358028475120763891 39304545537042712681145837)
      ·
        refine ⟨14739204576391017255429689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39304545537042712681145837 14739204576391017255429689)
        ·
          refine ⟨11054403432293262941572267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14739204576391017255429689 11054403432293262941572267)
          ·
            refine ⟨16581605148439894412358401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11054403432293262941572267 16581605148439894412358401)
            ·
              refine ⟨12436203861329920809268801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16581605148439894412358401 12436203861329920809268801)
              ·
                refine ⟨9327152895997440606951601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12436203861329920809268801 9327152895997440606951601)
                ·
                  refine ⟨6995364671998080455213701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327152895997440606951601 6995364671998080455213701)
                  ·
                    refine ⟨1311630875999640085352569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995364671998080455213701 1311630875999640085352569)
                    ·
                      rfl

theorem cell22_3831588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_3831588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831588 prefixEnd_3831588 := by exact prefixLift 3831588
  have htrace : WordTrace (prefixWord ++ tailWord_3831588) baseStart_3831588 baseEnd_3831588 := by
    simpa [prefixWord, tailWord_3831588, baseEnd_3831588] using wordTrace_append hprefix tailTrace_3831588
  have hstable : (prefixWord ++ tailWord_3831588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831588).length < 2 ^ (prefixWord ++ tailWord_3831588).sum := by decide
  have hdescent : baseEnd_3831588 < baseStart_3831588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831592 : List Nat := [2, 1, 5, 1, 1, 4, 2, 2, 4]
def baseStart_3831592 : Nat := 118140960795 + 3831592 * 2 ^ 59
def prefixEnd_3831592 : Nat := 4983230072969 + 3 ^ 40 * 3831592 * 2
def baseEnd_3831592 : Nat := 437210748427128469417519

theorem tailTrace_3831592 : CollatzResearch.WordTrace tailWord_3831592 prefixEnd_3831592 437210748427128469417519 := by
  unfold tailWord_3831592
  simp only [CollatzResearch.WordTrace]
  refine ⟨69874820567402021330276515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93166427423202695107035353 69874820567402021330276515)
  ·
    refine ⟨104812230851103031995414773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69874820567402021330276515 104812230851103031995414773)
    ·
      refine ⟨9826146642290909249570135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104812230851103031995414773 9826146642290909249570135)
      ·
        refine ⟨14739219963436363874355203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9826146642290909249570135 14739219963436363874355203)
        ·
          refine ⟨22108829945154545811532805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14739219963436363874355203 22108829945154545811532805)
          ·
            refine ⟨4145405614716477339662401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22108829945154545811532805 4145405614716477339662401)
            ·
              refine ⟨3109054211037358004746801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4145405614716477339662401 3109054211037358004746801)
              ·
                refine ⟨2331790658278018503560101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3109054211037358004746801 2331790658278018503560101)
                ·
                  refine ⟨437210748427128469417519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2331790658278018503560101 437210748427128469417519)
                  ·
                    rfl

theorem cell22_3831592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 4].length) (baseStart_3831592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831592 prefixEnd_3831592 := by exact prefixLift 3831592
  have htrace : WordTrace (prefixWord ++ tailWord_3831592) baseStart_3831592 baseEnd_3831592 := by
    simpa [prefixWord, tailWord_3831592, baseEnd_3831592] using wordTrace_append hprefix tailTrace_3831592
  have hstable : (prefixWord ++ tailWord_3831592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831592).length < 2 ^ (prefixWord ++ tailWord_3831592).sum := by decide
  have hdescent : baseEnd_3831592 < baseStart_3831592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831603 : List Nat := [1, 1, 1, 2, 7, 2, 1, 7]
def baseStart_3831603 : Nat := 118140960795 + 3831603 * 2 ^ 59
def prefixEnd_3831603 : Nat := 4983230072969 + 3 ^ 40 * 3831603 * 2
def baseEnd_3831603 : Nat := 145737334534020560691947

theorem tailTrace_3831603 : CollatzResearch.WordTrace tailWord_3831603 prefixEnd_3831603 145737334534020560691947 := by
  unfold tailWord_3831603
  simp only [CollatzResearch.WordTrace]
  refine ⟨139750042337764191539203463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93166694891842794359468975 139750042337764191539203463)
  ·
    refine ⟨209625063506646287308805195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139750042337764191539203463 209625063506646287308805195)
    ·
      refine ⟨314437595259969430963207793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209625063506646287308805195 314437595259969430963207793)
      ·
        refine ⟨235828196444977073222405845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314437595259969430963207793 235828196444977073222405845)
        ·
          refine ⟨5527223354179150153650137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 235828196444977073222405845 5527223354179150153650137)
          ·
            refine ⟨4145417515634362615237603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5527223354179150153650137 4145417515634362615237603)
            ·
              refine ⟨6218126273451543922856405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145417515634362615237603 6218126273451543922856405)
              ·
                refine ⟨145737334534020560691947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6218126273451543922856405 145737334534020560691947)
                ·
                  rfl

theorem cell22_3831603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 7].length) (baseStart_3831603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831603 prefixEnd_3831603 := by exact prefixLift 3831603
  have htrace : WordTrace (prefixWord ++ tailWord_3831603) baseStart_3831603 baseEnd_3831603 := by
    simpa [prefixWord, tailWord_3831603, baseEnd_3831603] using wordTrace_append hprefix tailTrace_3831603
  have hstable : (prefixWord ++ tailWord_3831603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831603).length < 2 ^ (prefixWord ++ tailWord_3831603).sum := by decide
  have hdescent : baseEnd_3831603 < baseStart_3831603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831622 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3831622 : Nat := 118140960795 + 3831622 * 2 ^ 59
def prefixEnd_3831622 : Nat := 4983230072969 + 3 ^ 40 * 3831622 * 2
def baseEnd_3831622 : Nat := 1311642514894475330002465

theorem tailTrace_3831622 : CollatzResearch.WordTrace tailWord_3831622 prefixEnd_3831622 1311642514894475330002465 := by
  unfold tailWord_3831622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4367210478896729930754535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93167156883130238522763413 4367210478896729930754535)
  ·
    refine ⟨6550815718345094896131803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4367210478896729930754535 6550815718345094896131803)
    ·
      refine ⟨9826223577517642344197705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6550815718345094896131803 9826223577517642344197705)
      ·
        refine ⟨7369667683138231758148279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9826223577517642344197705 7369667683138231758148279)
        ·
          refine ⟨11054501524707347637222419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7369667683138231758148279 11054501524707347637222419)
          ·
            refine ⟨16581752287061021455833629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11054501524707347637222419 16581752287061021455833629)
            ·
              refine ⟨6218157107647883045937611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16581752287061021455833629 6218157107647883045937611)
              ·
                refine ⟨9327235661471824568906417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6218157107647883045937611 9327235661471824568906417)
                ·
                  refine ⟨6995426746103868426679813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327235661471824568906417 6995426746103868426679813)
                  ·
                    refine ⟨1311642514894475330002465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6995426746103868426679813 1311642514894475330002465)
                    ·
                      rfl

theorem cell22_3831622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3831622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831622 prefixEnd_3831622 := by exact prefixLift 3831622
  have htrace : WordTrace (prefixWord ++ tailWord_3831622) baseStart_3831622 baseEnd_3831622 := by
    simpa [prefixWord, tailWord_3831622, baseEnd_3831622] using wordTrace_append hprefix tailTrace_3831622
  have hstable : (prefixWord ++ tailWord_3831622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831622).length < 2 ^ (prefixWord ++ tailWord_3831622).sum := by decide
  have hdescent : baseEnd_3831622 < baseStart_3831622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831648 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 5]
def baseStart_3831648 : Nat := 118140960795 + 3831648 * 2 ^ 59
def prefixEnd_3831648 : Nat := 4983230072969 + 3 ^ 40 * 3831648 * 2
def baseEnd_3831648 : Nat := 437217138408606642950795

theorem tailTrace_3831648 : CollatzResearch.WordTrace tailWord_3831648 prefixEnd_3831648 437217138408606642950795 := by
  unfold tailWord_3831648
  simp only [CollatzResearch.WordTrace]
  refine ⟨69875841811300582112295799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93167789081734109483061065 69875841811300582112295799)
  ·
    refine ⟨104813762716950873168443699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69875841811300582112295799 104813762716950873168443699)
    ·
      refine ⟨157220644075426309752665549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104813762716950873168443699 157220644075426309752665549)
      ·
        refine ⟨58957741528284866157249581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157220644075426309752665549 58957741528284866157249581)
        ·
          refine ⟨22109153073106824808968593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58957741528284866157249581 22109153073106824808968593)
          ·
            refine ⟨16581864804830118606726445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22109153073106824808968593 16581864804830118606726445)
            ·
              refine ⟨6218199301811294477522417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16581864804830118606726445 6218199301811294477522417)
              ·
                refine ⟨4663649476358470858141813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6218199301811294477522417 4663649476358470858141813)
                ·
                  refine ⟨437217138408606642950795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4663649476358470858141813 437217138408606642950795)
                  ·
                    rfl

theorem cell22_3831648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_3831648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831648 prefixEnd_3831648 := by exact prefixLift 3831648
  have htrace : WordTrace (prefixWord ++ tailWord_3831648) baseStart_3831648 baseEnd_3831648 := by
    simpa [prefixWord, tailWord_3831648, baseEnd_3831648] using wordTrace_append hprefix tailTrace_3831648
  have hstable : (prefixWord ++ tailWord_3831648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831648).length < 2 ^ (prefixWord ++ tailWord_3831648).sum := by decide
  have hdescent : baseEnd_3831648 < baseStart_3831648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831691 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 3, 5]
def baseStart_3831691 : Nat := 118140960795 + 3831691 * 2 ^ 59
def prefixEnd_3831691 : Nat := 4983230072969 + 3 ^ 40 * 3831691 * 2
def baseEnd_3831691 : Nat := 1311666135004582150027253

theorem tailTrace_3831691 : CollatzResearch.WordTrace tailWord_3831691 prefixEnd_3831691 1311666135004582150027253 := by
  unfold tailWord_3831691
  simp only [CollatzResearch.WordTrace]
  refine ⟨139753251961445382568406927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93168834640963588378937951 139753251961445382568406927)
  ·
    refine ⟨209629877942168073852610391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139753251961445382568406927 209629877942168073852610391)
    ·
      refine ⟨314444816913252110778915587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209629877942168073852610391 314444816913252110778915587)
      ·
        refine ⟨471667225369878166168373381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314444816913252110778915587 471667225369878166168373381)
        ·
          refine ⟨88437604756852156156570009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471667225369878166168373381 88437604756852156156570009)
          ·
            refine ⟨66328203567639117117427507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88437604756852156156570009 66328203567639117117427507)
            ·
              refine ⟨99492305351458675676141261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66328203567639117117427507 99492305351458675676141261)
              ·
                refine ⟨37309614506797003378552973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99492305351458675676141261 37309614506797003378552973)
                ·
                  refine ⟨13991105440048876266957365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37309614506797003378552973 13991105440048876266957365)
                  ·
                    refine ⟨1311666135004582150027253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13991105440048876266957365 1311666135004582150027253)
                    ·
                      rfl

theorem cell22_3831691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_3831691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831691 prefixEnd_3831691 := by exact prefixLift 3831691
  have htrace : WordTrace (prefixWord ++ tailWord_3831691) baseStart_3831691 baseEnd_3831691 := by
    simpa [prefixWord, tailWord_3831691, baseEnd_3831691] using wordTrace_append hprefix tailTrace_3831691
  have hstable : (prefixWord ++ tailWord_3831691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831691).length < 2 ^ (prefixWord ++ tailWord_3831691).sum := by decide
  have hdescent : baseEnd_3831691 < baseStart_3831691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831753 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 5, 3]
def baseStart_3831753 : Nat := 118140960795 + 3831753 * 2 ^ 59
def prefixEnd_3831753 : Nat := 4983230072969 + 3 ^ 40 * 3831753 * 2
def baseEnd_3831753 : Nat := 1311687358871634654977063

theorem tailTrace_3831753 : CollatzResearch.WordTrace tailWord_3831753 prefixEnd_3831753 1311687358871634654977063 := by
  unfold tailWord_3831753
  simp only [CollatzResearch.WordTrace]
  refine ⟨139755513287220767157163913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93170342191480511438109275 139755513287220767157163913)
  ·
    refine ⟨104816634965415575367872935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139755513287220767157163913 104816634965415575367872935)
    ·
      refine ⟨157224952448123363051809403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104816634965415575367872935 157224952448123363051809403)
      ·
        refine ⟨235837428672185044577714105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157224952448123363051809403 235837428672185044577714105)
        ·
          refine ⟨176878071504138783433285579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235837428672185044577714105 176878071504138783433285579)
          ·
            refine ⟨265317107256208175149928369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176878071504138783433285579 265317107256208175149928369)
            ·
              refine ⟨198987830442156131362446277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265317107256208175149928369 198987830442156131362446277)
              ·
                refine ⟨37310218207904274630458677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198987830442156131362446277 37310218207904274630458677)
                ·
                  refine ⟨3497832956991025746605501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37310218207904274630458677 3497832956991025746605501)
                  ·
                    refine ⟨1311687358871634654977063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3497832956991025746605501 1311687358871634654977063)
                    ·
                      rfl

theorem cell22_3831753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_3831753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831753 prefixEnd_3831753 := by exact prefixLift 3831753
  have htrace : WordTrace (prefixWord ++ tailWord_3831753) baseStart_3831753 baseEnd_3831753 := by
    simpa [prefixWord, tailWord_3831753, baseEnd_3831753] using wordTrace_append hprefix tailTrace_3831753
  have hstable : (prefixWord ++ tailWord_3831753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831753).length < 2 ^ (prefixWord ++ tailWord_3831753).sum := by decide
  have hdescent : baseEnd_3831753 < baseStart_3831753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831903 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 4, 6]
def baseStart_3831903 : Nat := 118140960795 + 3831903 * 2 ^ 59
def prefixEnd_3831903 : Nat := 4983230072969 + 3 ^ 40 * 3831903 * 2
def baseEnd_3831903 : Nat := 1311738706937084263726603

theorem tailTrace_3831903 : CollatzResearch.WordTrace tailWord_3831903 prefixEnd_3831903 1311738706937084263726603 := by
  unfold tailWord_3831903
  simp only [CollatzResearch.WordTrace]
  refine ⟨139760984236677342775124363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93173989491118228516749575 139760984236677342775124363)
  ·
    refine ⟨209641476355016014162686545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139760984236677342775124363 209641476355016014162686545)
    ·
      refine ⟨157231107266262010622014909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209641476355016014162686545 157231107266262010622014909)
      ·
        refine ⟨58961665224848253983255591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157231107266262010622014909 58961665224848253983255591)
        ·
          refine ⟨88442497837272380974883387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58961665224848253983255591 88442497837272380974883387)
          ·
            refine ⟨132663746755908571462325081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88442497837272380974883387 132663746755908571462325081)
            ·
              refine ⟨99497810066931428596743811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132663746755908571462325081 99497810066931428596743811)
              ·
                refine ⟨149246715100397142895115717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99497810066931428596743811 149246715100397142895115717)
                ·
                  refine ⟨27983759081324464292834197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149246715100397142895115717 27983759081324464292834197)
                  ·
                    refine ⟨1311738706937084263726603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27983759081324464292834197 1311738706937084263726603)
                    ·
                      rfl

theorem cell22_3831903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_3831903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831903 prefixEnd_3831903 := by exact prefixLift 3831903
  have htrace : WordTrace (prefixWord ++ tailWord_3831903) baseStart_3831903 baseEnd_3831903 := by
    simpa [prefixWord, tailWord_3831903, baseEnd_3831903] using wordTrace_append hprefix tailTrace_3831903
  have hstable : (prefixWord ++ tailWord_3831903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831903).length < 2 ^ (prefixWord ++ tailWord_3831903).sum := by decide
  have hdescent : baseEnd_3831903 < baseStart_3831903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831905 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 5, 3]
def baseStart_3831905 : Nat := 118140960795 + 3831905 * 2 ^ 59
def prefixEnd_3831905 : Nat := 4983230072969 + 3 ^ 40 * 3831905 * 2
def baseEnd_3831905 : Nat := 1311739391577956925176597

theorem tailTrace_3831905 : CollatzResearch.WordTrace tailWord_3831905 prefixEnd_3831905 1311739391577956925176597 := by
  unfold tailWord_3831905
  simp only [CollatzResearch.WordTrace]
  refine ⟨139761057182670097116697169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93174038121780064744464779 139761057182670097116697169)
  ·
    refine ⟨104820792887002572837522877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139761057182670097116697169 104820792887002572837522877)
    ·
      refine ⟨39307797332625964814071079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104820792887002572837522877 39307797332625964814071079)
      ·
        refine ⟨58961695998938947221106619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39307797332625964814071079 58961695998938947221106619)
        ·
          refine ⟨88442543998408420831659929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58961695998938947221106619 88442543998408420831659929)
          ·
            refine ⟨66331907998806315623744947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88442543998408420831659929 66331907998806315623744947)
            ·
              refine ⟨99497861998209473435617421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66331907998806315623744947 99497861998209473435617421)
              ·
                refine ⟨37311698249328552538356533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99497861998209473435617421 37311698249328552538356533)
                ·
                  refine ⟨3497971710874551800470925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37311698249328552538356533 3497971710874551800470925)
                  ·
                    refine ⟨1311739391577956925176597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3497971710874551800470925 1311739391577956925176597)
                    ·
                      rfl

theorem cell22_3831905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_3831905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831905 prefixEnd_3831905 := by exact prefixLift 3831905
  have htrace : WordTrace (prefixWord ++ tailWord_3831905) baseStart_3831905 baseEnd_3831905 := by
    simpa [prefixWord, tailWord_3831905, baseEnd_3831905] using wordTrace_append hprefix tailTrace_3831905
  have hstable : (prefixWord ++ tailWord_3831905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831905).length < 2 ^ (prefixWord ++ tailWord_3831905).sum := by decide
  have hdescent : baseEnd_3831905 < baseStart_3831905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831939 : List Nat := [1, 1, 1, 3, 3, 4, 1, 4, 1, 3]
def baseStart_3831939 : Nat := 118140960795 + 3831939 * 2 ^ 59
def prefixEnd_3831939 : Nat := 4983230072969 + 3 ^ 40 * 3831939 * 2
def baseEnd_3831939 : Nat := 1311751030472792169826493

theorem tailTrace_3831939 : CollatzResearch.WordTrace tailWord_3831939 prefixEnd_3831939 1311751030472792169826493 := by
  unfold tailWord_3831939
  simp only [CollatzResearch.WordTrace]
  refine ⟨139762297264546920923434871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93174864843031280615623247 139762297264546920923434871)
  ·
    refine ⟨209643445896820381385152307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139762297264546920923434871 209643445896820381385152307)
    ·
      refine ⟨314465168845230572077728461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209643445896820381385152307 314465168845230572077728461)
      ·
        refine ⟨117924438316961464529148173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314465168845230572077728461 117924438316961464529148173)
        ·
          refine ⟨44221664368860549198430565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117924438316961464529148173 44221664368860549198430565)
          ·
            refine ⟨8291562069161352974705731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44221664368860549198430565 8291562069161352974705731)
            ·
              refine ⟨12437343103742029462058597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291562069161352974705731 12437343103742029462058597)
              ·
                refine ⟨2332001831951630524135987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12437343103742029462058597 2332001831951630524135987)
                ·
                  refine ⟨3498002747927445786203981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332001831951630524135987 3498002747927445786203981)
                  ·
                    refine ⟨1311751030472792169826493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498002747927445786203981 1311751030472792169826493)
                    ·
                      rfl

theorem cell22_3831939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 3].length) (baseStart_3831939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831939 prefixEnd_3831939 := by exact prefixLift 3831939
  have htrace : WordTrace (prefixWord ++ tailWord_3831939) baseStart_3831939 baseEnd_3831939 := by
    simpa [prefixWord, tailWord_3831939, baseEnd_3831939] using wordTrace_append hprefix tailTrace_3831939
  have hstable : (prefixWord ++ tailWord_3831939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831939).length < 2 ^ (prefixWord ++ tailWord_3831939).sum := by decide
  have hdescent : baseEnd_3831939 < baseStart_3831939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3831956 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3831956 : Nat := 118140960795 + 3831956 * 2 ^ 59
def prefixEnd_3831956 : Nat := 4983230072969 + 3 ^ 40 * 3831956 * 2
def baseEnd_3831956 : Nat := 1311756849920209792151441

theorem tailTrace_3831956 : CollatzResearch.WordTrace tailWord_3831956 prefixEnd_3831956 1311756849920209792151441 := by
  unfold tailWord_3831956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69881458652742666413401861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93175278203656888551202481 69881458652742666413401861)
  ·
    refine ⟨13102773497389249952512849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69881458652742666413401861 13102773497389249952512849)
    ·
      refine ⟨9827080123041937464384637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13102773497389249952512849 9827080123041937464384637)
      ·
        refine ⟨3685155046140726549144239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9827080123041937464384637 3685155046140726549144239)
        ·
          refine ⟨5527732569211089823716359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685155046140726549144239 5527732569211089823716359)
          ·
            refine ⟨8291598853816634735574539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527732569211089823716359 8291598853816634735574539)
            ·
              refine ⟨12437398280724952103361809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291598853816634735574539 12437398280724952103361809)
              ·
                refine ⟨9328048710543714077521357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12437398280724952103361809 9328048710543714077521357)
                ·
                  refine ⟨3498018266453892779070509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9328048710543714077521357 3498018266453892779070509)
                  ·
                    refine ⟨1311756849920209792151441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498018266453892779070509 1311756849920209792151441)
                    ·
                      rfl

theorem cell22_3831956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3831956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3831956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3831956 prefixEnd_3831956 := by exact prefixLift 3831956
  have htrace : WordTrace (prefixWord ++ tailWord_3831956) baseStart_3831956 baseEnd_3831956 := by
    simpa [prefixWord, tailWord_3831956, baseEnd_3831956] using wordTrace_append hprefix tailTrace_3831956
  have hstable : (prefixWord ++ tailWord_3831956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3831956).length < 2 ^ (prefixWord ++ tailWord_3831956).sum := by decide
  have hdescent : baseEnd_3831956 < baseStart_3831956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3831956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832010 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_3832010 : Nat := 118140960795 + 3832010 * 2 ^ 59
def prefixEnd_3832010 : Nat := 4983230072969 + 3 ^ 40 * 3832010 * 2
def baseEnd_3832010 : Nat := 1311775335223771651301275

theorem tailTrace_3832010 : CollatzResearch.WordTrace tailWord_3832010 prefixEnd_3832010 1311775335223771651301275 := by
  unfold tailWord_3832010
  simp only [CollatzResearch.WordTrace]
  refine ⟨34941221711822425012317371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93176591231526466699512989 34941221711822425012317371)
  ·
    refine ⟨52411832567733637518476057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34941221711822425012317371 52411832567733637518476057)
    ·
      refine ⟨39308874425800228138857043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52411832567733637518476057 39308874425800228138857043)
      ·
        refine ⟨58963311638700342208285565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39308874425800228138857043 58963311638700342208285565)
        ·
          refine ⟨22111241864512628328107087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58963311638700342208285565 22111241864512628328107087)
          ·
            refine ⟨33166862796768942492160631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22111241864512628328107087 33166862796768942492160631)
            ·
              refine ⟨49750294195153413738240947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33166862796768942492160631 49750294195153413738240947)
              ·
                refine ⟨74625441292730120607361421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49750294195153413738240947 74625441292730120607361421)
                ·
                  refine ⟨27984540484773795227760533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74625441292730120607361421 27984540484773795227760533)
                  ·
                    refine ⟨1311775335223771651301275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27984540484773795227760533 1311775335223771651301275)
                    ·
                      rfl

theorem cell22_3832010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_3832010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832010 prefixEnd_3832010 := by exact prefixLift 3832010
  have htrace : WordTrace (prefixWord ++ tailWord_3832010) baseStart_3832010 baseEnd_3832010 := by
    simpa [prefixWord, tailWord_3832010, baseEnd_3832010] using wordTrace_append hprefix tailTrace_3832010
  have hstable : (prefixWord ++ tailWord_3832010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832010).length < 2 ^ (prefixWord ++ tailWord_3832010).sum := by decide
  have hdescent : baseEnd_3832010 < baseStart_3832010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832029 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3832029 : Nat := 118140960795 + 3832029 * 2 ^ 59
def prefixEnd_3832029 : Nat := 4983230072969 + 3 ^ 40 * 3832029 * 2
def baseEnd_3832029 : Nat := 1311781839312061935076217

theorem tailTrace_3832029 : CollatzResearch.WordTrace tailWord_3832029 prefixEnd_3832029 1311781839312061935076217 := by
  unfold tailWord_3832029
  simp only [CollatzResearch.WordTrace]
  refine ⟨139765579834220866294211141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93177053222813910862807427 139765579834220866294211141)
  ·
    refine ⟨26206046218916412430164589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139765579834220866294211141 26206046218916412430164589)
    ·
      refine ⟨9827267332093654661311721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26206046218916412430164589 9827267332093654661311721)
      ·
        refine ⟨7370450499070240995983791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9827267332093654661311721 7370450499070240995983791)
        ·
          refine ⟨11055675748605361493975687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7370450499070240995983791 11055675748605361493975687)
          ·
            refine ⟨16583513622908042240963531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11055675748605361493975687 16583513622908042240963531)
            ·
              refine ⟨24875270434362063361445297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16583513622908042240963531 24875270434362063361445297)
              ·
                refine ⟨18656452825771547521083973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24875270434362063361445297 18656452825771547521083973)
                ·
                  refine ⟨3498084904832165160203245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18656452825771547521083973 3498084904832165160203245)
                  ·
                    refine ⟨1311781839312061935076217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498084904832165160203245 1311781839312061935076217)
                    ·
                      rfl

theorem cell22_3832029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3832029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832029 prefixEnd_3832029 := by exact prefixLift 3832029
  have htrace : WordTrace (prefixWord ++ tailWord_3832029) baseStart_3832029 baseEnd_3832029 := by
    simpa [prefixWord, tailWord_3832029, baseEnd_3832029] using wordTrace_append hprefix tailTrace_3832029
  have hstable : (prefixWord ++ tailWord_3832029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832029).length < 2 ^ (prefixWord ++ tailWord_3832029).sum := by decide
  have hdescent : baseEnd_3832029 < baseStart_3832029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832057 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 3, 3]
def baseStart_3832057 : Nat := 118140960795 + 3832057 * 2 ^ 59
def prefixEnd_3832057 : Nat := 4983230072969 + 3 ^ 40 * 3832057 * 2
def baseEnd_3832057 : Nat := 1311791424284279195376131

theorem tailTrace_3832057 : CollatzResearch.WordTrace tailWord_3832057 prefixEnd_3832057 1311791424284279195376131 := by
  unfold tailWord_3832057
  simp only [CollatzResearch.WordTrace]
  refine ⟨139766601078119427076230425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93177734052079618050820283 139766601078119427076230425)
  ·
    refine ⟨104824950808589570307172819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139766601078119427076230425 104824950808589570307172819)
    ·
      refine ⟨157237426212884355460759229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104824950808589570307172819 157237426212884355460759229)
      ·
        refine ⟨58964034829831633297784711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157237426212884355460759229 58964034829831633297784711)
        ·
          refine ⟨88446052244747449946677067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58964034829831633297784711 88446052244747449946677067)
          ·
            refine ⟨132669078367121174920015601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88446052244747449946677067 132669078367121174920015601)
            ·
              refine ⟨99501808775340881190011701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132669078367121174920015601 99501808775340881190011701)
              ·
                refine ⟨9328294572688207611563597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99501808775340881190011701 9328294572688207611563597)
                ·
                  refine ⟨3498110464758077854336349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9328294572688207611563597 3498110464758077854336349)
                  ·
                    refine ⟨1311791424284279195376131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498110464758077854336349 1311791424284279195376131)
                    ·
                      rfl

theorem cell22_3832057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_3832057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832057 prefixEnd_3832057 := by exact prefixLift 3832057
  have htrace : WordTrace (prefixWord ++ tailWord_3832057) baseStart_3832057 baseEnd_3832057 := by
    simpa [prefixWord, tailWord_3832057, baseEnd_3832057] using wordTrace_append hprefix tailTrace_3832057
  have hstable : (prefixWord ++ tailWord_3832057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832057).length < 2 ^ (prefixWord ++ tailWord_3832057).sum := by decide
  have hdescent : baseEnd_3832057 < baseStart_3832057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832117 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3832117 : Nat := 118140960795 + 3832117 * 2 ^ 59
def prefixEnd_3832117 : Nat := 4983230072969 + 3 ^ 40 * 3832117 * 2
def baseEnd_3832117 : Nat := 1311811963510459038875947

theorem tailTrace_3832117 : CollatzResearch.WordTrace tailWord_3832117 prefixEnd_3832117 1311811963510459038875947 := by
  unfold tailWord_3832117
  simp only [CollatzResearch.WordTrace]
  refine ⟨139768789457902057323414605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93179192971934704882276403 139768789457902057323414605)
  ·
    refine ⟨52413296046713271496280477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139768789457902057323414605 52413296046713271496280477)
    ·
      refine ⟨19654986017517476811105179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52413296046713271496280477 19654986017517476811105179)
      ·
        refine ⟨29482479026276215216657769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19654986017517476811105179 29482479026276215216657769)
        ·
          refine ⟨22111859269707161412493327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29482479026276215216657769 22111859269707161412493327)
          ·
            refine ⟨33167788904560742118739991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22111859269707161412493327 33167788904560742118739991)
            ·
              refine ⟨49751683356841113178109987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33167788904560742118739991 49751683356841113178109987)
              ·
                refine ⟨74627525035261669767164981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49751683356841113178109987 74627525035261669767164981)
                ·
                  refine ⟨6996330472055781540671717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74627525035261669767164981 6996330472055781540671717)
                  ·
                    refine ⟨1311811963510459038875947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6996330472055781540671717 1311811963510459038875947)
                    ·
                      rfl

theorem cell22_3832117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3832117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832117 prefixEnd_3832117 := by exact prefixLift 3832117
  have htrace : WordTrace (prefixWord ++ tailWord_3832117) baseStart_3832117 baseEnd_3832117 := by
    simpa [prefixWord, tailWord_3832117, baseEnd_3832117] using wordTrace_append hprefix tailTrace_3832117
  have hstable : (prefixWord ++ tailWord_3832117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832117).length < 2 ^ (prefixWord ++ tailWord_3832117).sum := by decide
  have hdescent : baseEnd_3832117 < baseStart_3832117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832164 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_3832164 : Nat := 118140960795 + 3832164 * 2 ^ 59
def prefixEnd_3832164 : Nat := 4983230072969 + 3 ^ 40 * 3832164 * 2
def baseEnd_3832164 : Nat := 1311828052570966582950803

theorem tailTrace_3832164 : CollatzResearch.WordTrace tailWord_3832164 prefixEnd_3832164 1311828052570966582950803 := by
  unfold tailWord_3832164
  simp only [CollatzResearch.WordTrace]
  refine ⟨69885251844365892175187773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93180335792487856233583697 69885251844365892175187773)
  ·
    refine ⟨26206969441637209565695415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69885251844365892175187773 26206969441637209565695415)
    ·
      refine ⟨39310454162455814348543123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26206969441637209565695415 39310454162455814348543123)
      ·
        refine ⟨58965681243683721522814685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39310454162455814348543123 58965681243683721522814685)
        ·
          refine ⟨22112130466381395571055507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58965681243683721522814685 22112130466381395571055507)
          ·
            refine ⟨33168195699572093356583261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22112130466381395571055507 33168195699572093356583261)
            ·
              refine ⟨12438073387339535008718723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33168195699572093356583261 12438073387339535008718723)
              ·
                refine ⟨18657110081009302513078085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12438073387339535008718723 18657110081009302513078085)
                ·
                  refine ⟨3498208140189244221202141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18657110081009302513078085 3498208140189244221202141)
                  ·
                    refine ⟨1311828052570966582950803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498208140189244221202141 1311828052570966582950803)
                    ·
                      rfl

theorem cell22_3832164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_3832164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832164 prefixEnd_3832164 := by exact prefixLift 3832164
  have htrace : WordTrace (prefixWord ++ tailWord_3832164) baseStart_3832164 baseEnd_3832164 := by
    simpa [prefixWord, tailWord_3832164, baseEnd_3832164] using wordTrace_append hprefix tailTrace_3832164
  have hstable : (prefixWord ++ tailWord_3832164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832164).length < 2 ^ (prefixWord ++ tailWord_3832164).sum := by decide
  have hdescent : baseEnd_3832164 < baseStart_3832164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832181 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3832181 : Nat := 118140960795 + 3832181 * 2 ^ 59
def prefixEnd_3832181 : Nat := 4983230072969 + 3 ^ 40 * 3832181 * 2
def baseEnd_3832181 : Nat := 1311833872018384205275751

theorem tailTrace_3832181 : CollatzResearch.WordTrace tailWord_3832181 prefixEnd_3832181 1311833872018384205275751 := by
  unfold tailWord_3832181
  simp only [CollatzResearch.WordTrace]
  refine ⟨139771123729670196253744397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93180749153113464169162931 139771123729670196253744397)
  ·
    refine ⟨52414171398626323595154149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139771123729670196253744397 52414171398626323595154149)
    ·
      refine ⟨9827657137242435674091403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52414171398626323595154149 9827657137242435674091403)
      ·
        refine ⟨14741485705863653511137105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827657137242435674091403 14741485705863653511137105)
        ·
          refine ⟨11056114279397740133352829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14741485705863653511137105 11056114279397740133352829)
          ·
            refine ⟨4146042854774152550007311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11056114279397740133352829 4146042854774152550007311)
            ·
              refine ⟨6219064282161228825010967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146042854774152550007311 6219064282161228825010967)
              ·
                refine ⟨9328596423241843237516451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219064282161228825010967 9328596423241843237516451)
                ·
                  refine ⟨13992894634862764856274677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9328596423241843237516451 13992894634862764856274677)
                  ·
                    refine ⟨1311833872018384205275751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13992894634862764856274677 1311833872018384205275751)
                    ·
                      rfl

theorem cell22_3832181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3832181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832181 prefixEnd_3832181 := by exact prefixLift 3832181
  have htrace : WordTrace (prefixWord ++ tailWord_3832181) baseStart_3832181 baseEnd_3832181 := by
    simpa [prefixWord, tailWord_3832181, baseEnd_3832181] using wordTrace_append hprefix tailTrace_3832181
  have hstable : (prefixWord ++ tailWord_3832181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832181).length < 2 ^ (prefixWord ++ tailWord_3832181).sum := by decide
  have hdescent : baseEnd_3832181 < baseStart_3832181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832299 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 1, 5]
def baseStart_3832299 : Nat := 118140960795 + 3832299 * 2 ^ 59
def prefixEnd_3832299 : Nat := 4983230072969 + 3 ^ 40 * 3832299 * 2
def baseEnd_3832299 : Nat := 1311874265829871230825389

theorem tailTrace_3832299 : CollatzResearch.WordTrace tailWord_3832299 prefixEnd_3832299 1311874265829871230825389 := by
  unfold tailWord_3832299
  simp only [CollatzResearch.WordTrace]
  refine ⟨139775427543242702406539951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93183618362161801604359967 139775427543242702406539951)
  ·
    refine ⟨209663141314864053609809927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139775427543242702406539951 209663141314864053609809927)
    ·
      refine ⟨314494711972296080414714891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209663141314864053609809927 314494711972296080414714891)
      ·
        refine ⟨471742067958444120622072337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314494711972296080414714891 471742067958444120622072337)
        ·
          refine ⟨353806550968833090466554253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471742067958444120622072337 353806550968833090466554253)
          ·
            refine ⟨132677456613312408924957845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353806550968833090466554253 132677456613312408924957845)
            ·
              refine ⟨6219255778749019168357399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132677456613312408924957845 6219255778749019168357399)
              ·
                refine ⟨9328883668123528752536099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219255778749019168357399 9328883668123528752536099)
                ·
                  refine ⟨13993325502185293128804149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9328883668123528752536099 13993325502185293128804149)
                  ·
                    refine ⟨1311874265829871230825389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13993325502185293128804149 1311874265829871230825389)
                    ·
                      rfl

theorem cell22_3832299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 5].length) (baseStart_3832299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832299 prefixEnd_3832299 := by exact prefixLift 3832299
  have htrace : WordTrace (prefixWord ++ tailWord_3832299) baseStart_3832299 baseEnd_3832299 := by
    simpa [prefixWord, tailWord_3832299, baseEnd_3832299] using wordTrace_append hprefix tailTrace_3832299
  have hstable : (prefixWord ++ tailWord_3832299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832299).length < 2 ^ (prefixWord ++ tailWord_3832299).sum := by decide
  have hdescent : baseEnd_3832299 < baseStart_3832299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832301 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 6]
def baseStart_3832301 : Nat := 118140960795 + 3832301 * 2 ^ 59
def prefixEnd_3832301 : Nat := 4983230072969 + 3 ^ 40 * 3832301 * 2
def baseEnd_3832301 : Nat := 437291650156914630758461

theorem tailTrace_3832301 : CollatzResearch.WordTrace tailWord_3832301 prefixEnd_3832301 437291650156914630758461 := by
  unfold tailWord_3832301
  simp only [CollatzResearch.WordTrace]
  refine ⟨139775500489235456748112757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93183666992823637832075171 139775500489235456748112757)
  ·
    refine ⟨13103953170865824070135571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139775500489235456748112757 13103953170865824070135571)
    ·
      refine ⟨19655929756298736105203357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13103953170865824070135571 19655929756298736105203357)
      ·
        refine ⟨7370973658612026039451259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19655929756298736105203357 7370973658612026039451259)
        ·
          refine ⟨11056460487918039059176889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7370973658612026039451259 11056460487918039059176889)
          ·
            refine ⟨8292345365938529294382667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11056460487918039059176889 8292345365938529294382667)
            ·
              refine ⟨12438518048907793941574001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292345365938529294382667 12438518048907793941574001)
              ·
                refine ⟨9328888536680845456180501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12438518048907793941574001 9328888536680845456180501)
                ·
                  refine ⟨437291650156914630758461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9328888536680845456180501 437291650156914630758461)
                  ·
                    rfl

theorem cell22_3832301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_3832301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832301 prefixEnd_3832301 := by exact prefixLift 3832301
  have htrace : WordTrace (prefixWord ++ tailWord_3832301) baseStart_3832301 baseEnd_3832301 := by
    simpa [prefixWord, tailWord_3832301, baseEnd_3832301] using wordTrace_append hprefix tailTrace_3832301
  have hstable : (prefixWord ++ tailWord_3832301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832301).length < 2 ^ (prefixWord ++ tailWord_3832301).sum := by decide
  have hdescent : baseEnd_3832301 < baseStart_3832301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832314 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_3832314 : Nat := 118140960795 + 3832314 * 2 ^ 59
def prefixEnd_3832314 : Nat := 4983230072969 + 3 ^ 40 * 3832314 * 2
def baseEnd_3832314 : Nat := 1311879400636416191700343

theorem tailTrace_3832314 : CollatzResearch.WordTrace tailWord_3832314 prefixEnd_3832314 1311879400636416191700343 := by
  unfold tailWord_3832314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34943993659547089992083999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93183983092125573312223997 34943993659547089992083999)
  ·
    refine ⟨52415990489320634988125999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34943993659547089992083999 52415990489320634988125999)
    ·
      refine ⟨78623985733980952482188999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52415990489320634988125999 78623985733980952482188999)
      ·
        refine ⟨117935978600971428723283499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78623985733980952482188999 117935978600971428723283499)
        ·
          refine ⟨176903967901457143084925249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117935978600971428723283499 176903967901457143084925249)
          ·
            refine ⟨132677975926092857313693937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176903967901457143084925249 132677975926092857313693937)
            ·
              refine ⟨99508481944569642985270453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132677975926092857313693937 99508481944569642985270453)
              ·
                refine ⟨9328920182303404029869105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99508481944569642985270453 9328920182303404029869105)
                ·
                  refine ⟨6996690136727553022401829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9328920182303404029869105 6996690136727553022401829)
                  ·
                    refine ⟨1311879400636416191700343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6996690136727553022401829 1311879400636416191700343)
                    ·
                      rfl

theorem cell22_3832314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_3832314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832314 prefixEnd_3832314 := by exact prefixLift 3832314
  have htrace : WordTrace (prefixWord ++ tailWord_3832314) baseStart_3832314 baseEnd_3832314 := by
    simpa [prefixWord, tailWord_3832314, baseEnd_3832314] using wordTrace_append hprefix tailTrace_3832314
  have hstable : (prefixWord ++ tailWord_3832314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832314).length < 2 ^ (prefixWord ++ tailWord_3832314).sum := by decide
  have hdescent : baseEnd_3832314 < baseStart_3832314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832419 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 8]
def baseStart_3832419 : Nat := 118140960795 + 3832419 * 2 ^ 59
def prefixEnd_3832419 : Nat := 4983230072969 + 3 ^ 40 * 3832419 * 2
def baseEnd_3832419 : Nat := 437305114760743639275007

theorem tailTrace_3832419 : CollatzResearch.WordTrace tailWord_3832419 prefixEnd_3832419 437305114760743639275007 := by
  unfold tailWord_3832419
  simp only [CollatzResearch.WordTrace]
  refine ⟨139779804302807962900908311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93186536201871975267272207 139779804302807962900908311)
  ·
    refine ⟨209669706454211944351362467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139779804302807962900908311 209669706454211944351362467)
    ·
      refine ⟨314504559681317916527043701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209669706454211944351362467 314504559681317916527043701)
      ·
        refine ⟨29484802470123554674410347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314504559681317916527043701 29484802470123554674410347)
        ·
          refine ⟨44227203705185332011615521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29484802470123554674410347 44227203705185332011615521)
          ·
            refine ⟨33170402778888999008711641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44227203705185332011615521 33170402778888999008711641)
            ·
              refine ⟨24877802084166749256533731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33170402778888999008711641 24877802084166749256533731)
              ·
                refine ⟨37316703126250123884800597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24877802084166749256533731 37316703126250123884800597)
                ·
                  refine ⟨437305114760743639275007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37316703126250123884800597 437305114760743639275007)
                  ·
                    rfl

theorem cell22_3832419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 8].length) (baseStart_3832419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832419 prefixEnd_3832419 := by exact prefixLift 3832419
  have htrace : WordTrace (prefixWord ++ tailWord_3832419) baseStart_3832419 baseEnd_3832419 := by
    simpa [prefixWord, tailWord_3832419, baseEnd_3832419] using wordTrace_append hprefix tailTrace_3832419
  have hstable : (prefixWord ++ tailWord_3832419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832419).length < 2 ^ (prefixWord ++ tailWord_3832419).sum := by decide
  have hdescent : baseEnd_3832419 < baseStart_3832419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832451 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 4, 3]
def baseStart_3832451 : Nat := 118140960795 + 3832451 * 2 ^ 59
def prefixEnd_3832451 : Nat := 4983230072969 + 3 ^ 40 * 3832451 * 2
def baseEnd_3832451 : Nat := 1311926298536193501024923

theorem tailTrace_3832451 : CollatzResearch.WordTrace tailWord_3832451 prefixEnd_3832451 1311926298536193501024923 := by
  unfold tailWord_3832451
  simp only [CollatzResearch.WordTrace]
  refine ⟨139780971438692032366073207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93187314292461354910715471 139780971438692032366073207)
  ·
    refine ⟨209671457158038048549109811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139780971438692032366073207 209671457158038048549109811)
    ·
      refine ⟨314507185737057072823664717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209671457158038048549109811 314507185737057072823664717)
      ·
        refine ⟨117940194651396402308874269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 314507185737057072823664717 117940194651396402308874269)
        ·
          refine ⟨44227572994273650865827851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117940194651396402308874269 44227572994273650865827851)
          ·
            refine ⟨66341359491410476298741777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44227572994273650865827851 66341359491410476298741777)
            ·
              refine ⟨49756019618557857224056333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66341359491410476298741777 49756019618557857224056333)
              ·
                refine ⟨18658507356959196459021125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49756019618557857224056333 18658507356959196459021125)
                ·
                  refine ⟨3498470129429849336066461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18658507356959196459021125 3498470129429849336066461)
                  ·
                    refine ⟨1311926298536193501024923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498470129429849336066461 1311926298536193501024923)
                    ·
                      rfl

theorem cell22_3832451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 3].length) (baseStart_3832451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832451 prefixEnd_3832451 := by exact prefixLift 3832451
  have htrace : WordTrace (prefixWord ++ tailWord_3832451) baseStart_3832451 baseEnd_3832451 := by
    simpa [prefixWord, tailWord_3832451, baseEnd_3832451] using wordTrace_append hprefix tailTrace_3832451
  have hstable : (prefixWord ++ tailWord_3832451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832451).length < 2 ^ (prefixWord ++ tailWord_3832451).sum := by decide
  have hdescent : baseEnd_3832451 < baseStart_3832451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832453 : List Nat := [1, 3, 1, 1, 4, 3, 1, 4, 4]
def baseStart_3832453 : Nat := 118140960795 + 3832453 * 2 ^ 59
def prefixEnd_3832453 : Nat := 4983230072969 + 3 ^ 40 * 3832453 * 2
def baseEnd_3832453 : Nat := 437308994392355387491639

theorem tailTrace_3832453 : CollatzResearch.WordTrace tailWord_3832453 prefixEnd_3832453 437308994392355387491639 := by
  unfold tailWord_3832453
  simp only [CollatzResearch.WordTrace]
  refine ⟨139781044384684786707646013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93187362923123191138430675 139781044384684786707646013)
  ·
    refine ⟨52417891644256795015367255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139781044384684786707646013 52417891644256795015367255)
    ·
      refine ⟨78626837466385192523050883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52417891644256795015367255 78626837466385192523050883)
      ·
        refine ⟨117940256199577788784576325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78626837466385192523050883 117940256199577788784576325)
        ·
          refine ⟨22113798037420835397108061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117940256199577788784576325 22113798037420835397108061)
          ·
            refine ⟨8292674264032813273915523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22113798037420835397108061 8292674264032813273915523)
            ·
              refine ⟨12439011396049219910873285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292674264032813273915523 12439011396049219910873285)
              ·
                refine ⟨2332314636759228733288741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12439011396049219910873285 2332314636759228733288741)
                ·
                  refine ⟨437308994392355387491639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2332314636759228733288741 437308994392355387491639)
                  ·
                    rfl

theorem cell22_3832453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_3832453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832453 prefixEnd_3832453 := by exact prefixLift 3832453
  have htrace : WordTrace (prefixWord ++ tailWord_3832453) baseStart_3832453 baseEnd_3832453 := by
    simpa [prefixWord, tailWord_3832453, baseEnd_3832453] using wordTrace_append hprefix tailTrace_3832453
  have hstable : (prefixWord ++ tailWord_3832453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832453).length < 2 ^ (prefixWord ++ tailWord_3832453).sum := by decide
  have hdescent : baseEnd_3832453 < baseStart_3832453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832468 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3832468 : Nat := 118140960795 + 3832468 * 2 ^ 59
def prefixEnd_3832468 : Nat := 4983230072969 + 3 ^ 40 * 3832468 * 2
def baseEnd_3832468 : Nat := 1311932117983611123349871

theorem tailTrace_3832468 : CollatzResearch.WordTrace tailWord_3832468 prefixEnd_3832468 1311932117983611123349871 := by
  unfold tailWord_3832468
  simp only [CollatzResearch.WordTrace]
  refine ⟨69890795739815222134721029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93187727653086962846294705 69890795739815222134721029)
  ·
    refine ⟨13104524201215354150260193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69890795739815222134721029 13104524201215354150260193)
    ·
      refine ⟨9828393150911515612695145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13104524201215354150260193 9828393150911515612695145)
      ·
        refine ⟨7371294863183636709521359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9828393150911515612695145 7371294863183636709521359)
        ·
          refine ⟨11056942294775455064282039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371294863183636709521359 11056942294775455064282039)
          ·
            refine ⟨16585413442163182596423059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11056942294775455064282039 16585413442163182596423059)
            ·
              refine ⟨24878120163244773894634589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16585413442163182596423059 24878120163244773894634589)
              ·
                refine ⟨9329295061216790210487971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24878120163244773894634589 9329295061216790210487971)
                ·
                  refine ⟨13993942591825185315731957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329295061216790210487971 13993942591825185315731957)
                  ·
                    refine ⟨1311932117983611123349871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13993942591825185315731957 1311932117983611123349871)
                    ·
                      rfl

theorem cell22_3832468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3832468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832468 prefixEnd_3832468 := by exact prefixLift 3832468
  have htrace : WordTrace (prefixWord ++ tailWord_3832468) baseStart_3832468 baseEnd_3832468 := by
    simpa [prefixWord, tailWord_3832468, baseEnd_3832468] using wordTrace_append hprefix tailTrace_3832468
  have hstable : (prefixWord ++ tailWord_3832468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832468).length < 2 ^ (prefixWord ++ tailWord_3832468).sum := by decide
  have hdescent : baseEnd_3832468 < baseStart_3832468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832487 : List Nat := [1, 1, 6, 3, 1, 1, 2, 3, 4]
def baseStart_3832487 : Nat := 118140960795 + 3832487 * 2 ^ 59
def prefixEnd_3832487 : Nat := 4983230072969 + 3 ^ 40 * 3832487 * 2
def baseEnd_3832487 : Nat := 437312874023967135708271

theorem tailTrace_3832487 : CollatzResearch.WordTrace tailWord_3832487 prefixEnd_3832487 437312874023967135708271 := by
  unfold tailWord_3832487
  simp only [CollatzResearch.WordTrace]
  refine ⟨139782284466561610514383715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93188189644374407009589143 139782284466561610514383715)
  ·
    refine ⟨209673426699842415771575573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139782284466561610514383715 209673426699842415771575573)
    ·
      refine ⟨9828441876555113239292605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209673426699842415771575573 9828441876555113239292605)
      ·
        refine ⟨3685665703708167464734727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9828441876555113239292605 3685665703708167464734727)
        ·
          refine ⟨5528498555562251197102091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685665703708167464734727 5528498555562251197102091)
          ·
            refine ⟨8292747833343376795653137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528498555562251197102091 8292747833343376795653137)
            ·
              refine ⟨6219560875007532596739853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8292747833343376795653137 6219560875007532596739853)
              ·
                refine ⟨2332335328127824723777445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6219560875007532596739853 2332335328127824723777445)
                ·
                  refine ⟨437312874023967135708271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2332335328127824723777445 437312874023967135708271)
                  ·
                    rfl

theorem cell22_3832487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 4].length) (baseStart_3832487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832487 prefixEnd_3832487 := by exact prefixLift 3832487
  have htrace : WordTrace (prefixWord ++ tailWord_3832487) baseStart_3832487 baseEnd_3832487 := by
    simpa [prefixWord, tailWord_3832487, baseEnd_3832487] using wordTrace_append hprefix tailTrace_3832487
  have hstable : (prefixWord ++ tailWord_3832487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832487).length < 2 ^ (prefixWord ++ tailWord_3832487).sum := by decide
  have hdescent : baseEnd_3832487 < baseStart_3832487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832496 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 7, 3]
def baseStart_3832496 : Nat := 118140960795 + 3832496 * 2 ^ 59
def prefixEnd_3832496 : Nat := 4983230072969 + 3 ^ 40 * 3832496 * 2
def baseEnd_3832496 : Nat := 1311941702955828383649785

theorem tailTrace_3832496 : CollatzResearch.WordTrace tailWord_3832496 prefixEnd_3832496 1311941702955828383649785 := by
  unfold tailWord_3832496
  simp only [CollatzResearch.WordTrace]
  refine ⟨69891306361764502525730671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93188408482352670034307561 69891306361764502525730671)
  ·
    refine ⟨104836959542646753788596007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69891306361764502525730671 104836959542646753788596007)
    ·
      refine ⟨157255439313970130682894011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104836959542646753788596007 157255439313970130682894011)
      ·
        refine ⟨235883158970955196024341017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157255439313970130682894011 235883158970955196024341017)
        ·
          refine ⟨176912369228216397018255763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235883158970955196024341017 176912369228216397018255763)
          ·
            refine ⟨265368553842324595527383645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176912369228216397018255763 265368553842324595527383645)
            ·
              refine ⟨99513207690871723322768867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265368553842324595527383645 99513207690871723322768867)
              ·
                refine ⟨149269811536307584984153301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99513207690871723322768867 149269811536307584984153301)
                ·
                  refine ⟨3498511207882209023066093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 149269811536307584984153301 3498511207882209023066093)
                  ·
                    refine ⟨1311941702955828383649785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498511207882209023066093 1311941702955828383649785)
                    ·
                      rfl

theorem cell22_3832496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_3832496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832496 prefixEnd_3832496 := by exact prefixLift 3832496
  have htrace : WordTrace (prefixWord ++ tailWord_3832496) baseStart_3832496 baseEnd_3832496 := by
    simpa [prefixWord, tailWord_3832496, baseEnd_3832496] using wordTrace_append hprefix tailTrace_3832496
  have hstable : (prefixWord ++ tailWord_3832496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832496).length < 2 ^ (prefixWord ++ tailWord_3832496).sum := by decide
  have hdescent : baseEnd_3832496 < baseStart_3832496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832502 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3832502 : Nat := 118140960795 + 3832502 * 2 ^ 59
def prefixEnd_3832502 : Nat := 4983230072969 + 3 ^ 40 * 3832502 * 2
def baseEnd_3832502 : Nat := 1311943756878446367999767

theorem tailTrace_3832502 : CollatzResearch.WordTrace tailWord_3832502 prefixEnd_3832502 1311943756878446367999767 := by
  unfold tailWord_3832502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8736426972594204254761235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93188554374338178717453173 8736426972594204254761235)
  ·
    refine ⟨13104640458891306382141853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8736426972594204254761235 13104640458891306382141853)
    ·
      refine ⟨4914240172084239893303195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13104640458891306382141853 4914240172084239893303195)
      ·
        refine ⟨7371360258126359839954793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914240172084239893303195 7371360258126359839954793)
        ·
          refine ⟨5528520193594769879966095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7371360258126359839954793 5528520193594769879966095)
          ·
            refine ⟨8292780290392154819949143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528520193594769879966095 8292780290392154819949143)
            ·
              refine ⟨12439170435588232229923715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292780290392154819949143 12439170435588232229923715)
              ·
                refine ⟨18658755653382348344885573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12439170435588232229923715 18658755653382348344885573)
                ·
                  refine ⟨3498516685009190314666045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18658755653382348344885573 3498516685009190314666045)
                  ·
                    refine ⟨1311943756878446367999767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498516685009190314666045 1311943756878446367999767)
                    ·
                      rfl

theorem cell22_3832502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3832502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832502 prefixEnd_3832502 := by exact prefixLift 3832502
  have htrace : WordTrace (prefixWord ++ tailWord_3832502) baseStart_3832502 baseEnd_3832502 := by
    simpa [prefixWord, tailWord_3832502, baseEnd_3832502] using wordTrace_append hprefix tailTrace_3832502
  have hstable : (prefixWord ++ tailWord_3832502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832502).length < 2 ^ (prefixWord ++ tailWord_3832502).sum := by decide
  have hdescent : baseEnd_3832502 < baseStart_3832502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832532 : List Nat := [2, 4, 1, 3, 3, 1, 2, 6]
def baseStart_3832532 : Nat := 118140960795 + 3832532 * 2 ^ 59
def prefixEnd_3832532 : Nat := 4983230072969 + 3 ^ 40 * 3832532 * 2
def baseEnd_3832532 : Nat := 145772669610170698861075

theorem tailTrace_3832532 : CollatzResearch.WordTrace tailWord_3832532 prefixEnd_3832532 145772669610170698861075 := by
  unfold tailWord_3832532
  simp only [CollatzResearch.WordTrace]
  refine ⟨69891962875699291599885925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93189283834265722133181233 69891962875699291599885925)
  ·
    refine ⟨13104743039193617174978611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69891962875699291599885925 13104743039193617174978611)
    ·
      refine ⟨19657114558790425762467917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13104743039193617174978611 19657114558790425762467917)
      ·
        refine ⟨7371417959546409660925469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19657114558790425762467917 7371417959546409660925469)
        ·
          refine ⟨2764281734829903622847051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7371417959546409660925469 2764281734829903622847051)
          ·
            refine ⟨4146422602244855434270577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764281734829903622847051 4146422602244855434270577)
            ·
              refine ⟨3109816951683641575702933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4146422602244855434270577 3109816951683641575702933)
              ·
                refine ⟨145772669610170698861075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3109816951683641575702933 145772669610170698861075)
                ·
                  rfl

theorem cell22_3832532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 6].length) (baseStart_3832532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832532 prefixEnd_3832532 := by exact prefixLift 3832532
  have htrace : WordTrace (prefixWord ++ tailWord_3832532) baseStart_3832532 baseEnd_3832532 := by
    simpa [prefixWord, tailWord_3832532, baseEnd_3832532] using wordTrace_append hprefix tailTrace_3832532
  have hstable : (prefixWord ++ tailWord_3832532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832532).length < 2 ^ (prefixWord ++ tailWord_3832532).sum := by decide
  have hdescent : baseEnd_3832532 < baseStart_3832532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832547 : List Nat := [1, 1, 1, 7, 1, 1, 3, 3, 1, 3]
def baseStart_3832547 : Nat := 118140960795 + 3832547 * 2 ^ 59
def prefixEnd_3832547 : Nat := 4983230072969 + 3 ^ 40 * 3832547 * 2
def baseEnd_3832547 : Nat := 1311959161298081250624629

theorem tailTrace_3832547 : CollatzResearch.WordTrace tailWord_3832547 prefixEnd_3832547 1311959161298081250624629 := by
  unfold tailWord_3832547
  simp only [CollatzResearch.WordTrace]
  refine ⟨139784472846344240761567895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93189648564229493841045263 139784472846344240761567895)
  ·
    refine ⟨209676709269516361142351843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139784472846344240761567895 209676709269516361142351843)
    ·
      refine ⟨314515063904274541713527765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209676709269516361142351843 314515063904274541713527765)
      ·
        refine ⟨7371446810256434571410807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 314515063904274541713527765 7371446810256434571410807)
        ·
          refine ⟨11057170215384651857116211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371446810256434571410807 11057170215384651857116211)
          ·
            refine ⟨16585755323076977785674317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057170215384651857116211 16585755323076977785674317)
            ·
              refine ⟨6219658246153866669627869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16585755323076977785674317 6219658246153866669627869)
              ·
                refine ⟨2332371842307700001110451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6219658246153866669627869 2332371842307700001110451)
                ·
                  refine ⟨3498557763461550001665677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332371842307700001110451 3498557763461550001665677)
                  ·
                    refine ⟨1311959161298081250624629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498557763461550001665677 1311959161298081250624629)
                    ·
                      rfl

theorem cell22_3832547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 3].length) (baseStart_3832547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832547 prefixEnd_3832547 := by exact prefixLift 3832547
  have htrace : WordTrace (prefixWord ++ tailWord_3832547) baseStart_3832547 baseEnd_3832547 := by
    simpa [prefixWord, tailWord_3832547, baseEnd_3832547] using wordTrace_append hprefix tailTrace_3832547
  have hstable : (prefixWord ++ tailWord_3832547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832547).length < 2 ^ (prefixWord ++ tailWord_3832547).sum := by decide
  have hdescent : baseEnd_3832547 < baseStart_3832547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832556 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_3832556 : Nat := 118140960795 + 3832556 * 2 ^ 59
def prefixEnd_3832556 : Nat := 4983230072969 + 3 ^ 40 * 3832556 * 2
def baseEnd_3832556 : Nat := 1311962242182008227149601

theorem tailTrace_3832556 : CollatzResearch.WordTrace tailWord_3832556 prefixEnd_3832556 1311962242182008227149601 := by
  unfold tailWord_3832556
  simp only [CollatzResearch.WordTrace]
  refine ⟨69892400551655817649322761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93189867402207756865763681 69892400551655817649322761)
  ·
    refine ⟨52419300413741863236992071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69892400551655817649322761 52419300413741863236992071)
    ·
      refine ⟨78628950620612794855488107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52419300413741863236992071 78628950620612794855488107)
      ·
        refine ⟨117943425930919192283232161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78628950620612794855488107 117943425930919192283232161)
        ·
          refine ⟨88457569448189394212424121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117943425930919192283232161 88457569448189394212424121)
          ·
            refine ⟨66343177086142045659318091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88457569448189394212424121 66343177086142045659318091)
            ·
              refine ⟨99514765629213068488977137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66343177086142045659318091 99514765629213068488977137)
              ·
                refine ⟨74636074221909801366732853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99514765629213068488977137 74636074221909801366732853)
                ·
                  refine ⟨6997131958304043878131205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74636074221909801366732853 6997131958304043878131205)
                  ·
                    refine ⟨1311962242182008227149601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997131958304043878131205 1311962242182008227149601)
                    ·
                      rfl

theorem cell22_3832556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_3832556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832556 prefixEnd_3832556 := by exact prefixLift 3832556
  have htrace : WordTrace (prefixWord ++ tailWord_3832556) baseStart_3832556 baseEnd_3832556 := by
    simpa [prefixWord, tailWord_3832556, baseEnd_3832556] using wordTrace_append hprefix tailTrace_3832556
  have hstable : (prefixWord ++ tailWord_3832556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832556).length < 2 ^ (prefixWord ++ tailWord_3832556).sum := by decide
  have hdescent : baseEnd_3832556 < baseStart_3832556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832620 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_3832620 : Nat := 118140960795 + 3832620 * 2 ^ 59
def prefixEnd_3832620 : Nat := 4983230072969 + 3 ^ 40 * 3832620 * 2
def baseEnd_3832620 : Nat := 1311984150689933393549405

theorem tailTrace_3832620 : CollatzResearch.WordTrace tailWord_3832620 prefixEnd_3832620 1311984150689933393549405 := by
  unfold tailWord_3832620
  simp only [CollatzResearch.WordTrace]
  refine ⟨69893567687539887114487657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93191423583386516152650209 69893567687539887114487657)
  ·
    refine ⟨52420175765654915335865743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69893567687539887114487657 52420175765654915335865743)
    ·
      refine ⟨78630263648482373003798615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52420175765654915335865743 78630263648482373003798615)
      ·
        refine ⟨117945395472723559505697923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78630263648482373003798615 117945395472723559505697923)
        ·
          refine ⟨176918093209085339258546885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117945395472723559505697923 176918093209085339258546885)
          ·
            refine ⟨33172142476703501110977541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176918093209085339258546885 33172142476703501110977541)
            ·
              refine ⟨6219776714381906458308289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33172142476703501110977541 6219776714381906458308289)
              ·
                refine ⟨4664832535786429843731217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6219776714381906458308289 4664832535786429843731217)
                ·
                  refine ⟨3498624401839822382798413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4664832535786429843731217 3498624401839822382798413)
                  ·
                    refine ⟨1311984150689933393549405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498624401839822382798413 1311984150689933393549405)
                    ·
                      rfl

theorem cell22_3832620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_3832620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832620 prefixEnd_3832620 := by exact prefixLift 3832620
  have htrace : WordTrace (prefixWord ++ tailWord_3832620) baseStart_3832620 baseEnd_3832620 := by
    simpa [prefixWord, tailWord_3832620, baseEnd_3832620] using wordTrace_append hprefix tailTrace_3832620
  have hstable : (prefixWord ++ tailWord_3832620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832620).length < 2 ^ (prefixWord ++ tailWord_3832620).sum := by decide
  have hdescent : baseEnd_3832620 < baseStart_3832620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832622 : List Nat := [4, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_3832622 : Nat := 118140960795 + 3832622 * 2 ^ 59
def prefixEnd_3832622 : Nat := 4983230072969 + 3 ^ 40 * 3832622 * 2
def baseEnd_3832622 : Nat := 437328278443602018333133

theorem tailTrace_3832622 : CollatzResearch.WordTrace tailWord_3832622 prefixEnd_3832622 437328278443602018333133 := by
  unfold tailWord_3832622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17473401040134066071318515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93191472214048352380365413 17473401040134066071318515)
  ·
    refine ⟨26210101560201099106977773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17473401040134066071318515 26210101560201099106977773)
    ·
      refine ⟨9828788085075412165116665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26210101560201099106977773 9828788085075412165116665)
      ·
        refine ⟨7371591063806559123837499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9828788085075412165116665 7371591063806559123837499)
        ·
          refine ⟨11057386595709838685756249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371591063806559123837499 11057386595709838685756249)
          ·
            refine ⟨8293039946782379014317187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11057386595709838685756249 8293039946782379014317187)
            ·
              refine ⟨12439559920173568521475781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8293039946782379014317187 12439559920173568521475781)
              ·
                refine ⟨2332417485032544097776709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12439559920173568521475781 2332417485032544097776709)
                ·
                  refine ⟨437328278443602018333133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2332417485032544097776709 437328278443602018333133)
                  ·
                    rfl

theorem cell22_3832622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_3832622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832622 prefixEnd_3832622 := by exact prefixLift 3832622
  have htrace : WordTrace (prefixWord ++ tailWord_3832622) baseStart_3832622 baseEnd_3832622 := by
    simpa [prefixWord, tailWord_3832622, baseEnd_3832622] using wordTrace_append hprefix tailTrace_3832622
  have hstable : (prefixWord ++ tailWord_3832622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832622).length < 2 ^ (prefixWord ++ tailWord_3832622).sum := by decide
  have hdescent : baseEnd_3832622 < baseStart_3832622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832725 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_3832725 : Nat := 118140960795 + 3832725 * 2 ^ 59
def prefixEnd_3832725 : Nat := 4983230072969 + 3 ^ 40 * 3832725 * 2
def baseEnd_3832725 : Nat := 1312020094335748119674083

theorem tailTrace_3832725 : CollatzResearch.WordTrace tailWord_3832725 prefixEnd_3832725 1312020094335748119674083 := by
  unfold tailWord_3832725
  simp only [CollatzResearch.WordTrace]
  refine ⟨139790965039699377161547629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93193976693132918107698419 139790965039699377161547629)
  ·
    refine ⟨52421611889887266435580361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139790965039699377161547629 52421611889887266435580361)
    ·
      refine ⟨39316208917415449826685271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52421611889887266435580361 39316208917415449826685271)
      ·
        refine ⟨58974313376123174740027907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39316208917415449826685271 58974313376123174740027907)
        ·
          refine ⟨88461470064184762110041861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58974313376123174740027907 88461470064184762110041861)
          ·
            refine ⟨16586525637034642895632849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88461470064184762110041861 16586525637034642895632849)
            ·
              refine ⟨12439894227775982171724637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16586525637034642895632849 12439894227775982171724637)
              ·
                refine ⟨4664960335415993314396739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12439894227775982171724637 4664960335415993314396739)
                ·
                  refine ⟨6997440503123989971595109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664960335415993314396739 6997440503123989971595109)
                  ·
                    refine ⟨1312020094335748119674083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997440503123989971595109 1312020094335748119674083)
                    ·
                      rfl

theorem cell22_3832725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_3832725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832725 prefixEnd_3832725 := by exact prefixLift 3832725
  have htrace : WordTrace (prefixWord ++ tailWord_3832725) baseStart_3832725 baseEnd_3832725 := by
    simpa [prefixWord, tailWord_3832725, baseEnd_3832725] using wordTrace_append hprefix tailTrace_3832725
  have hstable : (prefixWord ++ tailWord_3832725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832725).length < 2 ^ (prefixWord ++ tailWord_3832725).sum := by decide
  have hdescent : baseEnd_3832725 < baseStart_3832725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832768 : List Nat := [2, 1, 1, 2, 3, 3, 2, 8]
def baseStart_3832768 : Nat := 118140960795 + 3832768 * 2 ^ 59
def prefixEnd_3832768 : Nat := 4983230072969 + 3 ^ 40 * 3832768 * 2
def baseEnd_3832768 : Nat := 145781646012723371205439

theorem tailTrace_3832768 : CollatzResearch.WordTrace tailWord_3832768 prefixEnd_3832768 145781646012723371205439 := by
  unfold tailWord_3832768
  simp only [CollatzResearch.WordTrace]
  refine ⟨69896266689271797752681479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93195022252362397003575305 69896266689271797752681479)
  ·
    refine ⟨104844400033907696629022219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69896266689271797752681479 104844400033907696629022219)
    ·
      refine ⟨157266600050861544943533329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104844400033907696629022219 157266600050861544943533329)
      ·
        refine ⟨117949950038146158707649997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157266600050861544943533329 117949950038146158707649997)
        ·
          refine ⟨44231231264304809515368749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117949950038146158707649997 44231231264304809515368749)
          ·
            refine ⟨16586711724114303568263281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44231231264304809515368749 16586711724114303568263281)
            ·
              refine ⟨12440033793085727676197461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16586711724114303568263281 12440033793085727676197461)
              ·
                refine ⟨145781646012723371205439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12440033793085727676197461 145781646012723371205439)
                ·
                  rfl

theorem cell22_3832768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 8].length) (baseStart_3832768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832768 prefixEnd_3832768 := by exact prefixLift 3832768
  have htrace : WordTrace (prefixWord ++ tailWord_3832768) baseStart_3832768 baseEnd_3832768 := by
    simpa [prefixWord, tailWord_3832768, baseEnd_3832768] using wordTrace_append hprefix tailTrace_3832768
  have hstable : (prefixWord ++ tailWord_3832768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832768).length < 2 ^ (prefixWord ++ tailWord_3832768).sum := by decide
  have hdescent : baseEnd_3832768 < baseStart_3832768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832789 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_3832789 : Nat := 118140960795 + 3832789 * 2 ^ 59
def prefixEnd_3832789 : Nat := 4983230072969 + 3 ^ 40 * 3832789 * 2
def baseEnd_3832789 : Nat := 1312042002843673286073887

theorem tailTrace_3832789 : CollatzResearch.WordTrace tailWord_3832789 prefixEnd_3832789 1312042002843673286073887 := by
  unfold tailWord_3832789
  simp only [CollatzResearch.WordTrace]
  refine ⟨139793299311467516091877421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93195532874311677394584947 139793299311467516091877421)
  ·
    refine ⟨52422487241800318534454033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139793299311467516091877421 52422487241800318534454033)
    ·
      refine ⟨39316865431350238900840525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52422487241800318534454033 39316865431350238900840525)
      ·
        refine ⟨14743824536756339587815197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39316865431350238900840525 14743824536756339587815197)
        ·
          refine ⟨5528934201283627345430699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14743824536756339587815197 5528934201283627345430699)
          ·
            refine ⟨8293401301925441018146049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528934201283627345430699 8293401301925441018146049)
            ·
              refine ⟨6220050976444080763609537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8293401301925441018146049 6220050976444080763609537)
              ·
                refine ⟨4665038232333060572707153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6220050976444080763609537 4665038232333060572707153)
                ·
                  refine ⟨3498778674249795429530365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4665038232333060572707153 3498778674249795429530365)
                  ·
                    refine ⟨1312042002843673286073887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498778674249795429530365 1312042002843673286073887)
                    ·
                      rfl

theorem cell22_3832789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_3832789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832789 prefixEnd_3832789 := by exact prefixLift 3832789
  have htrace : WordTrace (prefixWord ++ tailWord_3832789) baseStart_3832789 baseEnd_3832789 := by
    simpa [prefixWord, tailWord_3832789, baseEnd_3832789] using wordTrace_append hprefix tailTrace_3832789
  have hstable : (prefixWord ++ tailWord_3832789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832789).length < 2 ^ (prefixWord ++ tailWord_3832789).sum := by decide
  have hdescent : baseEnd_3832789 < baseStart_3832789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832802 : List Nat := [3, 3, 3, 1, 1, 1, 3, 7]
def baseStart_3832802 : Nat := 118140960795 + 3832802 * 2 ^ 59
def prefixEnd_3832802 : Nat := 4983230072969 + 3 ^ 40 * 3832802 * 2
def baseEnd_3832802 : Nat := 145782939223260620610983

theorem tailTrace_3832802 : CollatzResearch.WordTrace tailWord_3832802 prefixEnd_3832802 145782939223260620610983 := by
  unfold tailWord_3832802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34948443365105104828025165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93195848973613612874733773 34948443365105104828025165)
  ·
    refine ⟨13105666261914414310509437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34948443365105104828025165 13105666261914414310509437)
    ·
      refine ⟨4914624848217905366441039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13105666261914414310509437 4914624848217905366441039)
      ·
        refine ⟨7371937272326858049661559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914624848217905366441039 7371937272326858049661559)
        ·
          refine ⟨11057905908490287074492339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371937272326858049661559 11057905908490287074492339)
          ·
            refine ⟨16586858862735430611738509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057905908490287074492339 16586858862735430611738509)
            ·
              refine ⟨6220072073525786479401941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16586858862735430611738509 6220072073525786479401941)
              ·
                refine ⟨145782939223260620610983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6220072073525786479401941 145782939223260620610983)
                ·
                  rfl

theorem cell22_3832802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_3832802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832802 prefixEnd_3832802 := by exact prefixLift 3832802
  have htrace : WordTrace (prefixWord ++ tailWord_3832802) baseStart_3832802 baseEnd_3832802 := by
    simpa [prefixWord, tailWord_3832802, baseEnd_3832802] using wordTrace_append hprefix tailTrace_3832802
  have hstable : (prefixWord ++ tailWord_3832802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832802).length < 2 ^ (prefixWord ++ tailWord_3832802).sum := by decide
  have hdescent : baseEnd_3832802 < baseStart_3832802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832817 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 3, 3]
def baseStart_3832817 : Nat := 118140960795 + 3832817 * 2 ^ 59
def prefixEnd_3832817 : Nat := 4983230072969 + 3 ^ 40 * 3832817 * 2
def baseEnd_3832817 : Nat := 1312051587815890546373801

theorem tailTrace_3832817 : CollatzResearch.WordTrace tailWord_3832817 prefixEnd_3832817 1312051587815890546373801 := by
  unfold tailWord_3832817
  simp only [CollatzResearch.WordTrace]
  refine ⟨139794320555366076873896705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93196213703577384582597803 139794320555366076873896705)
  ·
    refine ⟨104845740416524557655422529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139794320555366076873896705 104845740416524557655422529)
    ·
      refine ⟨78634305312393418241566897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104845740416524557655422529 78634305312393418241566897)
      ·
        refine ⟨58975728984295063681175173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78634305312393418241566897 58975728984295063681175173)
        ·
          refine ⟨11057949184555324440220345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58975728984295063681175173 11057949184555324440220345)
          ·
            refine ⟨8293461888416493330165259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11057949184555324440220345 8293461888416493330165259)
            ·
              refine ⟨12440192832624739995247889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8293461888416493330165259 12440192832624739995247889)
              ·
                refine ⟨9330144624468554996435917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12440192832624739995247889 9330144624468554996435917)
                ·
                  refine ⟨3498804234175708123663469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9330144624468554996435917 3498804234175708123663469)
                  ·
                    refine ⟨1312051587815890546373801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498804234175708123663469 1312051587815890546373801)
                    ·
                      rfl

theorem cell22_3832817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_3832817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832817 prefixEnd_3832817 := by exact prefixLift 3832817
  have htrace : WordTrace (prefixWord ++ tailWord_3832817) baseStart_3832817 baseEnd_3832817 := by
    simpa [prefixWord, tailWord_3832817, baseEnd_3832817] using wordTrace_append hprefix tailTrace_3832817
  have hstable : (prefixWord ++ tailWord_3832817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832817).length < 2 ^ (prefixWord ++ tailWord_3832817).sum := by decide
  have hdescent : baseEnd_3832817 < baseStart_3832817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832821 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3832821 : Nat := 118140960795 + 3832821 * 2 ^ 59
def prefixEnd_3832821 : Nat := 4983230072969 + 3 ^ 40 * 3832821 * 2
def baseEnd_3832821 : Nat := 1312052957097635869273789

theorem tailTrace_3832821 : CollatzResearch.WordTrace tailWord_3832821 prefixEnd_3832821 1312052957097635869273789 := by
  unfold tailWord_3832821
  simp only [CollatzResearch.WordTrace]
  refine ⟨139794466447351585557042317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93196310964901057038028211 139794466447351585557042317)
  ·
    refine ⟨52422924917756844583890869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139794466447351585557042317 52422924917756844583890869)
    ·
      refine ⟨4914649211039704179739769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52422924917756844583890869 4914649211039704179739769)
      ·
        refine ⟨3685986908279778134804827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4914649211039704179739769 3685986908279778134804827)
        ·
          refine ⟨5528980362419667202207241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685986908279778134804827 5528980362419667202207241)
          ·
            refine ⟨4146735271814750401655431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5528980362419667202207241 4146735271814750401655431)
            ·
              refine ⟨6220102907722125602483147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146735271814750401655431 6220102907722125602483147)
              ·
                refine ⟨9330154361583188403724721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220102907722125602483147 9330154361583188403724721)
                ·
                  refine ⟨6997615771187391302793541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9330154361583188403724721 6997615771187391302793541)
                  ·
                    refine ⟨1312052957097635869273789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997615771187391302793541 1312052957097635869273789)
                    ·
                      rfl

theorem cell22_3832821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3832821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832821 prefixEnd_3832821 := by exact prefixLift 3832821
  have htrace : WordTrace (prefixWord ++ tailWord_3832821) baseStart_3832821 baseEnd_3832821 := by
    simpa [prefixWord, tailWord_3832821, baseEnd_3832821] using wordTrace_append hprefix tailTrace_3832821
  have hstable : (prefixWord ++ tailWord_3832821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832821).length < 2 ^ (prefixWord ++ tailWord_3832821).sum := by decide
  have hdescent : baseEnd_3832821 < baseStart_3832821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832890 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_3832890 : Nat := 118140960795 + 3832890 * 2 ^ 59
def prefixEnd_3832890 : Nat := 4983230072969 + 3 ^ 40 * 3832890 * 2
def baseEnd_3832890 : Nat := 1312076577207742689298577

theorem tailTrace_3832890 : CollatzResearch.WordTrace tailWord_3832890 prefixEnd_3832890 1312076577207742689298577 := by
  unfold tailWord_3832890
  simp only [CollatzResearch.WordTrace]
  refine ⟨34949245771025402585326031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93197988722734406894202749 34949245771025402585326031)
  ·
    refine ⟨52423868656538103877989047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34949245771025402585326031 52423868656538103877989047)
    ·
      refine ⟨78635802984807155816983571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52423868656538103877989047 78635802984807155816983571)
      ·
        refine ⟨117953704477210733725475357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78635802984807155816983571 117953704477210733725475357)
        ·
          refine ⟨44232639178954025147053259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117953704477210733725475357 44232639178954025147053259)
          ·
            refine ⟨66348958768431037720579889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44232639178954025147053259 66348958768431037720579889)
            ·
              refine ⟨49761719076323278290434917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66348958768431037720579889 49761719076323278290434917)
              ·
                refine ⟨9330322326810614679456547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49761719076323278290434917 9330322326810614679456547)
                ·
                  refine ⟨13995483490215922019184821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9330322326810614679456547 13995483490215922019184821)
                  ·
                    refine ⟨1312076577207742689298577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13995483490215922019184821 1312076577207742689298577)
                    ·
                      rfl

theorem cell22_3832890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_3832890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832890 prefixEnd_3832890 := by exact prefixLift 3832890
  have htrace : WordTrace (prefixWord ++ tailWord_3832890) baseStart_3832890 baseEnd_3832890 := by
    simpa [prefixWord, tailWord_3832890, baseEnd_3832890] using wordTrace_append hprefix tailTrace_3832890
  have hstable : (prefixWord ++ tailWord_3832890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832890).length < 2 ^ (prefixWord ++ tailWord_3832890).sum := by decide
  have hdescent : baseEnd_3832890 < baseStart_3832890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832894 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3832894 : Nat := 118140960795 + 3832894 * 2 ^ 59
def prefixEnd_3832894 : Nat := 4983230072969 + 3 ^ 40 * 3832894 * 2
def baseEnd_3832894 : Nat := 1312077946489488012198565

theorem tailTrace_3832894 : CollatzResearch.WordTrace tailWord_3832894 prefixEnd_3832894 1312077946489488012198565 := by
  unfold tailWord_3832894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474641122010889878056217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93198085984058079349633157 17474641122010889878056217)
  ·
    refine ⟨13105980841508167408542163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17474641122010889878056217 13105980841508167408542163)
    ·
      refine ⟨19658971262262251112813245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13105980841508167408542163 19658971262262251112813245)
      ·
        refine ⟨7372114223348344167304967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19658971262262251112813245 7372114223348344167304967)
        ·
          refine ⟨11058171335022516250957451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372114223348344167304967 11058171335022516250957451)
          ·
            refine ⟨16587257002533774376436177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058171335022516250957451 16587257002533774376436177)
            ·
              refine ⟨12440442751900330782327133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16587257002533774376436177 12440442751900330782327133)
              ·
                refine ⟨4665166031962624043372675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12440442751900330782327133 4665166031962624043372675)
                ·
                  refine ⟨6997749047943936065059013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665166031962624043372675 6997749047943936065059013)
                  ·
                    refine ⟨1312077946489488012198565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6997749047943936065059013 1312077946489488012198565)
                    ·
                      rfl

theorem cell22_3832894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3832894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832894 prefixEnd_3832894 := by exact prefixLift 3832894
  have htrace : WordTrace (prefixWord ++ tailWord_3832894) baseStart_3832894 baseEnd_3832894 := by
    simpa [prefixWord, tailWord_3832894, baseEnd_3832894] using wordTrace_append hprefix tailTrace_3832894
  have hstable : (prefixWord ++ tailWord_3832894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832894).length < 2 ^ (prefixWord ++ tailWord_3832894).sum := by decide
  have hdescent : baseEnd_3832894 < baseStart_3832894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832909 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3832909 : Nat := 118140960795 + 3832909 * 2 ^ 59
def prefixEnd_3832909 : Nat := 4983230072969 + 3 ^ 40 * 3832909 * 2
def baseEnd_3832909 : Nat := 437361027098677657691173

theorem tailTrace_3832909 : CollatzResearch.WordTrace tailWord_3832909 prefixEnd_3832909 437361027098677657691173 := by
  unfold tailWord_3832909
  simp only [CollatzResearch.WordTrace]
  refine ⟨139797676071032776586245781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93198450714021851057497187 139797676071032776586245781)
  ·
    refine ⟨6553016065829661402480271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139797676071032776586245781 6553016065829661402480271)
    ·
      refine ⟨9829524098744492103720407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6553016065829661402480271 9829524098744492103720407)
      ·
        refine ⟨14744286148116738155580611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829524098744492103720407 14744286148116738155580611)
        ·
          refine ⟨22116429222175107233370917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744286148116738155580611 22116429222175107233370917)
          ·
            refine ⟨4146830479157832606257047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22116429222175107233370917 4146830479157832606257047)
            ·
              refine ⟨6220245718736748909385571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146830479157832606257047 6220245718736748909385571)
              ·
                refine ⟨9330368578105123364078357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220245718736748909385571 9330368578105123364078357)
                ·
                  refine ⟨437361027098677657691173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9330368578105123364078357 437361027098677657691173)
                  ·
                    rfl

theorem cell22_3832909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3832909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832909 prefixEnd_3832909 := by exact prefixLift 3832909
  have htrace : WordTrace (prefixWord ++ tailWord_3832909) baseStart_3832909 baseEnd_3832909 := by
    simpa [prefixWord, tailWord_3832909, baseEnd_3832909] using wordTrace_append hprefix tailTrace_3832909
  have hstable : (prefixWord ++ tailWord_3832909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832909).length < 2 ^ (prefixWord ++ tailWord_3832909).sum := by decide
  have hdescent : baseEnd_3832909 < baseStart_3832909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832920 : List Nat := [2, 1, 2, 2, 1, 3, 4, 7]
def baseStart_3832920 : Nat := 118140960795 + 3832920 * 2 ^ 59
def prefixEnd_3832920 : Nat := 4983230072969 + 3 ^ 40 * 3832920 * 2
def baseEnd_3832920 : Nat := 145787427424536956783165

theorem tailTrace_3832920 : CollatzResearch.WordTrace tailWord_3832920 prefixEnd_3832920 145787427424536956783165 := by
  unfold tailWord_3832920
  simp only [CollatzResearch.WordTrace]
  refine ⟨69899038636996462732448107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93198718182661950309930809 69899038636996462732448107)
  ·
    refine ⟨104848557955494694098672161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69899038636996462732448107 104848557955494694098672161)
    ·
      refine ⟨78636418466621020574004121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104848557955494694098672161 78636418466621020574004121)
      ·
        refine ⟨58977313849965765430503091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78636418466621020574004121 58977313849965765430503091)
        ·
          refine ⟨88465970774948648145754637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58977313849965765430503091 88465970774948648145754637)
          ·
            refine ⟨33174739040605743054657989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88465970774948648145754637 33174739040605743054657989)
            ·
              refine ⟨6220263570113576822748373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33174739040605743054657989 6220263570113576822748373)
              ·
                refine ⟨145787427424536956783165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6220263570113576822748373 145787427424536956783165)
                ·
                  rfl

theorem cell22_3832920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 7].length) (baseStart_3832920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832920 prefixEnd_3832920 := by exact prefixLift 3832920
  have htrace : WordTrace (prefixWord ++ tailWord_3832920) baseStart_3832920 baseEnd_3832920 := by
    simpa [prefixWord, tailWord_3832920, baseEnd_3832920] using wordTrace_append hprefix tailTrace_3832920
  have hstable : (prefixWord ++ tailWord_3832920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832920).length < 2 ^ (prefixWord ++ tailWord_3832920).sum := by decide
  have hdescent : baseEnd_3832920 < baseStart_3832920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3832924 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3832924 : Nat := 118140960795 + 3832924 * 2 ^ 59
def prefixEnd_3832924 : Nat := 4983230072969 + 3 ^ 40 * 3832924 * 2
def baseEnd_3832924 : Nat := 1312088216102577933948473

theorem tailTrace_3832924 : CollatzResearch.WordTrace tailWord_3832924 prefixEnd_3832924 1312088216102577933948473 := by
  unfold tailWord_3832924
  simp only [CollatzResearch.WordTrace]
  refine ⟨69899111582989217074020913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93198815443985622765361217 69899111582989217074020913)
  ·
    refine ⟨52424333687241912805515685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69899111582989217074020913 52424333687241912805515685)
    ·
      refine ⟨9829562566357858651034191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52424333687241912805515685 9829562566357858651034191)
      ·
        refine ⟨14744343849536787976551287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829562566357858651034191 14744343849536787976551287)
        ·
          refine ⟨22116515774305181964826931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744343849536787976551287 22116515774305181964826931)
          ·
            refine ⟨33174773661457772947240397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22116515774305181964826931 33174773661457772947240397)
            ·
              refine ⟨12440540123046664855215149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33174773661457772947240397 12440540123046664855215149)
              ·
                refine ⟨4665202546142499320705681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12440540123046664855215149 4665202546142499320705681)
                ·
                  refine ⟨3498901909606874490529261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4665202546142499320705681 3498901909606874490529261)
                  ·
                    refine ⟨1312088216102577933948473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498901909606874490529261 1312088216102577933948473)
                    ·
                      rfl

theorem cell22_3832924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3832924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3832924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3832924 prefixEnd_3832924 := by exact prefixLift 3832924
  have htrace : WordTrace (prefixWord ++ tailWord_3832924) baseStart_3832924 baseEnd_3832924 := by
    simpa [prefixWord, tailWord_3832924, baseEnd_3832924] using wordTrace_append hprefix tailTrace_3832924
  have hstable : (prefixWord ++ tailWord_3832924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3832924).length < 2 ^ (prefixWord ++ tailWord_3832924).sum := by decide
  have hdescent : baseEnd_3832924 < baseStart_3832924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3832924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833057 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_3833057 : Nat := 118140960795 + 3833057 * 2 ^ 59
def prefixEnd_3833057 : Nat := 4983230072969 + 3 ^ 40 * 3833057 * 2
def baseEnd_3833057 : Nat := 1312133744720609920373065

theorem tailTrace_3833057 : CollatzResearch.WordTrace tailWord_3833057 prefixEnd_3833057 1312133744720609920373065 := by
  unfold tailWord_3833057
  simp only [CollatzResearch.WordTrace]
  refine ⟨139803074074496597862633425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93202049382997731908422283 139803074074496597862633425)
  ·
    refine ⟨104852305555872448396975069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139803074074496597862633425 104852305555872448396975069)
    ·
      refine ⟨39319614583452168148865651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104852305555872448396975069 39319614583452168148865651)
      ·
        refine ⟨58979421875178252223298477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39319614583452168148865651 58979421875178252223298477)
        ·
          refine ⟨22117283203191844583736929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58979421875178252223298477 22117283203191844583736929)
          ·
            refine ⟨16587962402393883437802697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22117283203191844583736929 16587962402393883437802697)
            ·
              refine ⟨12440971801795412578352023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16587962402393883437802697 12440971801795412578352023)
              ·
                refine ⟨18661457702693118867528035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12440971801795412578352023 18661457702693118867528035)
                ·
                  refine ⟨27992186554039678301292053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18661457702693118867528035 27992186554039678301292053)
                  ·
                    refine ⟨1312133744720609920373065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27992186554039678301292053 1312133744720609920373065)
                    ·
                      rfl

theorem cell22_3833057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_3833057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833057 prefixEnd_3833057 := by exact prefixLift 3833057
  have htrace : WordTrace (prefixWord ++ tailWord_3833057) baseStart_3833057 baseEnd_3833057 := by
    simpa [prefixWord, tailWord_3833057, baseEnd_3833057] using wordTrace_append hprefix tailTrace_3833057
  have hstable : (prefixWord ++ tailWord_3833057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833057).length < 2 ^ (prefixWord ++ tailWord_3833057).sum := by decide
  have hdescent : baseEnd_3833057 < baseStart_3833057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833121 : List Nat := [1, 2, 3, 2, 1, 1, 1, 7, 1, 3]
def baseStart_3833121 : Nat := 118140960795 + 3833121 * 2 ^ 59
def prefixEnd_3833121 : Nat := 4983230072969 + 3 ^ 40 * 3833121 * 2
def baseEnd_3833121 : Nat := 1312155653228535086772869

theorem tailTrace_3833121 : CollatzResearch.WordTrace tailWord_3833121 prefixEnd_3833121 1312155653228535086772869 := by
  unfold tailWord_3833121
  simp only [CollatzResearch.WordTrace]
  refine ⟨139805408346264736792963217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93203605564176491195308811 139805408346264736792963217)
  ·
    refine ⟨104854056259698552594722413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139805408346264736792963217 104854056259698552594722413)
    ·
      refine ⟨39320271097386957223020905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104854056259698552594722413 39320271097386957223020905)
      ·
        refine ⟨29490203323040217917265679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39320271097386957223020905 29490203323040217917265679)
        ·
          refine ⟨44235304984560326875898519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29490203323040217917265679 44235304984560326875898519)
          ·
            refine ⟨66352957476840490313847779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44235304984560326875898519 66352957476840490313847779)
            ·
              refine ⟨99529436215260735470771669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66352957476840490313847779 99529436215260735470771669)
              ·
                refine ⟨2332721161295173487596211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 99529436215260735470771669 2332721161295173487596211)
                ·
                  refine ⟨3499081741942760231394317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332721161295173487596211 3499081741942760231394317)
                  ·
                    refine ⟨1312155653228535086772869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499081741942760231394317 1312155653228535086772869)
                    ·
                      rfl

theorem cell22_3833121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_3833121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833121 prefixEnd_3833121 := by exact prefixLift 3833121
  have htrace : WordTrace (prefixWord ++ tailWord_3833121) baseStart_3833121 baseEnd_3833121 := by
    simpa [prefixWord, tailWord_3833121, baseEnd_3833121] using wordTrace_append hprefix tailTrace_3833121
  have hstable : (prefixWord ++ tailWord_3833121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833121).length < 2 ^ (prefixWord ++ tailWord_3833121).sum := by decide
  have hdescent : baseEnd_3833121 < baseStart_3833121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833132 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_3833132 : Nat := 118140960795 + 3833132 * 2 ^ 59
def prefixEnd_3833132 : Nat := 4983230072969 + 3 ^ 40 * 3833132 * 2
def baseEnd_3833132 : Nat := 1312159418753334724747835

theorem tailTrace_3833132 : CollatzResearch.WordTrace tailWord_3833132 prefixEnd_3833132 1312159418753334724747835 := by
  unfold tailWord_3833132
  simp only [CollatzResearch.WordTrace]
  refine ⟨69902904774612442835806825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93203873032816590447742433 69902904774612442835806825)
  ·
    refine ⟨52427178580959332126855119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69902904774612442835806825 52427178580959332126855119)
    ·
      refine ⟨78640767871438998190282679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52427178580959332126855119 78640767871438998190282679)
      ·
        refine ⟨117961151807158497285424019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78640767871438998190282679 117961151807158497285424019)
        ·
          refine ⟨176941727710737745928136029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117961151807158497285424019 176941727710737745928136029)
          ·
            refine ⟨66353147891526654723051011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176941727710737745928136029 66353147891526654723051011)
            ·
              refine ⟨99529721837289982084576517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66353147891526654723051011 99529721837289982084576517)
              ·
                refine ⟨18661822844491871640858097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99529721837289982084576517 18661822844491871640858097)
                ·
                  refine ⟨13996367133368903730643573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18661822844491871640858097 13996367133368903730643573)
                  ·
                    refine ⟨1312159418753334724747835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13996367133368903730643573 1312159418753334724747835)
                    ·
                      rfl

theorem cell22_3833132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_3833132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833132 prefixEnd_3833132 := by exact prefixLift 3833132
  have htrace : WordTrace (prefixWord ++ tailWord_3833132) baseStart_3833132 baseEnd_3833132 := by
    simpa [prefixWord, tailWord_3833132, baseEnd_3833132] using wordTrace_append hprefix tailTrace_3833132
  have hstable : (prefixWord ++ tailWord_3833132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833132).length < 2 ^ (prefixWord ++ tailWord_3833132).sum := by decide
  have hdescent : baseEnd_3833132 < baseStart_3833132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833138 : List Nat := [3, 2, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_3833138 : Nat := 118140960795 + 3833138 * 2 ^ 59
def prefixEnd_3833138 : Nat := 4983230072969 + 3 ^ 40 * 3833138 * 2
def baseEnd_3833138 : Nat := 1312161472675952709097817

theorem tailTrace_3833138 : CollatzResearch.WordTrace tailWord_3833138 prefixEnd_3833138 1312161472675952709097817 := by
  unfold tailWord_3833138
  simp only [CollatzResearch.WordTrace]
  refine ⟨34951507096800787174083017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93204018924802099130888045 34951507096800787174083017)
  ·
    refine ⟨26213630322600590380562263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34951507096800787174083017 26213630322600590380562263)
    ·
      refine ⟨39320445483900885570843395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26213630322600590380562263 39320445483900885570843395)
      ·
        refine ⟨58980668225851328356265093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39320445483900885570843395 58980668225851328356265093)
        ·
          refine ⟨11058875292347124066799705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58980668225851328356265093 11058875292347124066799705)
          ·
            refine ⟨8294156469260343050099779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11058875292347124066799705 8294156469260343050099779)
            ·
              refine ⟨12441234703890514575149669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8294156469260343050099779 12441234703890514575149669)
              ·
                refine ⟨2332731506979471482840563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12441234703890514575149669 2332731506979471482840563)
                ·
                  refine ⟨3499097260469207224260845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332731506979471482840563 3499097260469207224260845)
                  ·
                    refine ⟨1312161472675952709097817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499097260469207224260845 1312161472675952709097817)
                    ·
                      rfl

theorem cell22_3833138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_3833138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833138 prefixEnd_3833138 := by exact prefixLift 3833138
  have htrace : WordTrace (prefixWord ++ tailWord_3833138) baseStart_3833138 baseEnd_3833138 := by
    simpa [prefixWord, tailWord_3833138, baseEnd_3833138] using wordTrace_append hprefix tailTrace_3833138
  have hstable : (prefixWord ++ tailWord_3833138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833138).length < 2 ^ (prefixWord ++ tailWord_3833138).sum := by decide
  have hdescent : baseEnd_3833138 < baseStart_3833138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833164 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_3833164 : Nat := 118140960795 + 3833164 * 2 ^ 59
def prefixEnd_3833164 : Nat := 4983230072969 + 3 ^ 40 * 3833164 * 2
def baseEnd_3833164 : Nat := 1312170373007297307947737

theorem tailTrace_3833164 : CollatzResearch.WordTrace tailWord_3833164 prefixEnd_3833164 1312170373007297307947737 := by
  unfold tailWord_3833164
  simp only [CollatzResearch.WordTrace]
  refine ⟨69903488342554477568389273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93204651123405970091185697 69903488342554477568389273)
  ·
    refine ⟨52427616256915858176291955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69903488342554477568389273 52427616256915858176291955)
    ·
      refine ⟨78641424385373787264437933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52427616256915858176291955 78641424385373787264437933)
      ·
        refine ⟨29490534144515170224164225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78641424385373787264437933 29490534144515170224164225)
        ·
          refine ⟨22117900608386377668123169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29490534144515170224164225 22117900608386377668123169)
          ·
            refine ⟨16588425456289783251092377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22117900608386377668123169 16588425456289783251092377)
            ·
              refine ⟨12441319092217337438319283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16588425456289783251092377 12441319092217337438319283)
              ·
                refine ⟨18661978638326006157478925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12441319092217337438319283 18661978638326006157478925)
                ·
                  refine ⟨6998241989372252309054597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18661978638326006157478925 6998241989372252309054597)
                  ·
                    refine ⟨1312170373007297307947737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6998241989372252309054597 1312170373007297307947737)
                    ·
                      rfl

theorem cell22_3833164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_3833164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833164 prefixEnd_3833164 := by exact prefixLift 3833164
  have htrace : WordTrace (prefixWord ++ tailWord_3833164) baseStart_3833164 baseEnd_3833164 := by
    simpa [prefixWord, tailWord_3833164, baseEnd_3833164] using wordTrace_append hprefix tailTrace_3833164
  have hstable : (prefixWord ++ tailWord_3833164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833164).length < 2 ^ (prefixWord ++ tailWord_3833164).sum := by decide
  have hdescent : baseEnd_3833164 < baseStart_3833164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833196 : List Nat := [2, 2, 1, 1, 5, 1, 2, 4, 4]
def baseStart_3833196 : Nat := 118140960795 + 3833196 * 2 ^ 59
def prefixEnd_3833196 : Nat := 4983230072969 + 3 ^ 40 * 3833196 * 2
def baseEnd_3833196 : Nat := 437393775753753297049213

theorem tailTrace_3833196 : CollatzResearch.WordTrace tailWord_3833196 prefixEnd_3833196 437393775753753297049213 := by
  unfold tailWord_3833196
  simp only [CollatzResearch.WordTrace]
  refine ⟨69904071910496512300971721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93205429213995349734628961 69904071910496512300971721)
  ·
    refine ⟨52428053932872384225728791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69904071910496512300971721 52428053932872384225728791)
    ·
      refine ⟨78642080899308576338593187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52428053932872384225728791 78642080899308576338593187)
      ·
        refine ⟨117963121348962864507889781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78642080899308576338593187 117963121348962864507889781)
        ·
          refine ⟨11059042626465268547614667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117963121348962864507889781 11059042626465268547614667)
          ·
            refine ⟨16588563939697902821422001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11059042626465268547614667 16588563939697902821422001)
            ·
              refine ⟨12441422954773427116066501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16588563939697902821422001 12441422954773427116066501)
              ·
                refine ⟨2332766804020017584262469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12441422954773427116066501 2332766804020017584262469)
                ·
                  refine ⟨437393775753753297049213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2332766804020017584262469 437393775753753297049213)
                  ·
                    rfl

theorem cell22_3833196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_3833196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833196 prefixEnd_3833196 := by exact prefixLift 3833196
  have htrace : WordTrace (prefixWord ++ tailWord_3833196) baseStart_3833196 baseEnd_3833196 := by
    simpa [prefixWord, tailWord_3833196, baseEnd_3833196] using wordTrace_append hprefix tailTrace_3833196
  have hstable : (prefixWord ++ tailWord_3833196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833196).length < 2 ^ (prefixWord ++ tailWord_3833196).sum := by decide
  have hdescent : baseEnd_3833196 < baseStart_3833196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833207 : List Nat := [1, 1, 3, 1, 1, 2, 4, 9]
def baseStart_3833207 : Nat := 118140960795 + 3833207 * 2 ^ 59
def prefixEnd_3833207 : Nat := 4983230072969 + 3 ^ 40 * 3833207 * 2
def baseEnd_3833207 : Nat := 145798343642895503235845

theorem tailTrace_3833207 : CollatzResearch.WordTrace tailWord_3833207 prefixEnd_3833207 145798343642895503235845 := by
  unfold tailWord_3833207
  simp only [CollatzResearch.WordTrace]
  refine ⟨139808545023953173480593875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93205696682635448987062583 139808545023953173480593875)
  ·
    refine ⟨209712817535929760220890813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139808545023953173480593875 209712817535929760220890813)
    ·
      refine ⟨78642306575973660082834055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209712817535929760220890813 78642306575973660082834055)
      ·
        refine ⟨117963459863960490124251083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78642306575973660082834055 117963459863960490124251083)
        ·
          refine ⟨176945189795940735186376625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117963459863960490124251083 176945189795940735186376625)
          ·
            refine ⟨132708892346955551389782469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176945189795940735186376625 132708892346955551389782469)
            ·
              refine ⟨24882917315054165885584213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132708892346955551389782469 24882917315054165885584213)
              ·
                refine ⟨145798343642895503235845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24882917315054165885584213 145798343642895503235845)
                ·
                  rfl

theorem cell22_3833207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 9].length) (baseStart_3833207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833207 prefixEnd_3833207 := by exact prefixLift 3833207
  have htrace : WordTrace (prefixWord ++ tailWord_3833207) baseStart_3833207 baseEnd_3833207 := by
    simpa [prefixWord, tailWord_3833207, baseEnd_3833207] using wordTrace_append hprefix tailTrace_3833207
  have hstable : (prefixWord ++ tailWord_3833207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833207).length < 2 ^ (prefixWord ++ tailWord_3833207).sum := by decide
  have hdescent : baseEnd_3833207 < baseStart_3833207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833224 : List Nat := [2, 1, 3, 3, 1, 3, 1, 8]
def baseStart_3833224 : Nat := 118140960795 + 3833224 * 2 ^ 59
def prefixEnd_3833224 : Nat := 4983230072969 + 3 ^ 40 * 3833224 * 2
def baseEnd_3833224 : Nat := 145798990248164127938617

theorem tailTrace_3833224 : CollatzResearch.WordTrace tailWord_3833224 prefixEnd_3833224 145798990248164127938617 := by
  unfold tailWord_3833224
  simp only [CollatzResearch.WordTrace]
  refine ⟨69904582532445792691981363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93206110043261056922641817 69904582532445792691981363)
  ·
    refine ⟨104856873798668689037972045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69904582532445792691981363 104856873798668689037972045)
    ·
      refine ⟨39321327674500758389239517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104856873798668689037972045 39321327674500758389239517)
      ·
        refine ⟨14745497877937784395964819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39321327674500758389239517 14745497877937784395964819)
        ·
          refine ⟨22118246816906676593947229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14745497877937784395964819 22118246816906676593947229)
          ·
            refine ⟨8294342556340003722730211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22118246816906676593947229 8294342556340003722730211)
            ·
              refine ⟨12441513834510005584095317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8294342556340003722730211 12441513834510005584095317)
              ·
                refine ⟨145798990248164127938617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12441513834510005584095317 145798990248164127938617)
                ·
                  rfl

theorem cell22_3833224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 8].length) (baseStart_3833224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833224 prefixEnd_3833224 := by exact prefixLift 3833224
  have htrace : WordTrace (prefixWord ++ tailWord_3833224) baseStart_3833224 baseEnd_3833224 := by
    simpa [prefixWord, tailWord_3833224, baseEnd_3833224] using wordTrace_append hprefix tailTrace_3833224
  have hstable : (prefixWord ++ tailWord_3833224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833224).length < 2 ^ (prefixWord ++ tailWord_3833224).sum := by decide
  have hdescent : baseEnd_3833224 < baseStart_3833224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833230 : List Nat := [4, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3833230 : Nat := 118140960795 + 3833230 * 2 ^ 59
def prefixEnd_3833230 : Nat := 4983230072969 + 3 ^ 40 * 3833230 * 2
def baseEnd_3833230 : Nat := 437397655385365045265845

theorem tailTrace_3833230 : CollatzResearch.WordTrace tailWord_3833230 prefixEnd_3833230 437397655385365045265845 := by
  unfold tailWord_3833230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17476172987858731051085143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93206255935246565605787429 17476172987858731051085143)
  ·
    refine ⟨26214259481788096576627715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17476172987858731051085143 26214259481788096576627715)
    ·
      refine ⟨39321389222682144864941573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26214259481788096576627715 39321389222682144864941573)
      ·
        refine ⟨7372760479252902162176545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39321389222682144864941573 7372760479252902162176545)
        ·
          refine ⟨5529570359439676621632409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7372760479252902162176545 5529570359439676621632409)
          ·
            refine ⟨4147177769579757466224307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5529570359439676621632409 4147177769579757466224307)
            ·
              refine ⟨6220766654369636199336461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147177769579757466224307 6220766654369636199336461)
              ·
                refine ⟨2332787495388613574751173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6220766654369636199336461 2332787495388613574751173)
                ·
                  refine ⟨437397655385365045265845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2332787495388613574751173 437397655385365045265845)
                  ·
                    rfl

theorem cell22_3833230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3833230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833230 prefixEnd_3833230 := by exact prefixLift 3833230
  have htrace : WordTrace (prefixWord ++ tailWord_3833230) baseStart_3833230 baseEnd_3833230 := by
    simpa [prefixWord, tailWord_3833230, baseEnd_3833230] using wordTrace_append hprefix tailTrace_3833230
  have hstable : (prefixWord ++ tailWord_3833230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833230).length < 2 ^ (prefixWord ++ tailWord_3833230).sum := by decide
  have hdescent : baseEnd_3833230 < baseStart_3833230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833333 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3833333 : Nat := 118140960795 + 3833333 * 2 ^ 59
def prefixEnd_3833333 : Nat := 4983230072969 + 3 ^ 40 * 3833333 * 2
def baseEnd_3833333 : Nat := 1312228225161037200472219

theorem tailTrace_3833333 : CollatzResearch.WordTrace tailWord_3833333 prefixEnd_3833333 1312228225161037200472219 := by
  unfold tailWord_3833333
  simp only [CollatzResearch.WordTrace]
  refine ⟨139813140621496696999680653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93208760414331131333120435 139813140621496696999680653)
  ·
    refine ⟨52429927733061261374880245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139813140621496696999680653 52429927733061261374880245)
    ·
      refine ⟨4915305724974493253895023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52429927733061261374880245 4915305724974493253895023)
      ·
        refine ⟨7372958587461739880842535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4915305724974493253895023 7372958587461739880842535)
        ·
          refine ⟨11059437881192609821263803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372958587461739880842535 11059437881192609821263803)
          ·
            refine ⟨16589156821788914731895705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11059437881192609821263803 16589156821788914731895705)
            ·
              refine ⟨12441867616341686048921779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16589156821788914731895705 12441867616341686048921779)
              ·
                refine ⟨18662801424512529073382669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12441867616341686048921779 18662801424512529073382669)
                ·
                  refine ⟨6998550534192198402518501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18662801424512529073382669 6998550534192198402518501)
                  ·
                    refine ⟨1312228225161037200472219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6998550534192198402518501 1312228225161037200472219)
                    ·
                      rfl

theorem cell22_3833333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3833333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833333 prefixEnd_3833333 := by exact prefixLift 3833333
  have htrace : WordTrace (prefixWord ++ tailWord_3833333) baseStart_3833333 baseEnd_3833333 := by
    simpa [prefixWord, tailWord_3833333, baseEnd_3833333] using wordTrace_append hprefix tailTrace_3833333
  have hstable : (prefixWord ++ tailWord_3833333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833333).length < 2 ^ (prefixWord ++ tailWord_3833333).sum := by decide
  have hdescent : baseEnd_3833333 < baseStart_3833333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833363 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 2, 3]
def baseStart_3833363 : Nat := 118140960795 + 3833363 * 2 ^ 59
def prefixEnd_3833363 : Nat := 4983230072969 + 3 ^ 40 * 3833363 * 2
def baseEnd_3833363 : Nat := 1312238494774127122222127

theorem tailTrace_3833363 : CollatzResearch.WordTrace tailWord_3833363 prefixEnd_3833363 1312238494774127122222127 := by
  unfold tailWord_3833363
  simp only [CollatzResearch.WordTrace]
  refine ⟨139814234811388012123272743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93209489874258674748848495 139814234811388012123272743)
  ·
    refine ⟨209721352217082018184909115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139814234811388012123272743 209721352217082018184909115)
    ·
      refine ⟨314582028325623027277363673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209721352217082018184909115 314582028325623027277363673)
      ·
        refine ⟨235936521244217270458022755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314582028325623027277363673 235936521244217270458022755)
        ·
          refine ⟨353904781866325905687034133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235936521244217270458022755 353904781866325905687034133)
          ·
            refine ⟨16589286649984026829079725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 353904781866325905687034133 16589286649984026829079725)
            ·
              refine ⟨6220982493744010060904897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16589286649984026829079725 6220982493744010060904897)
              ·
                refine ⟨4665736870308007545678673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6220982493744010060904897 4665736870308007545678673)
                ·
                  refine ⟨3499302652731005659259005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4665736870308007545678673 3499302652731005659259005)
                  ·
                    refine ⟨1312238494774127122222127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499302652731005659259005 1312238494774127122222127)
                    ·
                      rfl

theorem cell22_3833363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 3].length) (baseStart_3833363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833363 prefixEnd_3833363 := by exact prefixLift 3833363
  have htrace : WordTrace (prefixWord ++ tailWord_3833363) baseStart_3833363 baseEnd_3833363 := by
    simpa [prefixWord, tailWord_3833363, baseEnd_3833363] using wordTrace_append hprefix tailTrace_3833363
  have hstable : (prefixWord ++ tailWord_3833363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833363).length < 2 ^ (prefixWord ++ tailWord_3833363).sum := by decide
  have hdescent : baseEnd_3833363 < baseStart_3833363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833476 : List Nat := [2, 3, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_3833476 : Nat := 118140960795 + 3833476 * 2 ^ 59
def prefixEnd_3833476 : Nat := 4983230072969 + 3 ^ 40 * 3833476 * 2
def baseEnd_3833476 : Nat := 1312277176983432494146781

theorem tailTrace_3833476 : CollatzResearch.WordTrace tailWord_3833476 prefixEnd_3833476 1312277176983432494146781 := by
  unfold tailWord_3833476
  simp only [CollatzResearch.WordTrace]
  refine ⟨69909178129989316211068141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93212237506652421614757521 69909178129989316211068141)
  ·
    refine ⟨26215941798745993579150553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69909178129989316211068141 26215941798745993579150553)
    ·
      refine ⟨19661956349059495184362915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26215941798745993579150553 19661956349059495184362915)
      ·
        refine ⟨29492934523589242776544373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19661956349059495184362915 29492934523589242776544373)
        ·
          refine ⟨2764962611586491510301035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29492934523589242776544373 2764962611586491510301035)
          ·
            refine ⟨4147443917379737265451553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764962611586491510301035 4147443917379737265451553)
            ·
              refine ⟨3110582938034802949088665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4147443917379737265451553 3110582938034802949088665)
              ·
                refine ⟨2332937203526102211816499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3110582938034802949088665 2332937203526102211816499)
                ·
                  refine ⟨3499405805289153317724749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332937203526102211816499 3499405805289153317724749)
                  ·
                    refine ⟨1312277176983432494146781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499405805289153317724749 1312277176983432494146781)
                    ·
                      rfl

theorem cell22_3833476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_3833476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833476 prefixEnd_3833476 := by exact prefixLift 3833476
  have htrace : WordTrace (prefixWord ++ tailWord_3833476) baseStart_3833476 baseEnd_3833476 := by
    simpa [prefixWord, tailWord_3833476, baseEnd_3833476] using wordTrace_append hprefix tailTrace_3833476
  have hstable : (prefixWord ++ tailWord_3833476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833476).length < 2 ^ (prefixWord ++ tailWord_3833476).sum := by decide
  have hdescent : baseEnd_3833476 < baseStart_3833476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833483 : List Nat := [1, 1, 1, 1, 4, 1, 5, 4, 4]
def baseStart_3833483 : Nat := 118140960795 + 3833483 * 2 ^ 59
def prefixEnd_3833483 : Nat := 4983230072969 + 3 ^ 40 * 3833483 * 2
def baseEnd_3833483 : Nat := 437426524408828936407253

theorem tailTrace_3833483 : CollatzResearch.WordTrace tailWord_3833483 prefixEnd_3833483 437426524408828936407253 := by
  unfold tailWord_3833483
  simp only [CollatzResearch.WordTrace]
  refine ⟨139818611570953272617641103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93212407713968848411760735 139818611570953272617641103)
  ·
    refine ⟨209727917356429908926461655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139818611570953272617641103 209727917356429908926461655)
    ·
      refine ⟨314591876034644863389692483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209727917356429908926461655 314591876034644863389692483)
      ·
        refine ⟨471887814051967295084538725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314591876034644863389692483 471887814051967295084538725)
        ·
          refine ⟨88478965134743867828351011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471887814051967295084538725 88478965134743867828351011)
          ·
            refine ⟨132718447702115801742526517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88478965134743867828351011 132718447702115801742526517)
            ·
              refine ⟨12442354472073356413361861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132718447702115801742526517 12442354472073356413361861)
              ·
                refine ⟨2332941463513754327505349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12442354472073356413361861 2332941463513754327505349)
                ·
                  refine ⟨437426524408828936407253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2332941463513754327505349 437426524408828936407253)
                  ·
                    rfl

theorem cell22_3833483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 4].length) (baseStart_3833483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833483 prefixEnd_3833483 := by exact prefixLift 3833483
  have htrace : WordTrace (prefixWord ++ tailWord_3833483) baseStart_3833483 baseEnd_3833483 := by
    simpa [prefixWord, tailWord_3833483, baseEnd_3833483] using wordTrace_append hprefix tailTrace_3833483
  have hstable : (prefixWord ++ tailWord_3833483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833483).length < 2 ^ (prefixWord ++ tailWord_3833483).sum := by decide
  have hdescent : baseEnd_3833483 < baseStart_3833483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833532 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_3833532 : Nat := 118140960795 + 3833532 * 2 ^ 59
def prefixEnd_3833532 : Nat := 4983230072969 + 3 ^ 40 * 3833532 * 2
def baseEnd_3833532 : Nat := 1312296346927867014746609

theorem tailTrace_3833532 : CollatzResearch.WordTrace tailWord_3833532 prefixEnd_3833532 1312296346927867014746609 := by
  unfold tailWord_3833532
  simp only [CollatzResearch.WordTrace]
  refine ⟨69910199373887876993087425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93213599165183835990783233 69910199373887876993087425)
  ·
    refine ⟨52432649530415907744815569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69910199373887876993087425 52432649530415907744815569)
    ·
      refine ⟨39324487147811930808611677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52432649530415907744815569 39324487147811930808611677)
      ·
        refine ⟨14746682680429474053229379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39324487147811930808611677 14746682680429474053229379)
        ·
          refine ⟨22120024020644211079844069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14746682680429474053229379 22120024020644211079844069)
          ·
            refine ⟨4147504503870789577470763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22120024020644211079844069 4147504503870789577470763)
            ·
              refine ⟨6221256755806184366206145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147504503870789577470763 6221256755806184366206145)
              ·
                refine ⟨4665942566854638274654609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6221256755806184366206145 4665942566854638274654609)
                ·
                  refine ⟨3499456925140978705990957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4665942566854638274654609 3499456925140978705990957)
                  ·
                    refine ⟨1312296346927867014746609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499456925140978705990957 1312296346927867014746609)
                    ·
                      rfl

theorem cell22_3833532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_3833532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833532 prefixEnd_3833532 := by exact prefixLift 3833532
  have htrace : WordTrace (prefixWord ++ tailWord_3833532) baseStart_3833532 baseEnd_3833532 := by
    simpa [prefixWord, tailWord_3833532, baseEnd_3833532] using wordTrace_append hprefix tailTrace_3833532
  have hstable : (prefixWord ++ tailWord_3833532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833532).length < 2 ^ (prefixWord ++ tailWord_3833532).sum := by decide
  have hdescent : baseEnd_3833532 < baseStart_3833532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833633 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_3833633 : Nat := 118140960795 + 3833633 * 2 ^ 59
def prefixEnd_3833633 : Nat := 4983230072969 + 3 ^ 40 * 3833633 * 2
def baseEnd_3833633 : Nat := 1312330921291936417971299

theorem tailTrace_3833633 : CollatzResearch.WordTrace tailWord_3833633 prefixEnd_3833633 1312330921291936417971299 := by
  unfold tailWord_3833633
  simp only [CollatzResearch.WordTrace]
  refine ⟨139824082520409848235601553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93216055013606565490401035 139824082520409848235601553)
  ·
    refine ⟨104868061890307386176701165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139824082520409848235601553 104868061890307386176701165)
    ·
      refine ⟨39325523208865269816262937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104868061890307386176701165 39325523208865269816262937)
      ·
        refine ⟨29494142406648952362197203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39325523208865269816262937 29494142406648952362197203)
        ·
          refine ⟨44241213609973428543295805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29494142406648952362197203 44241213609973428543295805)
          ·
            refine ⟨16590455103740035703735927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44241213609973428543295805 16590455103740035703735927)
            ·
              refine ⟨24885682655610053555603891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16590455103740035703735927 24885682655610053555603891)
              ·
                refine ⟨37328523983415080333405837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24885682655610053555603891 37328523983415080333405837)
                ·
                  refine ⟨13998196493780655125027189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37328523983415080333405837 13998196493780655125027189)
                  ·
                    refine ⟨1312330921291936417971299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13998196493780655125027189 1312330921291936417971299)
                    ·
                      rfl

theorem cell22_3833633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_3833633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833633 prefixEnd_3833633 := by exact prefixLift 3833633
  have htrace : WordTrace (prefixWord ++ tailWord_3833633) baseStart_3833633 baseEnd_3833633 := by
    simpa [prefixWord, tailWord_3833633, baseEnd_3833633] using wordTrace_append hprefix tailTrace_3833633
  have hstable : (prefixWord ++ tailWord_3833633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833633).length < 2 ^ (prefixWord ++ tailWord_3833633).sum := by decide
  have hdescent : baseEnd_3833633 < baseStart_3833633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833637 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_3833637 : Nat := 118140960795 + 3833637 * 2 ^ 59
def prefixEnd_3833637 : Nat := 4983230072969 + 3 ^ 40 * 3833637 * 2
def baseEnd_3833637 : Nat := 1312332290573681740871287

theorem tailTrace_3833637 : CollatzResearch.WordTrace tailWord_3833637 prefixEnd_3833637 1312332290573681740871287 := by
  unfold tailWord_3833637
  simp only [CollatzResearch.WordTrace]
  refine ⟨139824228412395356918747165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93216152274930237945831443 139824228412395356918747165)
  ·
    refine ⟨52434085654648258844530187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139824228412395356918747165 52434085654648258844530187)
    ·
      refine ⟨78651128481972388266795281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52434085654648258844530187 78651128481972388266795281)
      ·
        refine ⟨58988346361479291200096461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78651128481972388266795281 58988346361479291200096461)
        ·
          refine ⟨22120629885554734200036173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58988346361479291200096461 22120629885554734200036173)
          ·
            refine ⟨8295236207083025325013565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22120629885554734200036173 8295236207083025325013565)
            ·
              refine ⟨3110713577656134496880087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8295236207083025325013565 3110713577656134496880087)
              ·
                refine ⟨4666070366484201745320131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110713577656134496880087 4666070366484201745320131)
                ·
                  refine ⟨6999105549726302617980197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666070366484201745320131 6999105549726302617980197)
                  ·
                    refine ⟨1312332290573681740871287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6999105549726302617980197 1312332290573681740871287)
                    ·
                      rfl

theorem cell22_3833637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_3833637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833637 prefixEnd_3833637 := by exact prefixLift 3833637
  have htrace : WordTrace (prefixWord ++ tailWord_3833637) baseStart_3833637 baseEnd_3833637 := by
    simpa [prefixWord, tailWord_3833637, baseEnd_3833637] using wordTrace_append hprefix tailTrace_3833637
  have hstable : (prefixWord ++ tailWord_3833637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833637).length < 2 ^ (prefixWord ++ tailWord_3833637).sum := by decide
  have hdescent : baseEnd_3833637 < baseStart_3833637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833682 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_3833682 : Nat := 118140960795 + 3833682 * 2 ^ 59
def prefixEnd_3833682 : Nat := 4983230072969 + 3 ^ 40 * 3833682 * 2
def baseEnd_3833682 : Nat := 1312347694993316623496149

theorem tailTrace_3833682 : CollatzResearch.WordTrace tailWord_3833682 prefixEnd_3833682 1312347694993316623496149 := by
  unfold tailWord_3833682
  simp only [CollatzResearch.WordTrace]
  refine ⟨34956467424308082401033825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93217246464821553069423533 34956467424308082401033825)
  ·
    refine ⟨26217350568231061800775369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34956467424308082401033825 26217350568231061800775369)
    ·
      refine ⟨19663012926173296350581527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26217350568231061800775369 19663012926173296350581527)
      ·
        refine ⟨29494519389259944525872291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19663012926173296350581527 29494519389259944525872291)
        ·
          refine ⟨44241779083889916788808437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29494519389259944525872291 44241779083889916788808437)
          ·
            refine ⟨4147666789114679698950791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44241779083889916788808437 4147666789114679698950791)
            ·
              refine ⟨6221500183672019548426187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147666789114679698950791 6221500183672019548426187)
              ·
                refine ⟨9332250275508029322639281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221500183672019548426187 9332250275508029322639281)
                ·
                  refine ⟨6999187706631021991979461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9332250275508029322639281 6999187706631021991979461)
                  ·
                    refine ⟨1312347694993316623496149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6999187706631021991979461 1312347694993316623496149)
                    ·
                      rfl

theorem cell22_3833682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_3833682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833682 prefixEnd_3833682 := by exact prefixLift 3833682
  have htrace : WordTrace (prefixWord ++ tailWord_3833682) baseStart_3833682 baseEnd_3833682 := by
    simpa [prefixWord, tailWord_3833682, baseEnd_3833682] using wordTrace_append hprefix tailTrace_3833682
  have hstable : (prefixWord ++ tailWord_3833682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833682).length < 2 ^ (prefixWord ++ tailWord_3833682).sum := by decide
  have hdescent : baseEnd_3833682 < baseStart_3833682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833746 : List Nat := [3, 2, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3833746 : Nat := 118140960795 + 3833746 * 2 ^ 59
def prefixEnd_3833746 : Nat := 4983230072969 + 3 ^ 40 * 3833746 * 2
def baseEnd_3833746 : Nat := 1312369603501241789895953

theorem tailTrace_3833746 : CollatzResearch.WordTrace tailWord_3833746 prefixEnd_3833746 1312369603501241789895953 := by
  unfold tailWord_3833746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34957050992250117133616273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93218802646000312356310061 34957050992250117133616273)
  ·
    refine ⟨26217788244187587850212205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34957050992250117133616273 26217788244187587850212205)
    ·
      refine ⟨9831670591570345443829577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26217788244187587850212205 9831670591570345443829577)
      ·
        refine ⟨7373752943677759082872183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9831670591570345443829577 7373752943677759082872183)
        ·
          refine ⟨11060629415516638624308275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373752943677759082872183 11060629415516638624308275)
          ·
            refine ⟨16590944123274957936462413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060629415516638624308275 16590944123274957936462413)
            ·
              refine ⟨6221604046228109226173405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16590944123274957936462413 6221604046228109226173405)
              ·
                refine ⟨2333101517335540959815027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6221604046228109226173405 2333101517335540959815027)
                ·
                  refine ⟨3499652276003311439722541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333101517335540959815027 3499652276003311439722541)
                  ·
                    refine ⟨1312369603501241789895953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499652276003311439722541 1312369603501241789895953)
                    ·
                      rfl

theorem cell22_3833746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3833746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833746 prefixEnd_3833746 := by exact prefixLift 3833746
  have htrace : WordTrace (prefixWord ++ tailWord_3833746) baseStart_3833746 baseEnd_3833746 := by
    simpa [prefixWord, tailWord_3833746, baseEnd_3833746] using wordTrace_append hprefix tailTrace_3833746
  have hstable : (prefixWord ++ tailWord_3833746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833746).length < 2 ^ (prefixWord ++ tailWord_3833746).sum := by decide
  have hdescent : baseEnd_3833746 < baseStart_3833746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833753 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 8]
def baseStart_3833753 : Nat := 118140960795 + 3833753 * 2 ^ 59
def prefixEnd_3833753 : Nat := 4983230072969 + 3 ^ 40 * 3833753 * 2
def baseEnd_3833753 : Nat := 437457333248098701656977

theorem tailTrace_3833753 : CollatzResearch.WordTrace tailWord_3833753 prefixEnd_3833753 437457333248098701656977 := by
  unfold tailWord_3833753
  simp only [CollatzResearch.WordTrace]
  refine ⟨139828459279975108729969913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93218972853316739153313275 139828459279975108729969913)
  ·
    refine ⟨104871344459981331547477435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139828459279975108729969913 104871344459981331547477435)
    ·
      refine ⟨157307016689971997321216153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104871344459981331547477435 157307016689971997321216153)
      ·
        refine ⟨117980262517478997990912115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157307016689971997321216153 117980262517478997990912115)
        ·
          refine ⟨176970393776218496986368173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117980262517478997990912115 176970393776218496986368173)
          ·
            refine ⟨66363897666081936369888065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176970393776218496986368173 66363897666081936369888065)
            ·
              refine ⟨49772923249561452277416049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66363897666081936369888065 49772923249561452277416049)
              ·
                refine ⟨37329692437171089208062037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49772923249561452277416049 37329692437171089208062037)
                ·
                  refine ⟨437457333248098701656977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37329692437171089208062037 437457333248098701656977)
                  ·
                    rfl

theorem cell22_3833753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_3833753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833753 prefixEnd_3833753 := by exact prefixLift 3833753
  have htrace : WordTrace (prefixWord ++ tailWord_3833753) baseStart_3833753 baseEnd_3833753 := by
    simpa [prefixWord, tailWord_3833753, baseEnd_3833753] using wordTrace_append hprefix tailTrace_3833753
  have hstable : (prefixWord ++ tailWord_3833753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833753).length < 2 ^ (prefixWord ++ tailWord_3833753).sum := by decide
  have hdescent : baseEnd_3833753 < baseStart_3833753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833785 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_3833785 : Nat := 118140960795 + 3833785 * 2 ^ 59
def prefixEnd_3833785 : Nat := 4983230072969 + 3 ^ 40 * 3833785 * 2
def baseEnd_3833785 : Nat := 1312382953998258688170833

theorem tailTrace_3833785 : CollatzResearch.WordTrace tailWord_3833785 prefixEnd_3833785 1312382953998258688170833 := by
  unfold tailWord_3833785
  simp only [CollatzResearch.WordTrace]
  refine ⟨139829626415859178195134809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93219750943906118796756539 139829626415859178195134809)
  ·
    refine ⟨104872219811894383646351107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139829626415859178195134809 104872219811894383646351107)
    ·
      refine ⟨157308329717841575469526661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104872219811894383646351107 157308329717841575469526661)
      ·
        refine ⟨29495311822095295400536249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157308329717841575469526661 29495311822095295400536249)
        ·
          refine ⟨22121483866571471550402187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29495311822095295400536249 22121483866571471550402187)
          ·
            refine ⟨33182225799857207325603281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22121483866571471550402187 33182225799857207325603281)
            ·
              refine ⟨24886669349892905494202461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33182225799857207325603281 24886669349892905494202461)
              ·
                refine ⟨9332501006209839560325923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24886669349892905494202461 9332501006209839560325923)
                ·
                  refine ⟨13998751509314759340488885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9332501006209839560325923 13998751509314759340488885)
                  ·
                    refine ⟨1312382953998258688170833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13998751509314759340488885 1312382953998258688170833)
                    ·
                      rfl

theorem cell22_3833785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_3833785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833785 prefixEnd_3833785 := by exact prefixLift 3833785
  have htrace : WordTrace (prefixWord ++ tailWord_3833785) baseStart_3833785 baseEnd_3833785 := by
    simpa [prefixWord, tailWord_3833785, baseEnd_3833785] using wordTrace_append hprefix tailTrace_3833785
  have hstable : (prefixWord ++ tailWord_3833785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833785).length < 2 ^ (prefixWord ++ tailWord_3833785).sum := by decide
  have hdescent : baseEnd_3833785 < baseStart_3833785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833789 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_3833789 : Nat := 118140960795 + 3833789 * 2 ^ 59
def prefixEnd_3833789 : Nat := 4983230072969 + 3 ^ 40 * 3833789 * 2
def baseEnd_3833789 : Nat := 1312384323280004011070821

theorem tailTrace_3833789 : CollatzResearch.WordTrace tailWord_3833789 prefixEnd_3833789 1312384323280004011070821 := by
  unfold tailWord_3833789
  simp only [CollatzResearch.WordTrace]
  refine ⟨139829772307844686878280421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93219848205229791252186947 139829772307844686878280421)
  ·
    refine ⟨26218082307720878789677579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139829772307844686878280421 26218082307720878789677579)
    ·
      refine ⟨39327123461581318184516369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26218082307720878789677579 39327123461581318184516369)
      ·
        refine ⟨29495342596185988638387277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39327123461581318184516369 29495342596185988638387277)
        ·
          refine ⟨11060753473569745739395229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29495342596185988638387277 11060753473569745739395229)
          ·
            refine ⟨4147782552588654652273211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11060753473569745739395229 4147782552588654652273211)
            ·
              refine ⟨6221673828882981978409817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147782552588654652273211 6221673828882981978409817)
              ·
                refine ⟨4666255371662236483807363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6221673828882981978409817 4666255371662236483807363)
                ·
                  refine ⟨6999383057493354725711045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666255371662236483807363 6999383057493354725711045)
                  ·
                    refine ⟨1312384323280004011070821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6999383057493354725711045 1312384323280004011070821)
                    ·
                      rfl

theorem cell22_3833789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_3833789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833789 prefixEnd_3833789 := by exact prefixLift 3833789
  have htrace : WordTrace (prefixWord ++ tailWord_3833789) baseStart_3833789 baseEnd_3833789 := by
    simpa [prefixWord, tailWord_3833789, baseEnd_3833789] using wordTrace_append hprefix tailTrace_3833789
  have hstable : (prefixWord ++ tailWord_3833789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833789).length < 2 ^ (prefixWord ++ tailWord_3833789).sum := by decide
  have hdescent : baseEnd_3833789 < baseStart_3833789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833875 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 2, 5]
def baseStart_3833875 : Nat := 118140960795 + 3833875 * 2 ^ 59
def prefixEnd_3833875 : Nat := 4983230072969 + 3 ^ 40 * 3833875 * 2
def baseEnd_3833875 : Nat := 1312413762837528453420557

theorem tailTrace_3833875 : CollatzResearch.WordTrace tailWord_3833875 prefixEnd_3833875 1312413762837528453420557 := by
  unfold tailWord_3833875
  simp only [CollatzResearch.WordTrace]
  refine ⟨139832908985533123565911079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93221939323688749043940719 139832908985533123565911079)
  ·
    refine ⟨209749363478299685348866619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139832908985533123565911079 209749363478299685348866619)
    ·
      refine ⟨314624045217449528023299929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209749363478299685348866619 314624045217449528023299929)
      ·
        refine ⟨235968033913087146017474947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314624045217449528023299929 235968033913087146017474947)
        ·
          refine ⟨353952050869630719026212421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235968033913087146017474947 353952050869630719026212421)
          ·
            refine ⟨66366009538055759817414829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353952050869630719026212421 66366009538055759817414829)
            ·
              refine ⟨24887253576770909931530561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66366009538055759817414829 24887253576770909931530561)
              ·
                refine ⟨18665440182578182448647921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24887253576770909931530561 18665440182578182448647921)
                ·
                  refine ⟨13999080136933636836485941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18665440182578182448647921 13999080136933636836485941)
                  ·
                    refine ⟨1312413762837528453420557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13999080136933636836485941 1312413762837528453420557)
                    ·
                      rfl

theorem cell22_3833875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_3833875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833875 prefixEnd_3833875 := by exact prefixLift 3833875
  have htrace : WordTrace (prefixWord ++ tailWord_3833875) baseStart_3833875 baseEnd_3833875 := by
    simpa [prefixWord, tailWord_3833875, baseEnd_3833875] using wordTrace_append hprefix tailTrace_3833875
  have hstable : (prefixWord ++ tailWord_3833875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833875).length < 2 ^ (prefixWord ++ tailWord_3833875).sum := by decide
  have hdescent : baseEnd_3833875 < baseStart_3833875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833877 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 7]
def baseStart_3833877 : Nat := 118140960795 + 3833877 * 2 ^ 59
def prefixEnd_3833877 : Nat := 4983230072969 + 3 ^ 40 * 3833877 * 2
def baseEnd_3833877 : Nat := 437471482492800371623517

theorem tailTrace_3833877 : CollatzResearch.WordTrace tailWord_3833877 prefixEnd_3833877 437471482492800371623517 := by
  unfold tailWord_3833877
  simp only [CollatzResearch.WordTrace]
  refine ⟨139832981931525877907483885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93221987954350585271655923 139832981931525877907483885)
  ·
    refine ⟨52437368224322204215306457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139832981931525877907483885 52437368224322204215306457)
    ·
      refine ⟨39328026168241653161479843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52437368224322204215306457 39328026168241653161479843)
      ·
        refine ⟨58992039252362479742219765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39328026168241653161479843 58992039252362479742219765)
        ·
          refine ⟨5530503679908982475833103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58992039252362479742219765 5530503679908982475833103)
          ·
            refine ⟨8295755519863473713749655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530503679908982475833103 8295755519863473713749655)
            ·
              refine ⟨12443633279795210570624483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8295755519863473713749655 12443633279795210570624483)
              ·
                refine ⟨18665449919692815855936725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12443633279795210570624483 18665449919692815855936725)
                ·
                  refine ⟨437471482492800371623517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18665449919692815855936725 437471482492800371623517)
                  ·
                    rfl

theorem cell22_3833877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_3833877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833877 prefixEnd_3833877 := by exact prefixLift 3833877
  have htrace : WordTrace (prefixWord ++ tailWord_3833877) baseStart_3833877 baseEnd_3833877 := by
    simpa [prefixWord, tailWord_3833877, baseEnd_3833877] using wordTrace_append hprefix tailTrace_3833877
  have hstable : (prefixWord ++ tailWord_3833877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833877).length < 2 ^ (prefixWord ++ tailWord_3833877).sum := by decide
  have hdescent : baseEnd_3833877 < baseStart_3833877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3833907 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 1, 4]
def baseStart_3833907 : Nat := 118140960795 + 3833907 * 2 ^ 59
def prefixEnd_3833907 : Nat := 4983230072969 + 3 ^ 40 * 3833907 * 2
def baseEnd_3833907 : Nat := 1312424717091491036620459

theorem tailTrace_3833907 : CollatzResearch.WordTrace tailWord_3833907 prefixEnd_3833907 1312424717091491036620459 := by
  unfold tailWord_3833907
  simp only [CollatzResearch.WordTrace]
  refine ⟨139834076121417193031075975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93222717414278128687383983 139834076121417193031075975)
  ·
    refine ⟨209751114182125789546613963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139834076121417193031075975 209751114182125789546613963)
    ·
      refine ⟨314626671273188684319920945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209751114182125789546613963 314626671273188684319920945)
      ·
        refine ⟨235970003454891513239940709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314626671273188684319920945 235970003454891513239940709)
        ·
          refine ⟨44244375647792158732488883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235970003454891513239940709 44244375647792158732488883)
          ·
            refine ⟨66366563471688238098733325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44244375647792158732488883 66366563471688238098733325)
            ·
              refine ⟨24887461301883089287024997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66366563471688238098733325 24887461301883089287024997)
              ·
                refine ⟨4666398994103079241317187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24887461301883089287024997 4666398994103079241317187)
                ·
                  refine ⟨6999598491154618861975781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666398994103079241317187 6999598491154618861975781)
                  ·
                    refine ⟨1312424717091491036620459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6999598491154618861975781 1312424717091491036620459)
                    ·
                      rfl

theorem cell22_3833907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 4].length) (baseStart_3833907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3833907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3833907 prefixEnd_3833907 := by exact prefixLift 3833907
  have htrace : WordTrace (prefixWord ++ tailWord_3833907) baseStart_3833907 baseEnd_3833907 := by
    simpa [prefixWord, tailWord_3833907, baseEnd_3833907] using wordTrace_append hprefix tailTrace_3833907
  have hstable : (prefixWord ++ tailWord_3833907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3833907).length < 2 ^ (prefixWord ++ tailWord_3833907).sum := by decide
  have hdescent : baseEnd_3833907 < baseStart_3833907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3833907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834050 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3834050 : Nat := 118140960795 + 3834050 * 2 ^ 59
def prefixEnd_3834050 : Nat := 4983230072969 + 3 ^ 40 * 3834050 * 2
def baseEnd_3834050 : Nat := 1312473668913886330295021

theorem tailTrace_3834050 : CollatzResearch.WordTrace tailWord_3834050 prefixEnd_3834050 1312473668913886330295021 := by
  unfold tailWord_3834050
  simp only [CollatzResearch.WordTrace]
  refine ⟨34959822939974782113382901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93226194506599418969021069 34959822939974782113382901)
  ·
    refine ⟨3277483400622635823129647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34959822939974782113382901 3277483400622635823129647)
    ·
      refine ⟨4916225100933953734694471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3277483400622635823129647 4916225100933953734694471)
      ·
        refine ⟨7374337651400930602041707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4916225100933953734694471 7374337651400930602041707)
        ·
          refine ⟨11061506477101395903062561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7374337651400930602041707 11061506477101395903062561)
          ·
            refine ⟨8296129857826046927296921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11061506477101395903062561 8296129857826046927296921)
            ·
              refine ⟨6222097393369535195472691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8296129857826046927296921 6222097393369535195472691)
              ·
                refine ⟨9333146090054302793209037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6222097393369535195472691 9333146090054302793209037)
                ·
                  refine ⟨3499929783770363547453389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9333146090054302793209037 3499929783770363547453389)
                  ·
                    refine ⟨1312473668913886330295021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499929783770363547453389 1312473668913886330295021)
                    ·
                      rfl

theorem cell22_3834050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3834050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834050 prefixEnd_3834050 := by exact prefixLift 3834050
  have htrace : WordTrace (prefixWord ++ tailWord_3834050) baseStart_3834050 baseEnd_3834050 := by
    simpa [prefixWord, tailWord_3834050, baseEnd_3834050] using wordTrace_append hprefix tailTrace_3834050
  have hstable : (prefixWord ++ tailWord_3834050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834050).length < 2 ^ (prefixWord ++ tailWord_3834050).sum := by decide
  have hdescent : baseEnd_3834050 < baseStart_3834050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834108 : List Nat := [2, 2, 2, 1, 4, 2, 3, 2, 4]
def baseStart_3834108 : Nat := 118140960795 + 3834108 * 2 ^ 59
def prefixEnd_3834108 : Nat := 4983230072969 + 3 ^ 40 * 3834108 * 2
def baseEnd_3834108 : Nat := 437497841166397837448281

theorem tailTrace_3834108 : CollatzResearch.WordTrace tailWord_3834108 prefixEnd_3834108 437497841166397837448281 := by
  unfold tailWord_3834108
  simp only [CollatzResearch.WordTrace]
  refine ⟨69920703596844502179571489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93227604795792669572761985 69920703596844502179571489)
  ·
    refine ⟨52440527697633376634678617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69920703596844502179571489 52440527697633376634678617)
    ·
      refine ⟨39330395773225032476008963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52440527697633376634678617 39330395773225032476008963)
      ·
        refine ⟨58995593659837548714013445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39330395773225032476008963 58995593659837548714013445)
        ·
          refine ⟨11061673811219540383877521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58995593659837548714013445 11061673811219540383877521)
          ·
            refine ⟨8296255358414655287908141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11061673811219540383877521 8296255358414655287908141)
            ·
              refine ⟨3111095759405495732965553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8296255358414655287908141 3111095759405495732965553)
              ·
                refine ⟨2333321819554121799724165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111095759405495732965553 2333321819554121799724165)
                ·
                  refine ⟨437497841166397837448281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2333321819554121799724165 437497841166397837448281)
                  ·
                    rfl

theorem cell22_3834108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_3834108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834108 prefixEnd_3834108 := by exact prefixLift 3834108
  have htrace : WordTrace (prefixWord ++ tailWord_3834108) baseStart_3834108 baseEnd_3834108 := by
    simpa [prefixWord, tailWord_3834108, baseEnd_3834108] using wordTrace_append hprefix tailTrace_3834108
  have hstable : (prefixWord ++ tailWord_3834108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834108).length < 2 ^ (prefixWord ++ tailWord_3834108).sum := by decide
  have hdescent : baseEnd_3834108 < baseStart_3834108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834117 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_3834117 : Nat := 118140960795 + 3834117 * 2 ^ 59
def prefixEnd_3834117 : Nat := 4983230072969 + 3 ^ 40 * 3834117 * 2
def baseEnd_3834117 : Nat := 1312496604383120488869815

theorem tailTrace_3834117 : CollatzResearch.WordTrace tailWord_3834117 prefixEnd_3834117 1312496604383120488869815 := by
  unfold tailWord_3834117
  simp only [CollatzResearch.WordTrace]
  refine ⟨139841735450656398896220605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93227823633770932597480403 139841735450656398896220605)
  ·
    refine ⟨52440650793996149586082727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139841735450656398896220605 52440650793996149586082727)
    ·
      refine ⟨78660976190994224379124091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52440650793996149586082727 78660976190994224379124091)
      ·
        refine ⟨117991464286491336568686137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78660976190994224379124091 117991464286491336568686137)
        ·
          refine ⟨88493598214868502426514603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117991464286491336568686137 88493598214868502426514603)
          ·
            refine ⟨132740397322302753639771905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88493598214868502426514603 132740397322302753639771905)
            ·
              refine ⟨99555297991727065229828929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132740397322302753639771905 99555297991727065229828929)
              ·
                refine ⟨74666473493795298922371697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99555297991727065229828929 74666473493795298922371697)
                ·
                  refine ⟨55999855120346474191778773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74666473493795298922371697 55999855120346474191778773)
                  ·
                    refine ⟨1312496604383120488869815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55999855120346474191778773 1312496604383120488869815)
                    ·
                      rfl

theorem cell22_3834117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_3834117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834117 prefixEnd_3834117 := by exact prefixLift 3834117
  have htrace : WordTrace (prefixWord ++ tailWord_3834117) baseStart_3834117 baseEnd_3834117 := by
    simpa [prefixWord, tailWord_3834117, baseEnd_3834117] using wordTrace_append hprefix tailTrace_3834117
  have hstable : (prefixWord ++ tailWord_3834117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834117).length < 2 ^ (prefixWord ++ tailWord_3834117).sum := by decide
  have hdescent : baseEnd_3834117 < baseStart_3834117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834211 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 1, 4]
def baseStart_3834211 : Nat := 118140960795 + 3834211 * 2 ^ 59
def prefixEnd_3834211 : Nat := 4983230072969 + 3 ^ 40 * 3834211 * 2
def baseEnd_3834211 : Nat := 1312528782504135577019527

theorem tailTrace_3834211 : CollatzResearch.WordTrace tailWord_3834211 prefixEnd_3834211 1312528782504135577019527 := by
  unfold tailWord_3834211
  simp only [CollatzResearch.WordTrace]
  refine ⟨139845163912315852950142487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93230109274877235300094991 139845163912315852950142487)
  ·
    refine ⟨209767745868473779425213731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139845163912315852950142487 209767745868473779425213731)
    ·
      refine ⟨314651618802710669137820597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209767745868473779425213731 314651618802710669137820597)
      ·
        refine ⟨29498589262754125231670681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 314651618802710669137820597 29498589262754125231670681)
        ·
          refine ⟨22123941947065593923753011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29498589262754125231670681 22123941947065593923753011)
          ·
            refine ⟨33185912920598390885629517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22123941947065593923753011 33185912920598390885629517)
            ·
              refine ⟨12444717345224396582111069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33185912920598390885629517 12444717345224396582111069)
              ·
                refine ⟨4666769004459148718291651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12444717345224396582111069 4666769004459148718291651)
                ·
                  refine ⟨7000153506688723077437477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666769004459148718291651 7000153506688723077437477)
                  ·
                    refine ⟨1312528782504135577019527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000153506688723077437477 1312528782504135577019527)
                    ·
                      rfl

theorem cell22_3834211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 4].length) (baseStart_3834211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834211 prefixEnd_3834211 := by exact prefixLift 3834211
  have htrace : WordTrace (prefixWord ++ tailWord_3834211) baseStart_3834211 baseEnd_3834211 := by
    simpa [prefixWord, tailWord_3834211, baseEnd_3834211] using wordTrace_append hprefix tailTrace_3834211
  have hstable : (prefixWord ++ tailWord_3834211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834211).length < 2 ^ (prefixWord ++ tailWord_3834211).sum := by decide
  have hdescent : baseEnd_3834211 < baseStart_3834211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834226 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_3834226 : Nat := 118140960795 + 3834226 * 2 ^ 59
def prefixEnd_3834226 : Nat := 4983230072969 + 3 ^ 40 * 3834226 * 2
def baseEnd_3834226 : Nat := 437511305770226845964827

theorem tailTrace_3834226 : CollatzResearch.WordTrace tailWord_3834226 prefixEnd_3834226 437511305770226845964827 := by
  unfold tailWord_3834226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34961427751815377627984633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93230474004841007007959021 34961427751815377627984633)
  ·
    refine ⟨26221070813861533220988475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34961427751815377627984633 26221070813861533220988475)
    ·
      refine ⟨39331606220792299831482713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26221070813861533220988475 39331606220792299831482713)
      ·
        refine ⟨29498704665594224873612035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39331606220792299831482713 29498704665594224873612035)
        ·
          refine ⟨44248056998391337310418053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29498704665594224873612035 44248056998391337310418053)
          ·
            refine ⟨8296510687198375745703385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44248056998391337310418053 8296510687198375745703385)
            ·
              refine ⟨6222383015398781809277539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8296510687198375745703385 6222383015398781809277539)
              ·
                refine ⟨9333574523098172713916309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6222383015398781809277539 9333574523098172713916309)
                ·
                  refine ⟨437511305770226845964827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9333574523098172713916309 437511305770226845964827)
                  ·
                    rfl

theorem cell22_3834226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_3834226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834226 prefixEnd_3834226 := by exact prefixLift 3834226
  have htrace : WordTrace (prefixWord ++ tailWord_3834226) baseStart_3834226 baseEnd_3834226 := by
    simpa [prefixWord, tailWord_3834226, baseEnd_3834226] using wordTrace_append hprefix tailTrace_3834226
  have hstable : (prefixWord ++ tailWord_3834226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834226).length < 2 ^ (prefixWord ++ tailWord_3834226).sum := by decide
  have hdescent : baseEnd_3834226 < baseStart_3834226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834239 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 4, 4]
def baseStart_3834239 : Nat := 118140960795 + 3834239 * 2 ^ 59
def prefixEnd_3834239 : Nat := 4983230072969 + 3 ^ 40 * 3834239 * 2
def baseEnd_3834239 : Nat := 1312538367476352837319441

theorem tailTrace_3834239 : CollatzResearch.WordTrace tailWord_3834239 prefixEnd_3834239 1312538367476352837319441 := by
  unfold tailWord_3834239
  simp only [CollatzResearch.WordTrace]
  refine ⟨139846185156214413732161771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93230790104142942488107847 139846185156214413732161771)
  ·
    refine ⟨209769277734321620598242657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139846185156214413732161771 209769277734321620598242657)
    ·
      refine ⟨157326958300741215448681993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209769277734321620598242657 157326958300741215448681993)
      ·
        refine ⟨117995218725555911586511495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157326958300741215448681993 117995218725555911586511495)
        ·
          refine ⟨176992828088333867379767243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117995218725555911586511495 176992828088333867379767243)
          ·
            refine ⟨265489242132500801069650865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176992828088333867379767243 265489242132500801069650865)
            ·
              refine ⟨199116931599375600802238149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265489242132500801069650865 199116931599375600802238149)
              ·
                refine ⟨37334424674882925150419653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199116931599375600802238149 37334424674882925150419653)
                ·
                  refine ⟨7000204626540548465703685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37334424674882925150419653 7000204626540548465703685)
                  ·
                    refine ⟨1312538367476352837319441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000204626540548465703685 1312538367476352837319441)
                    ·
                      rfl

theorem cell22_3834239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_3834239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834239 prefixEnd_3834239 := by exact prefixLift 3834239
  have htrace : WordTrace (prefixWord ++ tailWord_3834239) baseStart_3834239 baseEnd_3834239 := by
    simpa [prefixWord, tailWord_3834239, baseEnd_3834239] using wordTrace_append hprefix tailTrace_3834239
  have hstable : (prefixWord ++ tailWord_3834239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834239).length < 2 ^ (prefixWord ++ tailWord_3834239).sum := by decide
  have hdescent : baseEnd_3834239 < baseStart_3834239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834284 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_3834284 : Nat := 118140960795 + 3834284 * 2 ^ 59
def prefixEnd_3834284 : Nat := 4983230072969 + 3 ^ 40 * 3834284 * 2
def baseEnd_3834284 : Nat := 1312553771895987719944303

theorem tailTrace_3834284 : CollatzResearch.WordTrace tailWord_3834284 prefixEnd_3834284 1312553771895987719944303 := by
  unfold tailWord_3834284
  simp only [CollatzResearch.WordTrace]
  refine ⟨69923913220525693208774953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93231884294034257611699937 69923913220525693208774953)
  ·
    refine ⟨52442934915394269906581215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69923913220525693208774953 52442934915394269906581215)
    ·
      refine ⟨78664402373091404859871823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52442934915394269906581215 78664402373091404859871823)
      ·
        refine ⟨117996603559637107289807735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78664402373091404859871823 117996603559637107289807735)
        ·
          refine ⟨176994905339455660934711603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117996603559637107289807735 176994905339455660934711603)
          ·
            refine ⟨265492358009183491402067405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176994905339455660934711603 265492358009183491402067405)
            ·
              refine ⟨99559634253443809275775277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265492358009183491402067405 99559634253443809275775277)
              ·
                refine ⟨37334862845041428478415729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99559634253443809275775277 37334862845041428478415729)
                ·
                  refine ⟨28001147133781071358811797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37334862845041428478415729 28001147133781071358811797)
                  ·
                    refine ⟨1312553771895987719944303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28001147133781071358811797 1312553771895987719944303)
                    ·
                      rfl

theorem cell22_3834284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_3834284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834284 prefixEnd_3834284 := by exact prefixLift 3834284
  have htrace : WordTrace (prefixWord ++ tailWord_3834284) baseStart_3834284 baseEnd_3834284 := by
    simpa [prefixWord, tailWord_3834284, baseEnd_3834284] using wordTrace_append hprefix tailTrace_3834284
  have hstable : (prefixWord ++ tailWord_3834284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834284).length < 2 ^ (prefixWord ++ tailWord_3834284).sum := by decide
  have hdescent : baseEnd_3834284 < baseStart_3834284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834333 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3834333 : Nat := 118140960795 + 3834333 * 2 ^ 59
def prefixEnd_3834333 : Nat := 4983230072969 + 3 ^ 40 * 3834333 * 2
def baseEnd_3834333 : Nat := 437523515199122641823051

theorem tailTrace_3834333 : CollatzResearch.WordTrace tailWord_3834333 prefixEnd_3834333 437523515199122641823051 := by
  unfold tailWord_3834333
  simp only [CollatzResearch.WordTrace]
  refine ⟨139849613617873867786083653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93233075745249245190722435 139849613617873867786083653)
  ·
    refine ⟨26221802553351350209890685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139849613617873867786083653 26221802553351350209890685)
    ·
      refine ⟨9833175957506756328709007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26221802553351350209890685 9833175957506756328709007)
      ·
        refine ⟨14749763936260134493063511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9833175957506756328709007 14749763936260134493063511)
        ·
          refine ⟨22124645904390201739595267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14749763936260134493063511 22124645904390201739595267)
          ·
            refine ⟨33186968856585302609392901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22124645904390201739595267 33186968856585302609392901)
            ·
              refine ⟨6222556660609744239261169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33186968856585302609392901 6222556660609744239261169)
              ·
                refine ⟨4666917495457308179445877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6222556660609744239261169 4666917495457308179445877)
                ·
                  refine ⟨437523515199122641823051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4666917495457308179445877 437523515199122641823051)
                  ·
                    rfl

theorem cell22_3834333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3834333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834333 prefixEnd_3834333 := by exact prefixLift 3834333
  have htrace : WordTrace (prefixWord ++ tailWord_3834333) baseStart_3834333 baseEnd_3834333 := by
    simpa [prefixWord, tailWord_3834333, baseEnd_3834333] using wordTrace_append hprefix tailTrace_3834333
  have hstable : (prefixWord ++ tailWord_3834333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834333).length < 2 ^ (prefixWord ++ tailWord_3834333).sum := by decide
  have hdescent : baseEnd_3834333 < baseStart_3834333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834380 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_3834380 : Nat := 118140960795 + 3834380 * 2 ^ 59
def prefixEnd_3834380 : Nat := 4983230072969 + 3 ^ 40 * 3834380 * 2
def baseEnd_3834380 : Nat := 1312586634657875469544009

theorem tailTrace_3834380 : CollatzResearch.WordTrace tailWord_3834380 prefixEnd_3834380 1312586634657875469544009 := by
  unfold tailWord_3834380
  simp only [CollatzResearch.WordTrace]
  refine ⟨69925663924351797406522297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93234218565802396542029729 69925663924351797406522297)
  ·
    refine ⟨52444247943263848054891723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69925663924351797406522297 52444247943263848054891723)
    ·
      refine ⟨78666371914895772082337585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52444247943263848054891723 78666371914895772082337585)
      ·
        refine ⟨58999778936171829061753189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78666371914895772082337585 58999778936171829061753189)
        ·
          refine ⟨11062458550532217949078723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58999778936171829061753189 11062458550532217949078723)
          ·
            refine ⟨16593687825798326923618085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11062458550532217949078723 16593687825798326923618085)
            ·
              refine ⟨3111316467337186298178391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16593687825798326923618085 3111316467337186298178391)
              ·
                refine ⟨4666974701005779447267587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111316467337186298178391 4666974701005779447267587)
                ·
                  refine ⟨7000462051508669170901381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666974701005779447267587 7000462051508669170901381)
                  ·
                    refine ⟨1312586634657875469544009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000462051508669170901381 1312586634657875469544009)
                    ·
                      rfl

theorem cell22_3834380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_3834380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834380 prefixEnd_3834380 := by exact prefixLift 3834380
  have htrace : WordTrace (prefixWord ++ tailWord_3834380) baseStart_3834380 baseEnd_3834380 := by
    simpa [prefixWord, tailWord_3834380, baseEnd_3834380] using wordTrace_append hprefix tailTrace_3834380
  have hstable : (prefixWord ++ tailWord_3834380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834380).length < 2 ^ (prefixWord ++ tailWord_3834380).sum := by decide
  have hdescent : baseEnd_3834380 < baseStart_3834380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834408 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3834408 : Nat := 118140960795 + 3834408 * 2 ^ 59
def prefixEnd_3834408 : Nat := 4983230072969 + 3 ^ 40 * 3834408 * 2
def baseEnd_3834408 : Nat := 1312596219630092729843923

theorem tailTrace_3834408 : CollatzResearch.WordTrace tailWord_3834408 prefixEnd_3834408 1312596219630092729843923 := by
  unfold tailWord_3834408
  simp only [CollatzResearch.WordTrace]
  refine ⟨69926174546301077797531939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93234899395068103730042585 69926174546301077797531939)
  ·
    refine ⟨104889261819451616696297909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69926174546301077797531939 104889261819451616696297909)
    ·
      refine ⟨9833368295573589065277929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104889261819451616696297909 9833368295573589065277929)
      ·
        refine ⟨7375026221680191798958447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9833368295573589065277929 7375026221680191798958447)
        ·
          refine ⟨11062539332520287698437671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375026221680191798958447 11062539332520287698437671)
          ·
            refine ⟨16593808998780431547656507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11062539332520287698437671 16593808998780431547656507)
            ·
              refine ⟨24890713498170647321484761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16593808998780431547656507 24890713498170647321484761)
              ·
                refine ⟨18668035123627985491113571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24890713498170647321484761 18668035123627985491113571)
                ·
                  refine ⟨28002052685441978236670357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18668035123627985491113571 28002052685441978236670357)
                  ·
                    refine ⟨1312596219630092729843923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28002052685441978236670357 1312596219630092729843923)
                    ·
                      rfl

theorem cell22_3834408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3834408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834408 prefixEnd_3834408 := by exact prefixLift 3834408
  have htrace : WordTrace (prefixWord ++ tailWord_3834408) baseStart_3834408 baseEnd_3834408 := by
    simpa [prefixWord, tailWord_3834408, baseEnd_3834408] using wordTrace_append hprefix tailTrace_3834408
  have hstable : (prefixWord ++ tailWord_3834408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834408).length < 2 ^ (prefixWord ++ tailWord_3834408).sum := by decide
  have hdescent : baseEnd_3834408 < baseStart_3834408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834410 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3834410 : Nat := 118140960795 + 3834410 * 2 ^ 59
def prefixEnd_3834410 : Nat := 4983230072969 + 3 ^ 40 * 3834410 * 2
def baseEnd_3834410 : Nat := 1312596904270965391293917

theorem tailTrace_3834410 : CollatzResearch.WordTrace tailWord_3834410 prefixEnd_3834410 1312596904270965391293917 := by
  unfold tailWord_3834410
  simp only [CollatzResearch.WordTrace]
  refine ⟨34963105509648727484159171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93234948025729939957757789 34963105509648727484159171)
  ·
    refine ⟨52444658264473091226238757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34963105509648727484159171 52444658264473091226238757)
    ·
      refine ⟨9833373424588704604919767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52444658264473091226238757 9833373424588704604919767)
      ·
        refine ⟨14750060136883056907379651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9833373424588704604919767 14750060136883056907379651)
        ·
          refine ⟨22125090205324585361069477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14750060136883056907379651 22125090205324585361069477)
          ·
            refine ⟨4148454413498359755200527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22125090205324585361069477 4148454413498359755200527)
            ·
              refine ⟨6222681620247539632800791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148454413498359755200527 6222681620247539632800791)
              ·
                refine ⟨9334022430371309449201187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6222681620247539632800791 9334022430371309449201187)
                ·
                  refine ⟨14001033645556964173801781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9334022430371309449201187 14001033645556964173801781)
                  ·
                    refine ⟨1312596904270965391293917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14001033645556964173801781 1312596904270965391293917)
                    ·
                      rfl

theorem cell22_3834410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3834410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834410 prefixEnd_3834410 := by exact prefixLift 3834410
  have htrace : WordTrace (prefixWord ++ tailWord_3834410) baseStart_3834410 baseEnd_3834410 := by
    simpa [prefixWord, tailWord_3834410, baseEnd_3834410] using wordTrace_append hprefix tailTrace_3834410
  have hstable : (prefixWord ++ tailWord_3834410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834410).length < 2 ^ (prefixWord ++ tailWord_3834410).sum := by decide
  have hdescent : baseEnd_3834410 < baseStart_3834410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834421 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3834421 : Nat := 118140960795 + 3834421 * 2 ^ 59
def prefixEnd_3834421 : Nat := 4983230072969 + 3 ^ 40 * 3834421 * 2
def baseEnd_3834421 : Nat := 1312600669795765029268883

theorem tailTrace_3834421 : CollatzResearch.WordTrace tailWord_3834421 prefixEnd_3834421 1312600669795765029268883 := by
  unfold tailWord_3834421
  simp only [CollatzResearch.WordTrace]
  refine ⟨139852823241555058815287117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93235215494370039210191411 139852823241555058815287117)
  ·
    refine ⟨52444808715583147055732669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139852823241555058815287117 52444808715583147055732669)
    ·
      refine ⟨19666803268343680145899751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52444808715583147055732669 19666803268343680145899751)
      ·
        refine ⟨29500204902515520218849627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19666803268343680145899751 29500204902515520218849627)
        ·
          refine ⟨44250307353773280328274441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29500204902515520218849627 44250307353773280328274441)
          ·
            refine ⟨33187730515329960246205831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44250307353773280328274441 33187730515329960246205831)
            ·
              refine ⟨49781595772994940369308747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33187730515329960246205831 49781595772994940369308747)
              ·
                refine ⟨74672393659492410553963121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49781595772994940369308747 74672393659492410553963121)
                ·
                  refine ⟨56004295244619307915472341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74672393659492410553963121 56004295244619307915472341)
                  ·
                    refine ⟨1312600669795765029268883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56004295244619307915472341 1312600669795765029268883)
                    ·
                      rfl

theorem cell22_3834421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3834421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834421 prefixEnd_3834421 := by exact prefixLift 3834421
  have htrace : WordTrace (prefixWord ++ tailWord_3834421) baseStart_3834421 baseEnd_3834421 := by
    simpa [prefixWord, tailWord_3834421, baseEnd_3834421] using wordTrace_append hprefix tailTrace_3834421
  have hstable : (prefixWord ++ tailWord_3834421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834421).length < 2 ^ (prefixWord ++ tailWord_3834421).sum := by decide
  have hdescent : baseEnd_3834421 < baseStart_3834421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834468 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 5]
def baseStart_3834468 : Nat := 118140960795 + 3834468 * 2 ^ 59
def prefixEnd_3834468 : Nat := 4983230072969 + 3 ^ 40 * 3834468 * 2
def baseEnd_3834468 : Nat := 437538919618757524447913

theorem tailTrace_3834468 : CollatzResearch.WordTrace tailWord_3834468 prefixEnd_3834468 437538919618757524447913 := by
  unfold tailWord_3834468
  simp only [CollatzResearch.WordTrace]
  refine ⟨69927268736192392921124029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93236358314923190561498705 69927268736192392921124029)
  ·
    refine ⟨26222725776072147345421511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69927268736192392921124029 26222725776072147345421511)
    ·
      refine ⟨39334088664108221018132267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26222725776072147345421511 39334088664108221018132267)
      ·
        refine ⟨59001132996162331527198401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39334088664108221018132267 59001132996162331527198401)
        ·
          refine ⟨44250849747121748645398801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59001132996162331527198401 44250849747121748645398801)
          ·
            refine ⟨33188137310341311484049101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44250849747121748645398801 33188137310341311484049101)
            ·
              refine ⟨12445551491377991806518413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33188137310341311484049101 12445551491377991806518413)
              ·
                refine ⟨4667081809266746927444405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12445551491377991806518413 4667081809266746927444405)
                ·
                  refine ⟨437538919618757524447913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667081809266746927444405 437538919618757524447913)
                  ·
                    rfl

theorem cell22_3834468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_3834468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834468 prefixEnd_3834468 := by exact prefixLift 3834468
  have htrace : WordTrace (prefixWord ++ tailWord_3834468) baseStart_3834468 baseEnd_3834468 := by
    simpa [prefixWord, tailWord_3834468, baseEnd_3834468] using wordTrace_append hprefix tailTrace_3834468
  have hstable : (prefixWord ++ tailWord_3834468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834468).length < 2 ^ (prefixWord ++ tailWord_3834468).sum := by decide
  have hdescent : baseEnd_3834468 < baseStart_3834468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834506 : List Nat := [3, 1, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_3834506 : Nat := 118140960795 + 3834506 * 2 ^ 59
def prefixEnd_3834506 : Nat := 4983230072969 + 3 ^ 40 * 3834506 * 2
def baseEnd_3834506 : Nat := 1312629767032853140893623

theorem tailTrace_3834506 : CollatzResearch.WordTrace tailWord_3834506 prefixEnd_3834506 1312629767032853140893623 := by
  unfold tailWord_3834506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34963980861561779583032843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93237282297498078888087581 34963980861561779583032843)
  ·
    refine ⟨52445971292342669374549265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34963980861561779583032843 52445971292342669374549265)
    ·
      refine ⟨39334478469257002030911949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52445971292342669374549265 39334478469257002030911949)
      ·
        refine ⟨14750429425971375761591981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39334478469257002030911949 14750429425971375761591981)
        ·
          refine ⟨5531411034739265910596993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14750429425971375761591981 5531411034739265910596993)
          ·
            refine ⟨4148558276054449432947745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5531411034739265910596993 4148558276054449432947745)
            ·
              refine ⟨3111418707040837074710809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4148558276054449432947745 3111418707040837074710809)
              ·
                refine ⟨2333564030280627806033107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111418707040837074710809 2333564030280627806033107)
                ·
                  refine ⟨3500346045420941709049661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333564030280627806033107 3500346045420941709049661)
                  ·
                    refine ⟨1312629767032853140893623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3500346045420941709049661 1312629767032853140893623)
                    ·
                      rfl

theorem cell22_3834506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_3834506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834506 prefixEnd_3834506 := by exact prefixLift 3834506
  have htrace : WordTrace (prefixWord ++ tailWord_3834506) baseStart_3834506 baseEnd_3834506 := by
    simpa [prefixWord, tailWord_3834506, baseEnd_3834506] using wordTrace_append hprefix tailTrace_3834506
  have hstable : (prefixWord ++ tailWord_3834506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834506).length < 2 ^ (prefixWord ++ tailWord_3834506).sum := by decide
  have hdescent : baseEnd_3834506 < baseStart_3834506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834543 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 1, 6]
def baseStart_3834543 : Nat := 118140960795 + 3834543 * 2 ^ 59
def prefixEnd_3834543 : Nat := 4983230072969 + 3 ^ 40 * 3834543 * 2
def baseEnd_3834543 : Nat := 1312642432888997377718509

theorem tailTrace_3834543 : CollatzResearch.WordTrace tailWord_3834543 prefixEnd_3834543 1312642432888997377718509 := by
  unfold tailWord_3834543
  simp only [CollatzResearch.WordTrace]
  refine ⟨139857272947113073651228283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93238181964742049100818855 139857272947113073651228283)
  ·
    refine ⟨209785909420669610476842425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139857272947113073651228283 209785909420669610476842425)
    ·
      refine ⟨157339432065502207857631819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209785909420669610476842425 157339432065502207857631819)
      ·
        refine ⟨236009148098253311786447729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157339432065502207857631819 236009148098253311786447729)
        ·
          refine ⟨177006861073689983839835797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236009148098253311786447729 177006861073689983839835797)
          ·
            refine ⟨8297196612829217992492303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177006861073689983839835797 8297196612829217992492303)
            ·
              refine ⟨12445794919243826988738455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297196612829217992492303 12445794919243826988738455)
              ·
                refine ⟨18668692378865740483107683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12445794919243826988738455 18668692378865740483107683)
                ·
                  refine ⟨28003038568298610724661525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18668692378865740483107683 28003038568298610724661525)
                  ·
                    refine ⟨1312642432888997377718509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28003038568298610724661525 1312642432888997377718509)
                    ·
                      rfl

theorem cell22_3834543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_3834543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834543 prefixEnd_3834543 := by exact prefixLift 3834543
  have htrace : WordTrace (prefixWord ++ tailWord_3834543) baseStart_3834543 baseEnd_3834543 := by
    simpa [prefixWord, tailWord_3834543, baseEnd_3834543] using wordTrace_append hprefix tailTrace_3834543
  have hstable : (prefixWord ++ tailWord_3834543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834543).length < 2 ^ (prefixWord ++ tailWord_3834543).sum := by decide
  have hdescent : baseEnd_3834543 < baseStart_3834543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834549 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3834549 : Nat := 118140960795 + 3834549 * 2 ^ 59
def prefixEnd_3834549 : Nat := 4983230072969 + 3 ^ 40 * 3834549 * 2
def baseEnd_3834549 : Nat := 1312644486811615362068491

theorem tailTrace_3834549 : CollatzResearch.WordTrace tailWord_3834549 prefixEnd_3834549 1312644486811615362068491 := by
  unfold tailWord_3834549
  simp only [CollatzResearch.WordTrace]
  refine ⟨139857491785091336675946701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93238327856727557783964467 139857491785091336675946701)
  ·
    refine ⟨52446559419409251253480013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139857491785091336675946701 52446559419409251253480013)
    ·
      refine ⟨19667459782278469220055005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52446559419409251253480013 19667459782278469220055005)
      ·
        refine ⟨7375297418354425957520627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19667459782278469220055005 7375297418354425957520627)
        ·
          refine ⟨11062946127531638936280941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375297418354425957520627 11062946127531638936280941)
          ·
            refine ⟨4148604797824364601105353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11062946127531638936280941 4148604797824364601105353)
            ·
              refine ⟨3111453598368273450829015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4148604797824364601105353 3111453598368273450829015)
              ·
                refine ⟨4667180397552410176243523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111453598368273450829015 4667180397552410176243523)
                ·
                  refine ⟨7000770596328615264365285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667180397552410176243523 7000770596328615264365285)
                  ·
                    refine ⟨1312644486811615362068491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000770596328615264365285 1312644486811615362068491)
                    ·
                      rfl

theorem cell22_3834549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3834549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834549 prefixEnd_3834549 := by exact prefixLift 3834549
  have htrace : WordTrace (prefixWord ++ tailWord_3834549) baseStart_3834549 baseEnd_3834549 := by
    simpa [prefixWord, tailWord_3834549, baseEnd_3834549] using wordTrace_append hprefix tailTrace_3834549
  have hstable : (prefixWord ++ tailWord_3834549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834549).length < 2 ^ (prefixWord ++ tailWord_3834549).sum := by decide
  have hdescent : baseEnd_3834549 < baseStart_3834549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834558 : List Nat := [4, 2, 1, 1, 2, 1, 11]
def baseStart_3834558 : Nat := 118140960795 + 3834558 * 2 ^ 59
def prefixEnd_3834558 : Nat := 4983230072969 + 3 ^ 40 * 3834558 * 2
def baseEnd_3834558 : Nat := 48616576581316382910869

theorem tailTrace_3834558 : CollatzResearch.WordTrace tailWord_3834558 prefixEnd_3834558 48616576581316382910869 := by
  unfold tailWord_3834558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17482227505257341401628041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93238546694705820808682885 17482227505257341401628041)
  ·
    refine ⟨13111670628943006051221031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17482227505257341401628041 13111670628943006051221031)
    ·
      refine ⟨19667505943414509076831547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13111670628943006051221031 19667505943414509076831547)
      ·
        refine ⟨29501258915121763615247321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19667505943414509076831547 29501258915121763615247321)
        ·
          refine ⟨22125944186341322711435491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29501258915121763615247321 22125944186341322711435491)
          ·
            refine ⟨33188916279511984067153237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22125944186341322711435491 33188916279511984067153237)
            ·
              refine ⟨48616576581316382910869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33188916279511984067153237 48616576581316382910869)
              ·
                rfl

theorem cell22_3834558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 11].length) (baseStart_3834558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834558 prefixEnd_3834558 := by exact prefixLift 3834558
  have htrace : WordTrace (prefixWord ++ tailWord_3834558) baseStart_3834558 baseEnd_3834558 := by
    simpa [prefixWord, tailWord_3834558, baseEnd_3834558] using wordTrace_append hprefix tailTrace_3834558
  have hstable : (prefixWord ++ tailWord_3834558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834558).length < 2 ^ (prefixWord ++ tailWord_3834558).sum := by decide
  have hdescent : baseEnd_3834558 < baseStart_3834558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834618 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_3834618 : Nat := 118140960795 + 3834618 * 2 ^ 59
def prefixEnd_3834618 : Nat := 4983230072969 + 3 ^ 40 * 3834618 * 2
def baseEnd_3834618 : Nat := 1312668106921722182093279

theorem tailTrace_3834618 : CollatzResearch.WordTrace tailWord_3834618 prefixEnd_3834618 1312668106921722182093279 := by
  unfold tailWord_3834618
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965002105460340365052127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93240005614560907640139005 34965002105460340365052127)
  ·
    refine ⟨52447503158190510547578191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34965002105460340365052127 52447503158190510547578191)
    ·
      refine ⟨78671254737285765821367287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52447503158190510547578191 78671254737285765821367287)
      ·
        refine ⟨118006882105928648732050931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78671254737285765821367287 118006882105928648732050931)
        ·
          refine ⟨177010323158892973098076397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118006882105928648732050931 177010323158892973098076397)
          ·
            refine ⟨66378871184584864911778649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177010323158892973098076397 66378871184584864911778649)
            ·
              refine ⟨49784153388438648683833987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66378871184584864911778649 49784153388438648683833987)
              ·
                refine ⟨74676230082657973025750981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49784153388438648683833987 74676230082657973025750981)
                ·
                  refine ⟨14001793140498369942328309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74676230082657973025750981 14001793140498369942328309)
                  ·
                    refine ⟨1312668106921722182093279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14001793140498369942328309 1312668106921722182093279)
                    ·
                      rfl

theorem cell22_3834618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_3834618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834618 prefixEnd_3834618 := by exact prefixLift 3834618
  have htrace : WordTrace (prefixWord ++ tailWord_3834618) baseStart_3834618 baseEnd_3834618 := by
    simpa [prefixWord, tailWord_3834618, baseEnd_3834618] using wordTrace_append hprefix tailTrace_3834618
  have hstable : (prefixWord ++ tailWord_3834618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834618).length < 2 ^ (prefixWord ++ tailWord_3834618).sum := by decide
  have hdescent : baseEnd_3834618 < baseStart_3834618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834648 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 8]
def baseStart_3834648 : Nat := 118140960795 + 3834648 * 2 ^ 59
def prefixEnd_3834648 : Nat := 4983230072969 + 3 ^ 40 * 3834648 * 2
def baseEnd_3834648 : Nat := 437559458844937367947729

theorem tailTrace_3834648 : CollatzResearch.WordTrace tailWord_3834648 prefixEnd_3834648 437559458844937367947729 := by
  unfold tailWord_3834648
  simp only [CollatzResearch.WordTrace]
  refine ⟨69930551305866338291900299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93240735074488451055867065 69930551305866338291900299)
  ·
    refine ⟨104895826958799507437850449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69930551305866338291900299 104895826958799507437850449)
    ·
      refine ⟨78671870219099630578387837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104895826958799507437850449 78671870219099630578387837)
      ·
        refine ⟨29501951332162361466895439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78671870219099630578387837 29501951332162361466895439)
        ·
          refine ⟨44252926998243542200343159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29501951332162361466895439 44252926998243542200343159)
          ·
            refine ⟨66379390497365313300514739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44252926998243542200343159 66379390497365313300514739)
            ·
              refine ⟨99569085746047969950772109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66379390497365313300514739 99569085746047969950772109)
              ·
                refine ⟨37338407154767988731539541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99569085746047969950772109 37338407154767988731539541)
                ·
                  refine ⟨437559458844937367947729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37338407154767988731539541 437559458844937367947729)
                  ·
                    rfl

theorem cell22_3834648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_3834648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834648 prefixEnd_3834648 := by exact prefixLift 3834648
  have htrace : WordTrace (prefixWord ++ tailWord_3834648) baseStart_3834648 baseEnd_3834648 := by
    simpa [prefixWord, tailWord_3834648, baseEnd_3834648] using wordTrace_append hprefix tailTrace_3834648
  have hstable : (prefixWord ++ tailWord_3834648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834648).length < 2 ^ (prefixWord ++ tailWord_3834648).sum := by decide
  have hdescent : baseEnd_3834648 < baseStart_3834648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834650 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_3834650 : Nat := 118140960795 + 3834650 * 2 ^ 59
def prefixEnd_3834650 : Nat := 4983230072969 + 3 ^ 40 * 3834650 * 2
def baseEnd_3834650 : Nat := 1312679061175684765293181

theorem tailTrace_3834650 : CollatzResearch.WordTrace tailWord_3834650 prefixEnd_3834650 1312679061175684765293181 := by
  unfold tailWord_3834650
  simp only [CollatzResearch.WordTrace]
  refine ⟨34965293889431357731343351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93240783705150287283582269 34965293889431357731343351)
  ·
    refine ⟨52447940834147036597015027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34965293889431357731343351 52447940834147036597015027)
    ·
      refine ⟨78671911251220554895522541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52447940834147036597015027 78671911251220554895522541)
      ·
        refine ⟨29501966719207708085820953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78671911251220554895522541 29501966719207708085820953)
        ·
          refine ⟨22126475039405781064365715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29501966719207708085820953 22126475039405781064365715)
          ·
            refine ⟨33189712559108671596548573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22126475039405781064365715 33189712559108671596548573)
            ·
              refine ⟨12446142209665751848705715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33189712559108671596548573 12446142209665751848705715)
              ·
                refine ⟨18669213314498627773058573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12446142209665751848705715 18669213314498627773058573)
                ·
                  refine ⟨7000954992936985414896965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18669213314498627773058573 7000954992936985414896965)
                  ·
                    refine ⟨1312679061175684765293181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7000954992936985414896965 1312679061175684765293181)
                    ·
                      rfl

theorem cell22_3834650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_3834650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834650 prefixEnd_3834650 := by exact prefixLift 3834650
  have htrace : WordTrace (prefixWord ++ tailWord_3834650) baseStart_3834650 baseEnd_3834650 := by
    simpa [prefixWord, tailWord_3834650, baseEnd_3834650] using wordTrace_append hprefix tailTrace_3834650
  have hstable : (prefixWord ++ tailWord_3834650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834650).length < 2 ^ (prefixWord ++ tailWord_3834650).sum := by decide
  have hdescent : baseEnd_3834650 < baseStart_3834650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834693 : List Nat := [1, 3, 1, 1, 1, 2, 2, 11]
def baseStart_3834693 : Nat := 118140960795 + 3834693 * 2 ^ 59
def prefixEnd_3834693 : Nat := 4983230072969 + 3 ^ 40 * 3834693 * 2
def baseEnd_3834693 : Nat := 145854864550494109607561

theorem tailTrace_3834693 : CollatzResearch.WordTrace tailWord_3834693 prefixEnd_3834693 145854864550494109607561 := by
  unfold tailWord_3834693
  simp only [CollatzResearch.WordTrace]
  refine ⟨139862743896569649269188733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93241829264379766179459155 139862743896569649269188733)
  ·
    refine ⟨52448528961213618475945775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139862743896569649269188733 52448528961213618475945775)
    ·
      refine ⟨78672793441820427713918663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52448528961213618475945775 78672793441820427713918663)
      ·
        refine ⟨118009190162730641570877995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78672793441820427713918663 118009190162730641570877995)
        ·
          refine ⟨177013785244095962356316993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118009190162730641570877995 177013785244095962356316993)
          ·
            refine ⟨132760338933071971767237745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177013785244095962356316993 132760338933071971767237745)
            ·
              refine ⟨99570254199803978825428309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132760338933071971767237745 99570254199803978825428309)
              ·
                refine ⟨145854864550494109607561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 99570254199803978825428309 145854864550494109607561)
                ·
                  rfl

theorem cell22_3834693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 11].length) (baseStart_3834693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834693 prefixEnd_3834693 := by exact prefixLift 3834693
  have htrace : WordTrace (prefixWord ++ tailWord_3834693) baseStart_3834693 baseEnd_3834693 := by
    simpa [prefixWord, tailWord_3834693, baseEnd_3834693] using wordTrace_append hprefix tailTrace_3834693
  have hstable : (prefixWord ++ tailWord_3834693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834693).length < 2 ^ (prefixWord ++ tailWord_3834693).sum := by decide
  have hdescent : baseEnd_3834693 < baseStart_3834693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834697 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 2, 3]
def baseStart_3834697 : Nat := 118140960795 + 3834697 * 2 ^ 59
def prefixEnd_3834697 : Nat := 4983230072969 + 3 ^ 40 * 3834697 * 2
def baseEnd_3834697 : Nat := 1312695150236192309368037

theorem tailTrace_3834697 : CollatzResearch.WordTrace tailWord_3834697 prefixEnd_3834697 1312695150236192309368037 := by
  unfold tailWord_3834697
  simp only [CollatzResearch.WordTrace]
  refine ⟨139862889788555157952334345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93241926525703438634889563 139862889788555157952334345)
  ·
    refine ⟨104897167341416368464250759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139862889788555157952334345 104897167341416368464250759)
    ·
      refine ⟨157345751012124552696376139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104897167341416368464250759 157345751012124552696376139)
      ·
        refine ⟨236018626518186829044564209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157345751012124552696376139 236018626518186829044564209)
        ·
          refine ⟨177013969888640121783423157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236018626518186829044564209 177013969888640121783423157)
          ·
            refine ⟨16595059677060011417195921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177013969888640121783423157 16595059677060011417195921)
            ·
              refine ⟨12446294757795008562896941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16595059677060011417195921 12446294757795008562896941)
              ·
                refine ⟨4667360534173128211086353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12446294757795008562896941 4667360534173128211086353)
                ·
                  refine ⟨3500520400629846158314765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667360534173128211086353 3500520400629846158314765)
                  ·
                    refine ⟨1312695150236192309368037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3500520400629846158314765 1312695150236192309368037)
                    ·
                      rfl

theorem cell22_3834697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_3834697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834697 prefixEnd_3834697 := by exact prefixLift 3834697
  have htrace : WordTrace (prefixWord ++ tailWord_3834697) baseStart_3834697 baseEnd_3834697 := by
    simpa [prefixWord, tailWord_3834697, baseEnd_3834697] using wordTrace_append hprefix tailTrace_3834697
  have hstable : (prefixWord ++ tailWord_3834697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834697).length < 2 ^ (prefixWord ++ tailWord_3834697).sum := by decide
  have hdescent : baseEnd_3834697 < baseStart_3834697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834836 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_3834836 : Nat := 118140960795 + 3834836 * 2 ^ 59
def prefixEnd_3834836 : Nat := 4983230072969 + 3 ^ 40 * 3834836 * 2
def baseEnd_3834836 : Nat := 1312742732776842280142611

theorem tailTrace_3834836 : CollatzResearch.WordTrace tailWord_3834836 prefixEnd_3834836 1312742732776842280142611 := by
  unfold tailWord_3834836
  simp only [CollatzResearch.WordTrace]
  refine ⟨69933979767525792345822181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93245306356701056461096241 69933979767525792345822181)
  ·
    refine ⟨13112621206411086064841659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69933979767525792345822181 13112621206411086064841659)
    ·
      refine ⟨19668931809616629097262489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13112621206411086064841659 19668931809616629097262489)
      ·
        refine ⟨14751698857212471822946867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19668931809616629097262489 14751698857212471822946867)
        ·
          refine ⟨22127548285818707734420301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14751698857212471822946867 22127548285818707734420301)
          ·
            refine ⟨8297830607182015400407613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22127548285818707734420301 8297830607182015400407613)
            ·
              refine ⟨3111686477693255775152855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8297830607182015400407613 3111686477693255775152855)
              ·
                refine ⟨4667529716539883662729283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111686477693255775152855 4667529716539883662729283)
                ·
                  refine ⟨7001294574809825494093925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667529716539883662729283 7001294574809825494093925)
                  ·
                    refine ⟨1312742732776842280142611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001294574809825494093925 1312742732776842280142611)
                    ·
                      rfl

theorem cell22_3834836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_3834836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834836 prefixEnd_3834836 := by exact prefixLift 3834836
  have htrace : WordTrace (prefixWord ++ tailWord_3834836) baseStart_3834836 baseEnd_3834836 := by
    simpa [prefixWord, tailWord_3834836, baseEnd_3834836] using wordTrace_append hprefix tailTrace_3834836
  have hstable : (prefixWord ++ tailWord_3834836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834836).length < 2 ^ (prefixWord ++ tailWord_3834836).sum := by decide
  have hdescent : baseEnd_3834836 < baseStart_3834836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834860 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_3834860 : Nat := 118140960795 + 3834860 * 2 ^ 59
def prefixEnd_3834860 : Nat := 4983230072969 + 3 ^ 40 * 3834860 * 2
def baseEnd_3834860 : Nat := 1312750948467314217542537

theorem tailTrace_3834860 : CollatzResearch.WordTrace tailWord_3834860 prefixEnd_3834860 1312750948467314217542537 := by
  unfold tailWord_3834860
  simp only [CollatzResearch.WordTrace]
  refine ⟨69934417443482318395259017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93245889924643091193678689 69934417443482318395259017)
  ·
    refine ⟨52450813082611738796444263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69934417443482318395259017 52450813082611738796444263)
    ·
      refine ⟨78676219623917608194666395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52450813082611738796444263 78676219623917608194666395)
      ·
        refine ⟨118014329435876412291999593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78676219623917608194666395 118014329435876412291999593)
        ·
          refine ⟨88510747076907309218999695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118014329435876412291999593 88510747076907309218999695)
          ·
            refine ⟨132766120615360963828499543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88510747076907309218999695 132766120615360963828499543)
            ·
              refine ⟨199149180923041445742749315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132766120615360963828499543 199149180923041445742749315)
              ·
                refine ⟨298723771384562168614123973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199149180923041445742749315 298723771384562168614123973)
                ·
                  refine ⟨56010707134605406615148245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298723771384562168614123973 56010707134605406615148245)
                  ·
                    refine ⟨1312750948467314217542537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56010707134605406615148245 1312750948467314217542537)
                    ·
                      rfl

theorem cell22_3834860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_3834860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834860 prefixEnd_3834860 := by exact prefixLift 3834860
  have htrace : WordTrace (prefixWord ++ tailWord_3834860) baseStart_3834860 baseEnd_3834860 := by
    simpa [prefixWord, tailWord_3834860, baseEnd_3834860] using wordTrace_append hprefix tailTrace_3834860
  have hstable : (prefixWord ++ tailWord_3834860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834860).length < 2 ^ (prefixWord ++ tailWord_3834860).sum := by decide
  have hdescent : baseEnd_3834860 < baseStart_3834860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834866 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_3834866 : Nat := 118140960795 + 3834866 * 2 ^ 59
def prefixEnd_3834866 : Nat := 4983230072969 + 3 ^ 40 * 3834866 * 2
def baseEnd_3834866 : Nat := 1312753002389932201892519

theorem tailTrace_3834866 : CollatzResearch.WordTrace tailWord_3834866 prefixEnd_3834866 1312753002389932201892519 := by
  unfold tailWord_3834866
  simp only [CollatzResearch.WordTrace]
  refine ⟨34967263431235724953809113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93246035816628599876824301 34967263431235724953809113)
  ·
    refine ⟨26225447573426793715356835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34967263431235724953809113 26225447573426793715356835)
    ·
      refine ⟨39338171360140190573035253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26225447573426793715356835 39338171360140190573035253)
      ·
        refine ⟨3687953565013142866222055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39338171360140190573035253 3687953565013142866222055)
        ·
          refine ⟨5531930347519714299333083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687953565013142866222055 5531930347519714299333083)
          ·
            refine ⟨8297895521279571448999625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531930347519714299333083 8297895521279571448999625)
            ·
              refine ⟨6223421640959678586749719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8297895521279571448999625 6223421640959678586749719)
              ·
                refine ⟨9335132461439517880124579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223421640959678586749719 9335132461439517880124579)
                ·
                  refine ⟨14002698692159276820186869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9335132461439517880124579 14002698692159276820186869)
                  ·
                    refine ⟨1312753002389932201892519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14002698692159276820186869 1312753002389932201892519)
                    ·
                      rfl

theorem cell22_3834866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_3834866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834866 prefixEnd_3834866 := by exact prefixLift 3834866
  have htrace : WordTrace (prefixWord ++ tailWord_3834866) baseStart_3834866 baseEnd_3834866 := by
    simpa [prefixWord, tailWord_3834866, baseEnd_3834866] using wordTrace_append hprefix tailTrace_3834866
  have hstable : (prefixWord ++ tailWord_3834866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834866).length < 2 ^ (prefixWord ++ tailWord_3834866).sum := by decide
  have hdescent : baseEnd_3834866 < baseStart_3834866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834875 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 4, 6]
def baseStart_3834875 : Nat := 118140960795 + 3834875 * 2 ^ 59
def prefixEnd_3834875 : Nat := 4983230072969 + 3 ^ 40 * 3834875 * 2
def baseEnd_3834875 : Nat := 1312756083273859178417491

theorem tailTrace_3834875 : CollatzResearch.WordTrace tailWord_3834875 prefixEnd_3834875 1312756083273859178417491 := by
  unfold tailWord_3834875
  simp only [CollatzResearch.WordTrace]
  refine ⟨139869381981910294352314079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93246254654606862901542719 139869381981910294352314079)
  ·
    refine ⟨209804072972865441528471119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139869381981910294352314079 209804072972865441528471119)
    ·
      refine ⟨314706109459298162292706679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209804072972865441528471119 314706109459298162292706679)
      ·
        refine ⟨472059164188947243439060019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314706109459298162292706679 472059164188947243439060019)
        ·
          refine ⟨708088746283420865158590029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472059164188947243439060019 708088746283420865158590029)
          ·
            refine ⟨265533279856282824434471261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708088746283420865158590029 265533279856282824434471261)
            ·
              refine ⟨99574979946106059162926723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265533279856282824434471261 99574979946106059162926723)
              ·
                refine ⟨149362469919159088744390085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99574979946106059162926723 149362469919159088744390085)
                ·
                  refine ⟨28005463109842329139573141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149362469919159088744390085 28005463109842329139573141)
                  ·
                    refine ⟨1312756083273859178417491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28005463109842329139573141 1312756083273859178417491)
                    ·
                      rfl

theorem cell22_3834875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_3834875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834875 prefixEnd_3834875 := by exact prefixLift 3834875
  have htrace : WordTrace (prefixWord ++ tailWord_3834875) baseStart_3834875 baseEnd_3834875 := by
    simpa [prefixWord, tailWord_3834875, baseEnd_3834875] using wordTrace_append hprefix tailTrace_3834875
  have hstable : (prefixWord ++ tailWord_3834875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834875).length < 2 ^ (prefixWord ++ tailWord_3834875).sum := by decide
  have hdescent : baseEnd_3834875 < baseStart_3834875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834911 : List Nat := [1, 1, 2, 4, 1, 3, 2, 4, 1, 3]
def baseStart_3834911 : Nat := 118140960795 + 3834911 * 2 ^ 59
def prefixEnd_3834911 : Nat := 4983230072969 + 3 ^ 40 * 3834911 * 2
def baseEnd_3834911 : Nat := 1312768406809567084517381

theorem tailTrace_3834911 : CollatzResearch.WordTrace tailWord_3834911 prefixEnd_3834911 1312768406809567084517381 := by
  unfold tailWord_3834911
  simp only [CollatzResearch.WordTrace]
  refine ⟨139870695009779872500624587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93247130006519915000416391 139870695009779872500624587)
  ·
    refine ⟨209806042514669808750936881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139870695009779872500624587 209806042514669808750936881)
    ·
      refine ⟨157354531886002356563202661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209806042514669808750936881 157354531886002356563202661)
      ·
        refine ⟨29503974728625441855600499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157354531886002356563202661 29503974728625441855600499)
        ·
          refine ⟨44255962092938162783400749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29503974728625441855600499 44255962092938162783400749)
          ·
            refine ⟨16595985784851811043775281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44255962092938162783400749 16595985784851811043775281)
            ·
              refine ⟨12446989338638858282831461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16595985784851811043775281 12446989338638858282831461)
              ·
                refine ⟨2333810500994785928030899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12446989338638858282831461 2333810500994785928030899)
                ·
                  refine ⟨3500715751492178892046349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333810500994785928030899 3500715751492178892046349)
                  ·
                    refine ⟨1312768406809567084517381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3500715751492178892046349 1312768406809567084517381)
                    ·
                      rfl

theorem cell22_3834911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 3].length) (baseStart_3834911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834911 prefixEnd_3834911 := by exact prefixLift 3834911
  have htrace : WordTrace (prefixWord ++ tailWord_3834911) baseStart_3834911 baseEnd_3834911 := by
    simpa [prefixWord, tailWord_3834911, baseEnd_3834911] using wordTrace_append hprefix tailTrace_3834911
  have hstable : (prefixWord ++ tailWord_3834911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834911).length < 2 ^ (prefixWord ++ tailWord_3834911).sum := by decide
  have hdescent : baseEnd_3834911 < baseStart_3834911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834924 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 5]
def baseStart_3834924 : Nat := 118140960795 + 3834924 * 2 ^ 59
def prefixEnd_3834924 : Nat := 4983230072969 + 3 ^ 40 * 3834924 * 2
def baseEnd_3834924 : Nat := 437590952325079794647447

theorem tailTrace_3834924 : CollatzResearch.WordTrace tailWord_3834924 prefixEnd_3834924 437590952325079794647447 := by
  unfold tailWord_3834924
  simp only [CollatzResearch.WordTrace]
  refine ⟨69935584579366387860423913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93247446105821850480565217 69935584579366387860423913)
  ·
    refine ⟨52451688434524790895317935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69935584579366387860423913 52451688434524790895317935)
    ·
      refine ⟨78677532651787186342976903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52451688434524790895317935 78677532651787186342976903)
      ·
        refine ⟨118016298977680779514465355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78677532651787186342976903 118016298977680779514465355)
        ·
          refine ⟨177024448466521169271698033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118016298977680779514465355 177024448466521169271698033)
          ·
            refine ⟨132768336349890876953773525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177024448466521169271698033 132768336349890876953773525)
            ·
              refine ⟨3111757883200567428604067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132768336349890876953773525 3111757883200567428604067)
              ·
                refine ⟨4667636824800851142906101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111757883200567428604067 4667636824800851142906101)
                ·
                  refine ⟨437590952325079794647447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4667636824800851142906101 437590952325079794647447)
                  ·
                    rfl

theorem cell22_3834924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_3834924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834924 prefixEnd_3834924 := by exact prefixLift 3834924
  have htrace : WordTrace (prefixWord ++ tailWord_3834924) baseStart_3834924 baseEnd_3834924 := by
    simpa [prefixWord, tailWord_3834924, baseEnd_3834924] using wordTrace_append hprefix tailTrace_3834924
  have hstable : (prefixWord ++ tailWord_3834924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834924).length < 2 ^ (prefixWord ++ tailWord_3834924).sum := by decide
  have hdescent : baseEnd_3834924 < baseStart_3834924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834945 : List Nat := [1, 2, 5, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3834945 : Nat := 118140960795 + 3834945 * 2 ^ 59
def prefixEnd_3834945 : Nat := 4983230072969 + 3 ^ 40 * 3834945 * 2
def baseEnd_3834945 : Nat := 1312780045704402329167277

theorem tailTrace_3834945 : CollatzResearch.WordTrace tailWord_3834945 prefixEnd_3834945 1312780045704402329167277 := by
  unfold tailWord_3834945
  simp only [CollatzResearch.WordTrace]
  refine ⟨139871935091656696307362289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93247956727771130871574859 139871935091656696307362289)
  ·
    refine ⟨104903951318742522230521717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139871935091656696307362289 104903951318742522230521717)
    ·
      refine ⟨9834745436132111459111411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104903951318742522230521717 9834745436132111459111411)
      ·
        refine ⟨14752118154198167188667117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9834745436132111459111411 14752118154198167188667117)
        ·
          refine ⟨5532044307824312695750169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14752118154198167188667117 5532044307824312695750169)
          ·
            refine ⟨4149033230868234521812627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5532044307824312695750169 4149033230868234521812627)
            ·
              refine ⟨6223549846302351782718941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149033230868234521812627 6223549846302351782718941)
              ·
                refine ⟨2333831192363381918519603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6223549846302351782718941 2333831192363381918519603)
                ·
                  refine ⟨3500746788545072877779405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333831192363381918519603 3500746788545072877779405)
                  ·
                    refine ⟨1312780045704402329167277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3500746788545072877779405 1312780045704402329167277)
                    ·
                      rfl

theorem cell22_3834945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3834945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834945 prefixEnd_3834945 := by exact prefixLift 3834945
  have htrace : WordTrace (prefixWord ++ tailWord_3834945) baseStart_3834945 baseEnd_3834945 := by
    simpa [prefixWord, tailWord_3834945, baseEnd_3834945] using wordTrace_append hprefix tailTrace_3834945
  have hstable : (prefixWord ++ tailWord_3834945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834945).length < 2 ^ (prefixWord ++ tailWord_3834945).sum := by decide
  have hdescent : baseEnd_3834945 < baseStart_3834945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834954 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_3834954 : Nat := 118140960795 + 3834954 * 2 ^ 59
def prefixEnd_3834954 : Nat := 4983230072969 + 3 ^ 40 * 3834954 * 2
def baseEnd_3834954 : Nat := 1312783126588329305692249

theorem tailTrace_3834954 : CollatzResearch.WordTrace tailWord_3834954 prefixEnd_3834954 1312783126588329305692249 := by
  unfold tailWord_3834954
  simp only [CollatzResearch.WordTrace]
  refine ⟨34968065837156022711109979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93248175565749393896293277 34968065837156022711109979)
  ·
    refine ⟨52452098755734034066664969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34968065837156022711109979 52452098755734034066664969)
    ·
      refine ⟨39339074066800525549998727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52452098755734034066664969 39339074066800525549998727)
      ·
        refine ⟨59008611100200788324998091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39339074066800525549998727 59008611100200788324998091)
        ·
          refine ⟨88512916650301182487497137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59008611100200788324998091 88512916650301182487497137)
          ·
            refine ⟨66384687487725886865622853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88512916650301182487497137 66384687487725886865622853)
            ·
              refine ⟨12447128903948603787304285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66384687487725886865622853 12447128903948603787304285)
              ·
                refine ⟨4667673338980726420239107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12447128903948603787304285 4667673338980726420239107)
                ·
                  refine ⟨7001510008471089630358661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667673338980726420239107 7001510008471089630358661)
                  ·
                    refine ⟨1312783126588329305692249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001510008471089630358661 1312783126588329305692249)
                    ·
                      rfl

theorem cell22_3834954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_3834954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834954 prefixEnd_3834954 := by exact prefixLift 3834954
  have htrace : WordTrace (prefixWord ++ tailWord_3834954) baseStart_3834954 baseEnd_3834954 := by
    simpa [prefixWord, tailWord_3834954, baseEnd_3834954] using wordTrace_append hprefix tailTrace_3834954
  have hstable : (prefixWord ++ tailWord_3834954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834954).length < 2 ^ (prefixWord ++ tailWord_3834954).sum := by decide
  have hdescent : baseEnd_3834954 < baseStart_3834954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3834999 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 2, 4]
def baseStart_3834999 : Nat := 118140960795 + 3834999 * 2 ^ 59
def prefixEnd_3834999 : Nat := 4983230072969 + 3 ^ 40 * 3834999 * 2
def baseEnd_3834999 : Nat := 1312798531007964188317111

theorem tailTrace_3834999 : CollatzResearch.WordTrace tailWord_3834999 prefixEnd_3834999 1312798531007964188317111 := by
  unfold tailWord_3834999
  simp only [CollatzResearch.WordTrace]
  refine ⟨139873904633461063529828051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93249269755640709019885367 139873904633461063529828051)
  ·
    refine ⟨209810856950191595294742077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139873904633461063529828051 209810856950191595294742077)
    ·
      refine ⟨78679071356321848235528279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209810856950191595294742077 78679071356321848235528279)
      ·
        refine ⟨118018607034482772353292419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78679071356321848235528279 118018607034482772353292419)
        ·
          refine ⟨177027910551724158529938629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118018607034482772353292419 177027910551724158529938629)
          ·
            refine ⟨33192733228448279724363493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177027910551724158529938629 33192733228448279724363493)
            ·
              refine ⟨6223637480334052448318155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33192733228448279724363493 6223637480334052448318155)
              ·
                refine ⟨9335456220501078672477233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223637480334052448318155 9335456220501078672477233)
                ·
                  refine ⟨7001592165375809004357925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9335456220501078672477233 7001592165375809004357925)
                  ·
                    refine ⟨1312798531007964188317111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001592165375809004357925 1312798531007964188317111)
                    ·
                      rfl

theorem cell22_3834999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_3834999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3834999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3834999 prefixEnd_3834999 := by exact prefixLift 3834999
  have htrace : WordTrace (prefixWord ++ tailWord_3834999) baseStart_3834999 baseEnd_3834999 := by
    simpa [prefixWord, tailWord_3834999, baseEnd_3834999] using wordTrace_append hprefix tailTrace_3834999
  have hstable : (prefixWord ++ tailWord_3834999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3834999).length < 2 ^ (prefixWord ++ tailWord_3834999).sum := by decide
  have hdescent : baseEnd_3834999 < baseStart_3834999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3834999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
