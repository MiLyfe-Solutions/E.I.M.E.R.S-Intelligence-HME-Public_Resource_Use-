import V185TrunkScan23Chunk1092

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6471260 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 6]
def baseStart_6471260 : Nat := 118140960795 + 6471260 * 2 ^ 59
def prefixEnd_6471260 : Nat := 4983230072969 + 3 ^ 40 * 6471260 * 2
def baseEnd_6471260 : Nat := 369207424468272933243247

theorem tailTrace_6471260 : CollatzResearch.WordTrace tailWord_6471260 prefixEnd_6471260 369207424468272933243247 := by
  unfold tailWord_6471260
  simp only [CollatzResearch.WordTrace]
  refine ⟨118013121267868849031693617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157350828357158465375591489 118013121267868849031693617)
  ·
    refine ⟨88509840950901636773770213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118013121267868849031693617 88509840950901636773770213)
    ·
      refine ⟨16595595178294056895081915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88509840950901636773770213 16595595178294056895081915)
      ·
        refine ⟨24893392767441085342622873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16595595178294056895081915 24893392767441085342622873)
        ·
          refine ⟨18670044575580814006967155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24893392767441085342622873 18670044575580814006967155)
          ·
            refine ⟨28005066863371221010450733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18670044575580814006967155 28005066863371221010450733)
            ·
              refine ⟨10501900073764207878919025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28005066863371221010450733 10501900073764207878919025)
              ·
                refine ⟨7876425055323155909189269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10501900073764207878919025 7876425055323155909189269)
                ·
                  refine ⟨369207424468272933243247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7876425055323155909189269 369207424468272933243247)
                  ·
                    rfl

theorem cell23_6471260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_6471260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471260 prefixEnd_6471260 := by exact prefixLift 6471260
  have htrace : WordTrace (prefixWord ++ tailWord_6471260) baseStart_6471260 baseEnd_6471260 := by
    simpa [prefixWord, tailWord_6471260, baseEnd_6471260] using wordTrace_append hprefix tailTrace_6471260
  have hstable : (prefixWord ++ tailWord_6471260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471260).length < 2 ^ (prefixWord ++ tailWord_6471260).sum := by decide
  have hdescent : baseEnd_6471260 < baseStart_6471260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471277 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 6]
def baseStart_6471277 : Nat := 118140960795 + 6471277 * 2 ^ 59
def prefixEnd_6471277 : Nat := 4983230072969 + 3 ^ 40 * 6471277 * 2
def baseEnd_6471277 : Nat := 369208394376175870297405

theorem tailTrace_6471277 : CollatzResearch.WordTrace tailWord_6471277 prefixEnd_6471277 369208394376175870297405 := by
  unfold tailWord_6471277
  simp only [CollatzResearch.WordTrace]
  refine ⟨236026862576676109966756085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157351241717784073311170723 236026862576676109966756085)
  ·
    refine ⟨22127518366563385309383383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236026862576676109966756085 22127518366563385309383383)
    ·
      refine ⟨33191277549845077964075075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22127518366563385309383383 33191277549845077964075075)
      ·
        refine ⟨49786916324767616946112613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33191277549845077964075075 49786916324767616946112613)
        ·
          refine ⟨9335046810893928177396115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49786916324767616946112613 9335046810893928177396115)
          ·
            refine ⟨14002570216340892266094173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9335046810893928177396115 14002570216340892266094173)
            ·
              refine ⟨5250963831127834599785315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14002570216340892266094173 5250963831127834599785315)
              ·
                refine ⟨7876445746691751899677973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250963831127834599785315 7876445746691751899677973)
                ·
                  refine ⟨369208394376175870297405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7876445746691751899677973 369208394376175870297405)
                  ·
                    rfl

theorem cell23_6471277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_6471277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471277 prefixEnd_6471277 := by exact prefixLift 6471277
  have htrace : WordTrace (prefixWord ++ tailWord_6471277) baseStart_6471277 baseEnd_6471277 := by
    simpa [prefixWord, tailWord_6471277, baseEnd_6471277] using wordTrace_append hprefix tailTrace_6471277
  have hstable : (prefixWord ++ tailWord_6471277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471277).length < 2 ^ (prefixWord ++ tailWord_6471277).sum := by decide
  have hdescent : baseEnd_6471277 < baseStart_6471277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471280 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 1, 5, 2]
def baseStart_6471280 : Nat := 118140960795 + 6471280 * 2 ^ 59
def prefixEnd_6471280 : Nat := 4983230072969 + 3 ^ 40 * 6471280 * 2
def baseEnd_6471280 : Nat := 3322877089827546320939131

theorem tailTrace_6471280 : CollatzResearch.WordTrace tailWord_6471280 prefixEnd_6471280 3322877089827546320939131 := by
  unfold tailWord_6471280
  simp only [CollatzResearch.WordTrace]
  refine ⟨118013485997832620739557647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157351314663776827652743529 118013485997832620739557647)
  ·
    refine ⟨177020228996748931109336471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118013485997832620739557647 177020228996748931109336471)
    ·
      refine ⟨265530343495123396664004707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177020228996748931109336471 265530343495123396664004707)
      ·
        refine ⟨398295515242685094996007061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265530343495123396664004707 398295515242685094996007061)
        ·
          refine ⟨18670102277000863827937831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 398295515242685094996007061 18670102277000863827937831)
          ·
            refine ⟨28005153415501295741906747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18670102277000863827937831 28005153415501295741906747)
            ·
              refine ⟨42007730123251943612860121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28005153415501295741906747 42007730123251943612860121)
              ·
                refine ⟨31505797592438957709645091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42007730123251943612860121 31505797592438957709645091)
                ·
                  refine ⟨47258696388658436564467637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31505797592438957709645091 47258696388658436564467637)
                  ·
                    refine ⟨4430502786436728427918841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47258696388658436564467637 4430502786436728427918841)
                    ·
                      refine ⟨3322877089827546320939131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430502786436728427918841 3322877089827546320939131)
                      ·
                        rfl

theorem cell23_6471280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 5, 2].length) (baseStart_6471280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471280 prefixEnd_6471280 := by exact prefixLift 6471280
  have htrace : WordTrace (prefixWord ++ tailWord_6471280) baseStart_6471280 baseEnd_6471280 := by
    simpa [prefixWord, tailWord_6471280, baseEnd_6471280] using wordTrace_append hprefix tailTrace_6471280
  have hstable : (prefixWord ++ tailWord_6471280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471280).length < 2 ^ (prefixWord ++ tailWord_6471280).sum := by decide
  have hdescent : baseEnd_6471280 < baseStart_6471280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471314 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_6471314 : Nat := 118140960795 + 6471314 * 2 ^ 59
def prefixEnd_6471314 : Nat := 4983230072969 + 3 ^ 40 * 6471314 * 2
def baseEnd_6471314 : Nat := 3322894548169799187913975

theorem tailTrace_6471314 : CollatzResearch.WordTrace tailWord_6471314 prefixEnd_6471314 3322894548169799187913975 := by
  unfold tailWord_6471314
  simp only [CollatzResearch.WordTrace]
  refine ⟨59007053019385516321463249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157352141385028043523901997 59007053019385516321463249)
  ·
    refine ⟨44255289764539137241097437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59007053019385516321463249 44255289764539137241097437)
    ·
      refine ⟨16595733661702176465411539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44255289764539137241097437 16595733661702176465411539)
      ·
        refine ⟨24893600492553264698117309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16595733661702176465411539 24893600492553264698117309)
        ·
          refine ⟨9335100184707474261793991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24893600492553264698117309 9335100184707474261793991)
          ·
            refine ⟨14002650277061211392690987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9335100184707474261793991 14002650277061211392690987)
            ·
              refine ⟨21003975415591817089036481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14002650277061211392690987 21003975415591817089036481)
              ·
                refine ⟨15752981561693862816777361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21003975415591817089036481 15752981561693862816777361)
                ·
                  refine ⟨11814736171270397112583021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15752981561693862816777361 11814736171270397112583021)
                  ·
                    refine ⟨4430526064226398917218633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11814736171270397112583021 4430526064226398917218633)
                    ·
                      refine ⟨3322894548169799187913975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430526064226398917218633 3322894548169799187913975)
                      ·
                        rfl

theorem cell23_6471314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_6471314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471314 prefixEnd_6471314 := by exact prefixLift 6471314
  have htrace : WordTrace (prefixWord ++ tailWord_6471314) baseStart_6471314 baseEnd_6471314 := by
    simpa [prefixWord, tailWord_6471314, baseEnd_6471314] using wordTrace_append hprefix tailTrace_6471314
  have hstable : (prefixWord ++ tailWord_6471314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471314).length < 2 ^ (prefixWord ++ tailWord_6471314).sum := by decide
  have hdescent : baseEnd_6471314 < baseStart_6471314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471320 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 4, 4]
def baseStart_6471320 : Nat := 118140960795 + 6471320 * 2 ^ 59
def prefixEnd_6471320 : Nat := 4983230072969 + 3 ^ 40 * 6471320 * 2
def baseEnd_6471320 : Nat := 1107632543017908721479649

theorem tailTrace_6471320 : CollatzResearch.WordTrace tailWord_6471320 prefixEnd_6471320 1107632543017908721479649 := by
  unfold tailWord_6471320
  simp only [CollatzResearch.WordTrace]
  refine ⟨118014215457760164155285707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157352287277013552207047609 118014215457760164155285707)
  ·
    refine ⟨177021323186640246232928561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118014215457760164155285707 177021323186640246232928561)
    ·
      refine ⟨132765992389980184674696421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177021323186640246232928561 132765992389980184674696421)
      ·
        refine ⟨24893623573121284626505579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132765992389980184674696421 24893623573121284626505579)
        ·
          refine ⟨37340435359681926939758369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24893623573121284626505579 37340435359681926939758369)
          ·
            refine ⟨28005326519761445204818777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37340435359681926939758369 28005326519761445204818777)
            ·
              refine ⟨21003994889821083903614083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28005326519761445204818777 21003994889821083903614083)
              ·
                refine ⟨31505992334731625855421125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21003994889821083903614083 31505992334731625855421125)
                ·
                  refine ⟨5907373562762179847891461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31505992334731625855421125 5907373562762179847891461)
                  ·
                    refine ⟨1107632543017908721479649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5907373562762179847891461 1107632543017908721479649)
                    ·
                      rfl

theorem cell23_6471320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_6471320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471320 prefixEnd_6471320 := by exact prefixLift 6471320
  have htrace : WordTrace (prefixWord ++ tailWord_6471320) baseStart_6471320 baseEnd_6471320 := by
    simpa [prefixWord, tailWord_6471320, baseEnd_6471320] using wordTrace_append hprefix tailTrace_6471320
  have hstable : (prefixWord ++ tailWord_6471320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471320).length < 2 ^ (prefixWord ++ tailWord_6471320).sum := by decide
  have hdescent : baseEnd_6471320 < baseStart_6471320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471360 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 3]
def baseStart_6471360 : Nat := 118140960795 + 6471360 * 2 ^ 59
def prefixEnd_6471360 : Nat := 4983230072969 + 3 ^ 40 * 6471360 * 2
def baseEnd_6471360 : Nat := 3322918168279906007938763

theorem tailTrace_6471360 : CollatzResearch.WordTrace tailWord_6471360 prefixEnd_6471360 3322918168279906007938763 := by
  unfold tailWord_6471360
  simp only [CollatzResearch.WordTrace]
  refine ⟨118014944917687707571013767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157353259890250276761351689 118014944917687707571013767)
  ·
    refine ⟨177022417376531561356520651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118014944917687707571013767 177022417376531561356520651)
    ·
      refine ⟨265533626064797342034780977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177022417376531561356520651 265533626064797342034780977)
      ·
        refine ⟨199150219548598006526085733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265533626064797342034780977 199150219548598006526085733)
        ·
          refine ⟨37340666165362126223641075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199150219548598006526085733 37340666165362126223641075)
          ·
            refine ⟨56010999248043189335461613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37340666165362126223641075 56010999248043189335461613)
            ·
              refine ⟨21004124718016196000798105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56010999248043189335461613 21004124718016196000798105)
              ·
                refine ⟨15753093538512147000598579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21004124718016196000798105 15753093538512147000598579)
                ·
                  refine ⟨23629640307768220500897869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15753093538512147000598579 23629640307768220500897869)
                  ·
                    refine ⟨8861115115413082687836701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23629640307768220500897869 8861115115413082687836701)
                    ·
                      refine ⟨3322918168279906007938763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8861115115413082687836701 3322918168279906007938763)
                      ·
                        rfl

theorem cell23_6471360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_6471360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471360 prefixEnd_6471360 := by exact prefixLift 6471360
  have htrace : WordTrace (prefixWord ++ tailWord_6471360) baseStart_6471360 baseEnd_6471360 := by
    simpa [prefixWord, tailWord_6471360, baseEnd_6471360] using wordTrace_append hprefix tailTrace_6471360
  have hstable : (prefixWord ++ tailWord_6471360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471360).length < 2 ^ (prefixWord ++ tailWord_6471360).sum := by decide
  have hdescent : baseEnd_6471360 < baseStart_6471360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471364 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_6471364 : Nat := 118140960795 + 6471364 * 2 ^ 59
def prefixEnd_6471364 : Nat := 4983230072969 + 3 ^ 40 * 6471364 * 2
def baseEnd_6471364 : Nat := 3322920222202523992288745

theorem tailTrace_6471364 : CollatzResearch.WordTrace tailWord_6471364 prefixEnd_6471364 3322920222202523992288745 := by
  unfold tailWord_6471364
  simp only [CollatzResearch.WordTrace]
  refine ⟨118015017863680461912586573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157353357151573949216782097 118015017863680461912586573)
  ·
    refine ⟨44255631698880173217219965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118015017863680461912586573 44255631698880173217219965)
    ·
      refine ⟨16595861887080064956457487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44255631698880173217219965 16595861887080064956457487)
      ·
        refine ⟨24893792830620097434686231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16595861887080064956457487 24893792830620097434686231)
        ·
          refine ⟨37340689245930146152029347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24893792830620097434686231 37340689245930146152029347)
          ·
            refine ⟨56011033868895219228044021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37340689245930146152029347 56011033868895219228044021)
            ·
              refine ⟨5251034425208926802629127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56011033868895219228044021 5251034425208926802629127)
              ·
                refine ⟨7876551637813390203943691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251034425208926802629127 7876551637813390203943691)
                ·
                  refine ⟨11814827456720085305915537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7876551637813390203943691 11814827456720085305915537)
                  ·
                    refine ⟨8861120592540063979436653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11814827456720085305915537 8861120592540063979436653)
                    ·
                      refine ⟨3322920222202523992288745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8861120592540063979436653 3322920222202523992288745)
                      ·
                        rfl

theorem cell23_6471364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_6471364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471364 prefixEnd_6471364 := by exact prefixLift 6471364
  have htrace : WordTrace (prefixWord ++ tailWord_6471364) baseStart_6471364 baseEnd_6471364 := by
    simpa [prefixWord, tailWord_6471364, baseEnd_6471364] using wordTrace_append hprefix tailTrace_6471364
  have hstable : (prefixWord ++ tailWord_6471364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471364).length < 2 ^ (prefixWord ++ tailWord_6471364).sum := by decide
  have hdescent : baseEnd_6471364 < baseStart_6471364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471377 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_6471377 : Nat := 118140960795 + 6471377 * 2 ^ 59
def prefixEnd_6471377 : Nat := 4983230072969 + 3 ^ 40 * 6471377 * 2
def baseEnd_6471377 : Nat := 3322926897451032441426185

theorem tailTrace_6471377 : CollatzResearch.WordTrace tailWord_6471377 prefixEnd_6471377 3322926897451032441426185 := by
  unfold tailWord_6471377
  simp only [CollatzResearch.WordTrace]
  refine ⟨236030509876313827045396385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157353673250875884696930923 236030509876313827045396385)
  ·
    refine ⟨177022882407235370284047289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236030509876313827045396385 177022882407235370284047289)
    ·
      refine ⟨132767161805426527713035467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177022882407235370284047289 132767161805426527713035467)
      ·
        refine ⟨199150742708139791569553201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132767161805426527713035467 199150742708139791569553201)
        ·
          refine ⟨149363057031104843677164901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199150742708139791569553201 149363057031104843677164901)
          ·
            refine ⟨28005573193332158189468419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149363057031104843677164901 28005573193332158189468419)
            ·
              refine ⟨42008359789998237284202629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28005573193332158189468419 42008359789998237284202629)
              ·
                refine ⟨7876567460624669490787993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42008359789998237284202629 7876567460624669490787993)
                ·
                  refine ⟨5907425595468502118090995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7876567460624669490787993 5907425595468502118090995)
                  ·
                    refine ⟨8861138393202753177136493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5907425595468502118090995 8861138393202753177136493)
                    ·
                      refine ⟨3322926897451032441426185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8861138393202753177136493 3322926897451032441426185)
                      ·
                        rfl

theorem cell23_6471377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_6471377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471377 prefixEnd_6471377 := by exact prefixLift 6471377
  have htrace : WordTrace (prefixWord ++ tailWord_6471377) baseStart_6471377 baseEnd_6471377 := by
    simpa [prefixWord, tailWord_6471377, baseEnd_6471377] using wordTrace_append hprefix tailTrace_6471377
  have hstable : (prefixWord ++ tailWord_6471377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471377).length < 2 ^ (prefixWord ++ tailWord_6471377).sum := by decide
  have hdescent : baseEnd_6471377 < baseStart_6471377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471378 : List Nat := [3, 2, 2, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_6471378 : Nat := 118140960795 + 6471378 * 2 ^ 59
def prefixEnd_6471378 : Nat := 4983230072969 + 3 ^ 40 * 6471378 * 2
def baseEnd_6471378 : Nat := 3322927410931686937513681

theorem tailTrace_6471378 : CollatzResearch.WordTrace tailWord_6471378 prefixEnd_6471378 3322927410931686937513681 := by
  unfold tailWord_6471378
  simp only [CollatzResearch.WordTrace]
  refine ⟨59007636587327551054045697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157353697566206802810788525 59007636587327551054045697)
  ·
    refine ⟨44255727440495663290534273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59007636587327551054045697 44255727440495663290534273)
    ·
      refine ⟨33191795580371747467900705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44255727440495663290534273 33191795580371747467900705)
      ·
        refine ⟨24893846685278810600925529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33191795580371747467900705 24893846685278810600925529)
        ·
          refine ⟨18670385013959107950694147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24893846685278810600925529 18670385013959107950694147)
          ·
            refine ⟨28005577520938661926041221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18670385013959107950694147 28005577520938661926041221)
            ·
              refine ⟨5251045785175999111132729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28005577520938661926041221 5251045785175999111132729)
              ·
                refine ⟨3938284338881999333349547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5251045785175999111132729 3938284338881999333349547)
                ·
                  refine ⟨5907426508322999000024321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938284338881999333349547 5907426508322999000024321)
                  ·
                    refine ⟨4430569881242249250018241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5907426508322999000024321 4430569881242249250018241)
                    ·
                      refine ⟨3322927410931686937513681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430569881242249250018241 3322927410931686937513681)
                      ·
                        rfl

theorem cell23_6471378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_6471378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471378 prefixEnd_6471378 := by exact prefixLift 6471378
  have htrace : WordTrace (prefixWord ++ tailWord_6471378) baseStart_6471378 baseEnd_6471378 := by
    simpa [prefixWord, tailWord_6471378, baseEnd_6471378] using wordTrace_append hprefix tailTrace_6471378
  have hstable : (prefixWord ++ tailWord_6471378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471378).length < 2 ^ (prefixWord ++ tailWord_6471378).sum := by decide
  have hdescent : baseEnd_6471378 < baseStart_6471378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471380 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_6471380 : Nat := 118140960795 + 6471380 * 2 ^ 59
def prefixEnd_6471380 : Nat := 4983230072969 + 3 ^ 40 * 6471380 * 2
def baseEnd_6471380 : Nat := 1107642812630998643229557

theorem tailTrace_6471380 : CollatzResearch.WordTrace tailWord_6471380 prefixEnd_6471380 1107642812630998643229557 := by
  unfold tailWord_6471380
  simp only [CollatzResearch.WordTrace]
  refine ⟨118015309647651479278877797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157353746196868639038503729 118015309647651479278877797)
  ·
    refine ⟨22127870558934652364789587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118015309647651479278877797 22127870558934652364789587)
    ·
      refine ⟨33191805838401978547184381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22127870558934652364789587 33191805838401978547184381)
      ·
        refine ⟨12446927189400741955194143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33191805838401978547184381 12446927189400741955194143)
        ·
          refine ⟨18670390784101112932791215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12446927189400741955194143 18670390784101112932791215)
          ·
            refine ⟨28005586176151669399186823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18670390784101112932791215 28005586176151669399186823)
            ·
              refine ⟨42008379264227504098780235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28005586176151669399186823 42008379264227504098780235)
              ·
                refine ⟨63012568896341256148170353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42008379264227504098780235 63012568896341256148170353)
                ·
                  refine ⟨47259426672255942111127765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63012568896341256148170353 47259426672255942111127765)
                  ·
                    refine ⟨1107642812630998643229557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47259426672255942111127765 1107642812630998643229557)
                    ·
                      rfl

theorem cell23_6471380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_6471380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471380 prefixEnd_6471380 := by exact prefixLift 6471380
  have htrace : WordTrace (prefixWord ++ tailWord_6471380) baseStart_6471380 baseEnd_6471380 := by
    simpa [prefixWord, tailWord_6471380, baseEnd_6471380] using wordTrace_append hprefix tailTrace_6471380
  have hstable : (prefixWord ++ tailWord_6471380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471380).length < 2 ^ (prefixWord ++ tailWord_6471380).sum := by decide
  have hdescent : baseEnd_6471380 < baseStart_6471380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471383 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_6471383 : Nat := 118140960795 + 6471383 * 2 ^ 59
def prefixEnd_6471383 : Nat := 4983230072969 + 3 ^ 40 * 6471383 * 2
def baseEnd_6471383 : Nat := 3322929978334959417951157

theorem tailTrace_6471383 : CollatzResearch.WordTrace tailWord_6471383 prefixEnd_6471383 3322929978334959417951157 := by
  unfold tailWord_6471383
  simp only [CollatzResearch.WordTrace]
  refine ⟨236030728714292090070114803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157353819142861393380076535 236030728714292090070114803)
  ·
    refine ⟨354046093071438135105172205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236030728714292090070114803 354046093071438135105172205)
    ·
      refine ⟨132767284901789300664439577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354046093071438135105172205 132767284901789300664439577)
      ·
        refine ⟨99575463676341975498329683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132767284901789300664439577 99575463676341975498329683)
        ·
          refine ⟨149363195514512963247494525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99575463676341975498329683 149363195514512963247494525)
          ·
            refine ⟨56011198317942361217810447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149363195514512963247494525 56011198317942361217810447)
            ·
              refine ⟨84016797476913541826715671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56011198317942361217810447 84016797476913541826715671)
              ·
                refine ⟨126025196215370312740073507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84016797476913541826715671 126025196215370312740073507)
                ·
                  refine ⟨189037794323055469110110261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126025196215370312740073507 189037794323055469110110261)
                  ·
                    refine ⟨17722293217786450229072837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 189037794323055469110110261 17722293217786450229072837)
                    ·
                      refine ⟨3322929978334959417951157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17722293217786450229072837 3322929978334959417951157)
                      ·
                        rfl

theorem cell23_6471383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_6471383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471383 prefixEnd_6471383 := by exact prefixLift 6471383
  have htrace : WordTrace (prefixWord ++ tailWord_6471383) baseStart_6471383 baseEnd_6471383 := by
    simpa [prefixWord, tailWord_6471383, baseEnd_6471383] using wordTrace_append hprefix tailTrace_6471383
  have hstable : (prefixWord ++ tailWord_6471383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471383).length < 2 ^ (prefixWord ++ tailWord_6471383).sum := by decide
  have hdescent : baseEnd_6471383 < baseStart_6471383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471403 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 5]
def baseStart_6471403 : Nat := 118140960795 + 6471403 * 2 ^ 59
def prefixEnd_6471403 : Nat := 4983230072969 + 3 ^ 40 * 6471403 * 2
def baseEnd_6471403 : Nat := 3322940247948049339701065

theorem tailTrace_6471403 : CollatzResearch.WordTrace tailWord_6471403 prefixEnd_6471403 3322940247948049339701065 := by
  unfold tailWord_6471403
  simp only [CollatzResearch.WordTrace]
  refine ⟨236031458174219633485842863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157354305449479755657228575 236031458174219633485842863)
  ·
    refine ⟨354047187261329450228764295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236031458174219633485842863 354047187261329450228764295)
    ·
      refine ⟨531070780891994175343146443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354047187261329450228764295 531070780891994175343146443)
      ·
        refine ⟨796606171337991263014719665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531070780891994175343146443 796606171337991263014719665)
        ·
          refine ⟨597454628503493447261039749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796606171337991263014719665 597454628503493447261039749)
          ·
            refine ⟨112022742844405021361444953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 597454628503493447261039749 112022742844405021361444953)
            ·
              refine ⟨84017057133303766021083715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112022742844405021361444953 84017057133303766021083715)
              ·
                refine ⟨126025585699955649031625573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84017057133303766021083715 126025585699955649031625573)
                ·
                  refine ⟨23629797318741684193429795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126025585699955649031625573 23629797318741684193429795)
                  ·
                    refine ⟨35444695978112526290144693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23629797318741684193429795 35444695978112526290144693)
                    ·
                      refine ⟨3322940247948049339701065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35444695978112526290144693 3322940247948049339701065)
                      ·
                        rfl

theorem cell23_6471403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_6471403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471403 prefixEnd_6471403 := by exact prefixLift 6471403
  have htrace : WordTrace (prefixWord ++ tailWord_6471403) baseStart_6471403 baseEnd_6471403 := by
    simpa [prefixWord, tailWord_6471403, baseEnd_6471403] using wordTrace_append hprefix tailTrace_6471403
  have hstable : (prefixWord ++ tailWord_6471403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471403).length < 2 ^ (prefixWord ++ tailWord_6471403).sum := by decide
  have hdescent : baseEnd_6471403 < baseStart_6471403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471434 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_6471434 : Nat := 118140960795 + 6471434 * 2 ^ 59
def prefixEnd_6471434 : Nat := 4983230072969 + 3 ^ 40 * 6471434 * 2
def baseEnd_6471434 : Nat := 3322956165848338718413423

theorem tailTrace_6471434 : CollatzResearch.WordTrace tailWord_6471434 prefixEnd_6471434 3322956165848338718413423 := by
  unfold tailWord_6471434
  simp only [CollatzResearch.WordTrace]
  refine ⟨59008147209276831445055339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157355059224738217186814237 59008147209276831445055339)
  ·
    refine ⟨88512220813915247167583009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59008147209276831445055339 88512220813915247167583009)
    ·
      refine ⟨66384165610436435375687257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88512220813915247167583009 66384165610436435375687257)
      ·
        refine ⟨49788124207827326531765443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66384165610436435375687257 49788124207827326531765443)
        ·
          refine ⟨74682186311740989797648165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49788124207827326531765443 74682186311740989797648165)
          ·
            refine ⟨14002909933451435587059031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74682186311740989797648165 14002909933451435587059031)
            ·
              refine ⟨21004364900177153380588547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14002909933451435587059031 21004364900177153380588547)
              ·
                refine ⟨31506547350265730070882821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21004364900177153380588547 31506547350265730070882821)
                ·
                  refine ⟨5907477628174824388290529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31506547350265730070882821 5907477628174824388290529)
                  ·
                    refine ⟨4430608221131118291217897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5907477628174824388290529 4430608221131118291217897)
                    ·
                      refine ⟨3322956165848338718413423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430608221131118291217897 3322956165848338718413423)
                      ·
                        rfl

theorem cell23_6471434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_6471434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471434 prefixEnd_6471434 := by exact prefixLift 6471434
  have htrace : WordTrace (prefixWord ++ tailWord_6471434) baseStart_6471434 baseEnd_6471434 := by
    simpa [prefixWord, tailWord_6471434, baseEnd_6471434] using wordTrace_append hprefix tailTrace_6471434
  have hstable : (prefixWord ++ tailWord_6471434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471434).length < 2 ^ (prefixWord ++ tailWord_6471434).sum := by decide
  have hdescent : baseEnd_6471434 < baseStart_6471434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471474 : List Nat := [3, 2, 1, 1, 3, 4, 1, 3, 5]
def baseStart_6471474 : Nat := 118140960795 + 6471474 * 2 ^ 59
def prefixEnd_6471474 : Nat := 4983230072969 + 3 ^ 40 * 6471474 * 2
def baseEnd_6471474 : Nat := 369219633897168729101471

theorem tailTrace_6471474 : CollatzResearch.WordTrace tailWord_6471474 prefixEnd_6471474 369219633897168729101471 := by
  unfold tailWord_6471474
  simp only [CollatzResearch.WordTrace]
  refine ⟨59008511939240603152919369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157356031837974941741118317 59008511939240603152919369)
  ·
    refine ⟨44256383954430452364689527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59008511939240603152919369 44256383954430452364689527)
    ·
      refine ⟨66384575931645678547034291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44256383954430452364689527 66384575931645678547034291)
      ·
        refine ⟨99576863897468517820551437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66384575931645678547034291 99576863897468517820551437)
        ·
          refine ⟨37341323961550694182706789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99576863897468517820551437 37341323961550694182706789)
          ·
            refine ⟨7001498242790755159257523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37341323961550694182706789 7001498242790755159257523)
            ·
              refine ⟨10502247364186132738886285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7001498242790755159257523 10502247364186132738886285)
              ·
                refine ⟨3938342761569799777082357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10502247364186132738886285 3938342761569799777082357)
                ·
                  refine ⟨369219633897168729101471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3938342761569799777082357 369219633897168729101471)
                  ·
                    rfl

theorem cell23_6471474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_6471474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471474 prefixEnd_6471474 := by exact prefixLift 6471474
  have htrace : WordTrace (prefixWord ++ tailWord_6471474) baseStart_6471474 baseEnd_6471474 := by
    simpa [prefixWord, tailWord_6471474, baseEnd_6471474] using wordTrace_append hprefix tailTrace_6471474
  have hstable : (prefixWord ++ tailWord_6471474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471474).length < 2 ^ (prefixWord ++ tailWord_6471474).sum := by decide
  have hdescent : baseEnd_6471474 < baseStart_6471474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471487 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 2, 5]
def baseStart_6471487 : Nat := 118140960795 + 6471487 * 2 ^ 59
def prefixEnd_6471487 : Nat := 4983230072969 + 3 ^ 40 * 6471487 * 2
def baseEnd_6471487 : Nat := 1107661126774342337016893

theorem tailTrace_6471487 : CollatzResearch.WordTrace tailWord_6471487 prefixEnd_6471487 1107661126774342337016893 := by
  unfold tailWord_6471487
  simp only [CollatzResearch.WordTrace]
  refine ⟨236034521905915315831900715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157356347937276877221267143 236034521905915315831900715)
  ·
    refine ⟨354051782858872973747851073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236034521905915315831900715 354051782858872973747851073)
    ·
      refine ⟨265538837144154730310888305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354051782858872973747851073 265538837144154730310888305)
      ·
        refine ⟨199154127858116047733166229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265538837144154730310888305 199154127858116047733166229)
        ·
          refine ⟨9335349743349189737492167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199154127858116047733166229 9335349743349189737492167)
          ·
            refine ⟨14003024615023784606238251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9335349743349189737492167 14003024615023784606238251)
            ·
              refine ⟨21004536922535676909357377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14003024615023784606238251 21004536922535676909357377)
              ·
                refine ⟨15753402691901757682018033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21004536922535676909357377 15753402691901757682018033)
                ·
                  refine ⟨11815052018926318261513525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15753402691901757682018033 11815052018926318261513525)
                  ·
                    refine ⟨1107661126774342337016893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11815052018926318261513525 1107661126774342337016893)
                    ·
                      rfl

theorem cell23_6471487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_6471487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471487 prefixEnd_6471487 := by exact prefixLift 6471487
  have htrace : WordTrace (prefixWord ++ tailWord_6471487) baseStart_6471487 baseEnd_6471487 := by
    simpa [prefixWord, tailWord_6471487, baseEnd_6471487] using wordTrace_append hprefix tailTrace_6471487
  have hstable : (prefixWord ++ tailWord_6471487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471487).length < 2 ^ (prefixWord ++ tailWord_6471487).sum := by decide
  have hdescent : baseEnd_6471487 < baseStart_6471487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471524 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_6471524 : Nat := 118140960795 + 6471524 * 2 ^ 59
def prefixEnd_6471524 : Nat := 4983230072969 + 3 ^ 40 * 6471524 * 2
def baseEnd_6471524 : Nat := 3323002379107243366288009

theorem tailTrace_6471524 : CollatzResearch.WordTrace tailWord_6471524 prefixEnd_6471524 3323002379107243366288009 := by
  unfold tailWord_6471524
  simp only [CollatzResearch.WordTrace]
  refine ⟨118017935703390635575498813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157357247604520847433998417 118017935703390635575498813)
  ·
    refine ⟨44256725888771488340812055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118017935703390635575498813 44256725888771488340812055)
    ·
      refine ⟨66385088833157232511218083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44256725888771488340812055 66385088833157232511218083)
      ·
        refine ⟨99577633249735848766827125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66385088833157232511218083 99577633249735848766827125)
        ·
          refine ⟨9335403117162735821890043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99577633249735848766827125 9335403117162735821890043)
          ·
            refine ⟨14003104675744103732835065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9335403117162735821890043 14003104675744103732835065)
            ·
              refine ⟨10502328506808077799626299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14003104675744103732835065 10502328506808077799626299)
              ·
                refine ⟨15753492760212116699439449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10502328506808077799626299 15753492760212116699439449)
                ·
                  refine ⟨11815119570159087524579587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15753492760212116699439449 11815119570159087524579587)
                  ·
                    refine ⟨17722679355238631286869381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11815119570159087524579587 17722679355238631286869381)
                    ·
                      refine ⟨3323002379107243366288009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17722679355238631286869381 3323002379107243366288009)
                      ·
                        rfl

theorem cell23_6471524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_6471524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471524 prefixEnd_6471524 := by exact prefixLift 6471524
  have htrace : WordTrace (prefixWord ++ tailWord_6471524) baseStart_6471524 baseEnd_6471524 := by
    simpa [prefixWord, tailWord_6471524, baseEnd_6471524] using wordTrace_append hprefix tailTrace_6471524
  have hstable : (prefixWord ++ tailWord_6471524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471524).length < 2 ^ (prefixWord ++ tailWord_6471524).sum := by decide
  have hdescent : baseEnd_6471524 < baseStart_6471524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471600 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_6471600 : Nat := 118140960795 + 6471600 * 2 ^ 59
def prefixEnd_6471600 : Nat := 4983230072969 + 3 ^ 40 * 6471600 * 2
def baseEnd_6471600 : Nat := 3323041403636985068937659

theorem tailTrace_6471600 : CollatzResearch.WordTrace tailWord_6471600 prefixEnd_6471600 3323041403636985068937659 := by
  unfold tailWord_6471600
  simp only [CollatzResearch.WordTrace]
  refine ⟨118019321677252968065382127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157359095569670624087176169 118019321677252968065382127)
  ·
    refine ⟨177028982515879452098073191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118019321677252968065382127 177028982515879452098073191)
    ·
      refine ⟨265543473773819178147109787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177028982515879452098073191 265543473773819178147109787)
      ·
        refine ⟨398315210660728767220664681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265543473773819178147109787 398315210660728767220664681)
        ·
          refine ⟨298736407995546575415498511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398315210660728767220664681 298736407995546575415498511)
          ·
            refine ⟨448104611993319863123247767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298736407995546575415498511 448104611993319863123247767)
            ·
              refine ⟨672156917989979794684871651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448104611993319863123247767 672156917989979794684871651)
              ·
                refine ⟨1008235376984969692027307477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672156917989979794684871651 1008235376984969692027307477)
                ·
                  refine ⟨23630516648085227156890019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1008235376984969692027307477 23630516648085227156890019)
                  ·
                    refine ⟨35445774972127840735335029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23630516648085227156890019 35445774972127840735335029)
                    ·
                      refine ⟨3323041403636985068937659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35445774972127840735335029 3323041403636985068937659)
                      ·
                        rfl

theorem cell23_6471600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_6471600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471600 prefixEnd_6471600 := by exact prefixLift 6471600
  have htrace : WordTrace (prefixWord ++ tailWord_6471600) baseStart_6471600 baseEnd_6471600 := by
    simpa [prefixWord, tailWord_6471600, baseEnd_6471600] using wordTrace_append hprefix tailTrace_6471600
  have hstable : (prefixWord ++ tailWord_6471600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471600).length < 2 ^ (prefixWord ++ tailWord_6471600).sum := by decide
  have hdescent : baseEnd_6471600 < baseStart_6471600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471624 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 1, 6]
def baseStart_6471624 : Nat := 118140960795 + 6471624 * 2 ^ 59
def prefixEnd_6471624 : Nat := 4983230072969 + 3 ^ 40 * 6471624 * 2
def baseEnd_6471624 : Nat := 1107684575724230991679183

theorem tailTrace_6471624 : CollatzResearch.WordTrace tailWord_6471624 prefixEnd_6471624 1107684575724230991679183 := by
  unfold tailWord_6471624
  simp only [CollatzResearch.WordTrace]
  refine ⟨118019759353209494114818963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157359679137612658819758617 118019759353209494114818963)
  ·
    refine ⟨177029639029814241172228445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118019759353209494114818963 177029639029814241172228445)
    ·
      refine ⟨66386114636180340439585667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177029639029814241172228445 66386114636180340439585667)
      ·
        refine ⟨99579171954270510659378501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66386114636180340439585667 99579171954270510659378501)
        ·
          refine ⟨18671094741425720748633469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99579171954270510659378501 18671094741425720748633469)
          ·
            refine ⟨7001660528034645280737551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18671094741425720748633469 7001660528034645280737551)
            ·
              refine ⟨10502490792051967921106327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7001660528034645280737551 10502490792051967921106327)
              ·
                refine ⟨15753736188077951881659491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10502490792051967921106327 15753736188077951881659491)
                ·
                  refine ⟨23630604282116927822489237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15753736188077951881659491 23630604282116927822489237)
                  ·
                    refine ⟨1107684575724230991679183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23630604282116927822489237 1107684575724230991679183)
                    ·
                      rfl

theorem cell23_6471624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_6471624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471624 prefixEnd_6471624 := by exact prefixLift 6471624
  have htrace : WordTrace (prefixWord ++ tailWord_6471624) baseStart_6471624 baseEnd_6471624 := by
    simpa [prefixWord, tailWord_6471624, baseEnd_6471624] using wordTrace_append hprefix tailTrace_6471624
  have hstable : (prefixWord ++ tailWord_6471624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471624).length < 2 ^ (prefixWord ++ tailWord_6471624).sum := by decide
  have hdescent : baseEnd_6471624 < baseStart_6471624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471637 : List Nat := [1, 3, 2, 3, 2, 2, 1, 9]
def baseStart_6471637 : Nat := 118140960795 + 6471637 * 2 ^ 59
def prefixEnd_6471637 : Nat := 4983230072969 + 3 ^ 40 * 6471637 * 2
def baseEnd_6471637 : Nat := 123076311200785237932407

theorem tailTrace_6471637 : CollatzResearch.WordTrace tailWord_6471637 prefixEnd_6471637 123076311200785237932407 := by
  unfold tailWord_6471637
  simp only [CollatzResearch.WordTrace]
  refine ⟨236039992855371891449861165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157359995236914594299907443 236039992855371891449861165)
  ·
    refine ⟨88514997320764459293697937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236039992855371891449861165 88514997320764459293697937)
    ·
      refine ⟨66386247990573344470273453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88514997320764459293697937 66386247990573344470273453)
      ·
        refine ⟨24894842996465004176352545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66386247990573344470273453 24894842996465004176352545)
        ·
          refine ⟨18671132247348753132264409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24894842996465004176352545 18671132247348753132264409)
          ·
            refine ⟨14003349185511564849198307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18671132247348753132264409 14003349185511564849198307)
            ·
              refine ⟨21005023778267347273797461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14003349185511564849198307 21005023778267347273797461)
              ·
                refine ⟨123076311200785237932407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21005023778267347273797461 123076311200785237932407)
                ·
                  rfl

theorem cell23_6471637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 9].length) (baseStart_6471637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471637 prefixEnd_6471637 := by exact prefixLift 6471637
  have htrace : WordTrace (prefixWord ++ tailWord_6471637) baseStart_6471637 baseEnd_6471637 := by
    simpa [prefixWord, tailWord_6471637, baseEnd_6471637] using wordTrace_append hprefix tailTrace_6471637
  have hstable : (prefixWord ++ tailWord_6471637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471637).length < 2 ^ (prefixWord ++ tailWord_6471637).sum := by decide
  have hdescent : baseEnd_6471637 < baseStart_6471637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471664 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 4, 1, 3]
def baseStart_6471664 : Nat := 118140960795 + 6471664 * 2 ^ 59
def prefixEnd_6471664 : Nat := 4983230072969 + 3 ^ 40 * 6471664 * 2
def baseEnd_6471664 : Nat := 3323074266398872818537365

theorem tailTrace_6471664 : CollatzResearch.WordTrace tailWord_6471664 prefixEnd_6471664 3323074266398872818537365 := by
  unfold tailWord_6471664
  simp only [CollatzResearch.WordTrace]
  refine ⟨118020488813137037530547023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157360651750849383374062697 118020488813137037530547023)
  ·
    refine ⟨177030733219705556295820535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118020488813137037530547023 177030733219705556295820535)
    ·
      refine ⟨265546099829558334443730803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177030733219705556295820535 265546099829558334443730803)
      ·
        refine ⟨398319149744337501665596205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265546099829558334443730803 398319149744337501665596205)
        ·
          refine ⟨149369681154126563124598577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398319149744337501665596205 149369681154126563124598577)
          ·
            refine ⟨112027260865594922343448933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149369681154126563124598577 112027260865594922343448933)
            ·
              refine ⟨21005111412299047939396675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112027260865594922343448933 21005111412299047939396675)
              ·
                refine ⟨31507667118448571909095013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21005111412299047939396675 31507667118448571909095013)
                ·
                  refine ⟨5907687584709107232955315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31507667118448571909095013 5907687584709107232955315)
                  ·
                    refine ⟨8861531377063660849432973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5907687584709107232955315 8861531377063660849432973)
                    ·
                      refine ⟨3323074266398872818537365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8861531377063660849432973 3323074266398872818537365)
                      ·
                        rfl

theorem cell23_6471664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 1, 3].length) (baseStart_6471664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471664 prefixEnd_6471664 := by exact prefixLift 6471664
  have htrace : WordTrace (prefixWord ++ tailWord_6471664) baseStart_6471664 baseEnd_6471664 := by
    simpa [prefixWord, tailWord_6471664, baseEnd_6471664] using wordTrace_append hprefix tailTrace_6471664
  have hstable : (prefixWord ++ tailWord_6471664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471664).length < 2 ^ (prefixWord ++ tailWord_6471664).sum := by decide
  have hdescent : baseEnd_6471664 < baseStart_6471664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471665 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 3, 2, 2]
def baseStart_6471665 : Nat := 118140960795 + 6471665 * 2 ^ 59
def prefixEnd_6471665 : Nat := 4983230072969 + 3 ^ 40 * 6471665 * 2
def baseEnd_6471665 : Nat := 3323074779879527314624861

theorem tailTrace_6471665 : CollatzResearch.WordTrace tailWord_6471665 prefixEnd_6471665 3323074779879527314624861 := by
  unfold tailWord_6471665
  simp only [CollatzResearch.WordTrace]
  refine ⟨236041014099270452231880449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157360676066180301487920299 236041014099270452231880449)
  ·
    refine ⟨177030760574452839173910337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236041014099270452231880449 177030760574452839173910337)
    ·
      refine ⟨132773070430839629380432753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177030760574452839173910337 132773070430839629380432753)
      ·
        refine ⟨99579802823129722035324565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132773070430839629380432753 99579802823129722035324565)
        ·
          refine ⟨4667803257334205720405839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99579802823129722035324565 4667803257334205720405839)
          ·
            refine ⟨7001704886001308580608759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4667803257334205720405839 7001704886001308580608759)
            ·
              refine ⟨10502557329001962870913139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7001704886001308580608759 10502557329001962870913139)
              ·
                refine ⟨15753835993502944306369709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10502557329001962870913139 15753835993502944306369709)
                ·
                  refine ⟨5907688497563604114888641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15753835993502944306369709 5907688497563604114888641)
                  ·
                    refine ⟨4430766373172703086166481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5907688497563604114888641 4430766373172703086166481)
                    ·
                      refine ⟨3323074779879527314624861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430766373172703086166481 3323074779879527314624861)
                      ·
                        rfl

theorem cell23_6471665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_6471665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471665 prefixEnd_6471665 := by exact prefixLift 6471665
  have htrace : WordTrace (prefixWord ++ tailWord_6471665) baseStart_6471665 baseEnd_6471665 := by
    simpa [prefixWord, tailWord_6471665, baseEnd_6471665] using wordTrace_append hprefix tailTrace_6471665
  have hstable : (prefixWord ++ tailWord_6471665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471665).length < 2 ^ (prefixWord ++ tailWord_6471665).sum := by decide
  have hdescent : baseEnd_6471665 < baseStart_6471665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471681 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_6471681 : Nat := 118140960795 + 6471681 * 2 ^ 59
def prefixEnd_6471681 : Nat := 4983230072969 + 3 ^ 40 * 6471681 * 2
def baseEnd_6471681 : Nat := 3323082995569999252024787

theorem tailTrace_6471681 : CollatzResearch.WordTrace tailWord_6471681 prefixEnd_6471681 3323082995569999252024787 := by
  unfold tailWord_6471681
  simp only [CollatzResearch.WordTrace]
  refine ⟨236041597667212486964462897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157361065111474991309641931 236041597667212486964462897)
  ·
    refine ⟨177031198250409365223347173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236041597667212486964462897 177031198250409365223347173)
    ·
      refine ⟨33193349671951755979377595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177031198250409365223347173 33193349671951755979377595)
      ·
        refine ⟨49790024507927633969066393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33193349671951755979377595 49790024507927633969066393)
        ·
          refine ⟨37342518380945725476799795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49790024507927633969066393 37342518380945725476799795)
          ·
            refine ⟨56013777571418588215199693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37342518380945725476799795 56013777571418588215199693)
            ·
              refine ⟨21005166589281970580699885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56013777571418588215199693 21005166589281970580699885)
              ·
                refine ⟨7876937470980738967762457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21005166589281970580699885 7876937470980738967762457)
                ·
                  refine ⟨5907703103235554225821843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7876937470980738967762457 5907703103235554225821843)
                  ·
                    refine ⟨8861554654853331338732765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5907703103235554225821843 8861554654853331338732765)
                    ·
                      refine ⟨3323082995569999252024787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8861554654853331338732765 3323082995569999252024787)
                      ·
                        rfl

theorem cell23_6471681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_6471681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471681 prefixEnd_6471681 := by exact prefixLift 6471681
  have htrace : WordTrace (prefixWord ++ tailWord_6471681) baseStart_6471681 baseEnd_6471681 := by
    simpa [prefixWord, tailWord_6471681, baseEnd_6471681] using wordTrace_append hprefix tailTrace_6471681
  have hstable : (prefixWord ++ tailWord_6471681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471681).length < 2 ^ (prefixWord ++ tailWord_6471681).sum := by decide
  have hdescent : baseEnd_6471681 < baseStart_6471681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471767 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_6471767 : Nat := 118140960795 + 6471767 * 2 ^ 59
def prefixEnd_6471767 : Nat := 4983230072969 + 3 ^ 40 * 6471767 * 2
def baseEnd_6471767 : Nat := 3323127154906285915549391

theorem tailTrace_6471767 : CollatzResearch.WordTrace tailWord_6471767 prefixEnd_6471767 3323127154906285915549391 := by
  unfold tailWord_6471767
  simp only [CollatzResearch.WordTrace]
  refine ⟨236044734344900923652093555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157363156229933949101395703 236044734344900923652093555)
  ·
    refine ⟨354067101517351385478140333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236044734344900923652093555 354067101517351385478140333)
    ·
      refine ⟨132775163069006769554302625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354067101517351385478140333 132775163069006769554302625)
      ·
        refine ⟨99581372301755077165726969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132775163069006769554302625 99581372301755077165726969)
        ·
          refine ⟨74686029226316307874295227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99581372301755077165726969 74686029226316307874295227)
          ·
            refine ⟨112029043839474461811442841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74686029226316307874295227 112029043839474461811442841)
            ·
              refine ⟨84021782879605846358582131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112029043839474461811442841 84021782879605846358582131)
              ·
                refine ⟨126032674319408769537873197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84021782879605846358582131 126032674319408769537873197)
                ·
                  refine ⟨47262252869778288576702449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126032674319408769537873197 47262252869778288576702449)
                  ·
                    refine ⟨35446689652333716432526837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47262252869778288576702449 35446689652333716432526837)
                    ·
                      refine ⟨3323127154906285915549391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35446689652333716432526837 3323127154906285915549391)
                      ·
                        rfl

theorem cell23_6471767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_6471767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471767 prefixEnd_6471767 := by exact prefixLift 6471767
  have htrace : WordTrace (prefixWord ++ tailWord_6471767) baseStart_6471767 baseEnd_6471767 := by
    simpa [prefixWord, tailWord_6471767, baseEnd_6471767] using wordTrace_append hprefix tailTrace_6471767
  have hstable : (prefixWord ++ tailWord_6471767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471767).length < 2 ^ (prefixWord ++ tailWord_6471767).sum := by decide
  have hdescent : baseEnd_6471767 < baseStart_6471767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471794 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6471794 : Nat := 118140960795 + 6471794 * 2 ^ 59
def prefixEnd_6471794 : Nat := 4983230072969 + 3 ^ 40 * 6471794 * 2
def baseEnd_6471794 : Nat := 3323141018883957309911767

theorem tailTrace_6471794 : CollatzResearch.WordTrace tailWord_6471794 prefixEnd_6471794 3323141018883957309911767 := by
  unfold tailWord_6471794
  simp only [CollatzResearch.WordTrace]
  refine ⟨59011429778950776815831609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157363812743868738175550957 59011429778950776815831609)
  ·
    refine ⟨44258572334213082611873707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59011429778950776815831609 44258572334213082611873707)
    ·
      refine ⟨66387858501319623917810561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44258572334213082611873707 66387858501319623917810561)
      ·
        refine ⟨49790893875989717938357921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66387858501319623917810561 49790893875989717938357921)
        ·
          refine ⟨37343170406992288453768441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49790893875989717938357921 37343170406992288453768441)
          ·
            refine ⟨28007377805244216340326331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37343170406992288453768441 28007377805244216340326331)
            ·
              refine ⟨42011066707866324510489497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28007377805244216340326331 42011066707866324510489497)
              ·
                refine ⟨31508300030899743382867123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42011066707866324510489497 31508300030899743382867123)
                ·
                  refine ⟨47262450046349615074300685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31508300030899743382867123 47262450046349615074300685)
                  ·
                    refine ⟨17723418767381105652862757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47262450046349615074300685 17723418767381105652862757)
                    ·
                      refine ⟨3323141018883957309911767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17723418767381105652862757 3323141018883957309911767)
                      ·
                        rfl

theorem cell23_6471794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6471794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471794 prefixEnd_6471794 := by exact prefixLift 6471794
  have htrace : WordTrace (prefixWord ++ tailWord_6471794) baseStart_6471794 baseEnd_6471794 := by
    simpa [prefixWord, tailWord_6471794, baseEnd_6471794] using wordTrace_append hprefix tailTrace_6471794
  have hstable : (prefixWord ++ tailWord_6471794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471794).length < 2 ^ (prefixWord ++ tailWord_6471794).sum := by decide
  have hdescent : baseEnd_6471794 < baseStart_6471794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471817 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 10]
def baseStart_6471817 : Nat := 118140960795 + 6471817 * 2 ^ 59
def prefixEnd_6471817 : Nat := 4983230072969 + 3 ^ 40 * 6471817 * 2
def baseEnd_6471817 : Nat := 369239203215445635547129

theorem tailTrace_6471817 : CollatzResearch.WordTrace tailWord_6471817 prefixEnd_6471817 369239203215445635547129 := by
  unfold tailWord_6471817
  simp only [CollatzResearch.WordTrace]
  refine ⟨236046557994719782191413705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157364371996479854794275803 236046557994719782191413705)
  ·
    refine ⟨177034918496039836643560279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236046557994719782191413705 177034918496039836643560279)
    ·
      refine ⟨265552377744059754965340419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177034918496039836643560279 265552377744059754965340419)
      ·
        refine ⟨398328566616089632448010629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265552377744059754965340419 398328566616089632448010629)
        ·
          refine ⟨74686606240516806084001993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398328566616089632448010629 74686606240516806084001993)
          ·
            refine ⟨56014954680387604563001495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74686606240516806084001993 56014954680387604563001495)
            ·
              refine ⟨84022432020581406844502243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56014954680387604563001495 84022432020581406844502243)
              ·
                refine ⟨126033648030872110266753365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84022432020581406844502243 126033648030872110266753365)
                ·
                  refine ⟨369239203215445635547129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126033648030872110266753365 369239203215445635547129)
                  ·
                    rfl

theorem cell23_6471817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 10].length) (baseStart_6471817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471817 prefixEnd_6471817 := by exact prefixLift 6471817
  have htrace : WordTrace (prefixWord ++ tailWord_6471817) baseStart_6471817 baseEnd_6471817 := by
    simpa [prefixWord, tailWord_6471817, baseEnd_6471817] using wordTrace_append hprefix tailTrace_6471817
  have hstable : (prefixWord ++ tailWord_6471817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471817).length < 2 ^ (prefixWord ++ tailWord_6471817).sum := by decide
  have hdescent : baseEnd_6471817 < baseStart_6471817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471864 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 3, 5]
def baseStart_6471864 : Nat := 118140960795 + 6471864 * 2 ^ 59
def prefixEnd_6471864 : Nat := 4983230072969 + 3 ^ 40 * 6471864 * 2
def baseEnd_6471864 : Nat := 1107725654176590678678815

theorem tailTrace_6471864 : CollatzResearch.WordTrace tailWord_6471864 prefixEnd_6471864 1107725654176590678678815 := by
  unfold tailWord_6471864
  simp only [CollatzResearch.WordTrace]
  refine ⟨118024136112774754609187323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157365514817033006145583097 118024136112774754609187323)
  ·
    refine ⟨177036204169162131913780985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118024136112774754609187323 177036204169162131913780985)
    ·
      refine ⟨132777153126871598935335739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177036204169162131913780985 132777153126871598935335739)
      ·
        refine ⟨199165729690307398403003609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132777153126871598935335739 199165729690307398403003609)
        ·
          refine ⟨149374297267730548802252707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199165729690307398403003609 149374297267730548802252707)
          ·
            refine ⟨224061445901595823203379061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149374297267730548802252707 224061445901595823203379061)
            ·
              refine ⟨21005760553274608425316787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224061445901595823203379061 21005760553274608425316787)
              ·
                refine ⟨31508640829911912637975181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21005760553274608425316787 31508640829911912637975181)
                ·
                  refine ⟨11815740311216967239240693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31508640829911912637975181 11815740311216967239240693)
                  ·
                    refine ⟨1107725654176590678678815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11815740311216967239240693 1107725654176590678678815)
                    ·
                      rfl

theorem cell23_6471864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_6471864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471864 prefixEnd_6471864 := by exact prefixLift 6471864
  have htrace : WordTrace (prefixWord ++ tailWord_6471864) baseStart_6471864 baseEnd_6471864 := by
    simpa [prefixWord, tailWord_6471864, baseEnd_6471864] using wordTrace_append hprefix tailTrace_6471864
  have hstable : (prefixWord ++ tailWord_6471864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471864).length < 2 ^ (prefixWord ++ tailWord_6471864).sum := by decide
  have hdescent : baseEnd_6471864 < baseStart_6471864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471904 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_6471904 : Nat := 118140960795 + 6471904 * 2 ^ 59
def prefixEnd_6471904 : Nat := 4983230072969 + 3 ^ 40 * 6471904 * 2
def baseEnd_6471904 : Nat := 3323197501755951879536261

theorem tailTrace_6471904 : CollatzResearch.WordTrace tailWord_6471904 prefixEnd_6471904 3323197501755951879536261 := by
  unfold tailWord_6471904
  simp only [CollatzResearch.WordTrace]
  refine ⟨118024865572702298024915383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157366487430269730699887177 118024865572702298024915383)
  ·
    refine ⟨177037298359053447037373075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118024865572702298024915383 177037298359053447037373075)
    ·
      refine ⟨265555947538580170556059613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177037298359053447037373075 265555947538580170556059613)
      ·
        refine ⟨99583480326967563958522355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265555947538580170556059613 99583480326967563958522355)
        ·
          refine ⟨149375220490451345937783533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99583480326967563958522355 149375220490451345937783533)
          ·
            refine ⟨56015707683919254726668825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149375220490451345937783533 56015707683919254726668825)
            ·
              refine ⟨42011780762939441045001619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56015707683919254726668825 42011780762939441045001619)
              ·
                refine ⟨63017671144409161567502429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42011780762939441045001619 63017671144409161567502429)
                ·
                  refine ⟨23631626679153435587813411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63017671144409161567502429 23631626679153435587813411)
                  ·
                    refine ⟨35447440018730153381720117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23631626679153435587813411 35447440018730153381720117)
                    ·
                      refine ⟨3323197501755951879536261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35447440018730153381720117 3323197501755951879536261)
                      ·
                        rfl

theorem cell23_6471904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_6471904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471904 prefixEnd_6471904 := by exact prefixLift 6471904
  have htrace : WordTrace (prefixWord ++ tailWord_6471904) baseStart_6471904 baseEnd_6471904 := by
    simpa [prefixWord, tailWord_6471904, baseEnd_6471904] using wordTrace_append hprefix tailTrace_6471904
  have hstable : (prefixWord ++ tailWord_6471904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471904).length < 2 ^ (prefixWord ++ tailWord_6471904).sum := by decide
  have hdescent : baseEnd_6471904 < baseStart_6471904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471911 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 1, 6]
def baseStart_6471911 : Nat := 118140960795 + 6471911 * 2 ^ 59
def prefixEnd_6471911 : Nat := 4983230072969 + 3 ^ 40 * 6471911 * 2
def baseEnd_6471911 : Nat := 1107733698706844450716243

theorem tailTrace_6471911 : CollatzResearch.WordTrace tailWord_6471911 prefixEnd_6471911 1107733698706844450716243 := by
  unfold tailWord_6471911
  simp only [CollatzResearch.WordTrace]
  refine ⟨236049986456379236245335587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157366657637586157496890391 236049986456379236245335587)
  ·
    refine ⟨354074979684568854368003381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236049986456379236245335587 354074979684568854368003381)
    ·
      refine ⟨33194529345428330097000317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 354074979684568854368003381 33194529345428330097000317)
      ·
        refine ⟨12447948504535623786375119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33194529345428330097000317 12447948504535623786375119)
        ·
          refine ⟨18671922756803435679562679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12447948504535623786375119 18671922756803435679562679)
          ·
            refine ⟨28007884135205153519344019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18671922756803435679562679 28007884135205153519344019)
            ·
              refine ⟨42011826202807730279016029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28007884135205153519344019 42011826202807730279016029)
              ·
                refine ⟨15754434826052898854631011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42011826202807730279016029 15754434826052898854631011)
                ·
                  refine ⟨23631652239079348281946517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15754434826052898854631011 23631652239079348281946517)
                  ·
                    refine ⟨1107733698706844450716243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23631652239079348281946517 1107733698706844450716243)
                    ·
                      rfl

theorem cell23_6471911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_6471911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471911 prefixEnd_6471911 := by exact prefixLift 6471911
  have htrace : WordTrace (prefixWord ++ tailWord_6471911) baseStart_6471911 baseEnd_6471911 := by
    simpa [prefixWord, tailWord_6471911, baseEnd_6471911] using wordTrace_append hprefix tailTrace_6471911
  have hstable : (prefixWord ++ tailWord_6471911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471911).length < 2 ^ (prefixWord ++ tailWord_6471911).sum := by decide
  have hdescent : baseEnd_6471911 < baseStart_6471911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471921 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_6471921 : Nat := 118140960795 + 6471921 * 2 ^ 59
def prefixEnd_6471921 : Nat := 4983230072969 + 3 ^ 40 * 6471921 * 2
def baseEnd_6471921 : Nat := 3323206230927078313023683

theorem tailTrace_6471921 : CollatzResearch.WordTrace tailWord_6471921 prefixEnd_6471921 3323206230927078313023683 := by
  unfold tailWord_6471921
  simp only [CollatzResearch.WordTrace]
  refine ⟨236050351186343007953199617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157366900790895338635466411 236050351186343007953199617)
  ·
    refine ⟨177037763389757255964899713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236050351186343007953199617 177037763389757255964899713)
    ·
      refine ⟨132778322542317941973674785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177037763389757255964899713 132778322542317941973674785)
      ·
        refine ⟨99583741906738456480256089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132778322542317941973674785 99583741906738456480256089)
        ·
          refine ⟨74687806430053842360192067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99583741906738456480256089 74687806430053842360192067)
          ·
            refine ⟨112031709645080763540288101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74687806430053842360192067 112031709645080763540288101)
            ·
              refine ⟨21005945558452643163804019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112031709645080763540288101 21005945558452643163804019)
              ·
                refine ⟨31508918337678964745706029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21005945558452643163804019 31508918337678964745706029)
                ·
                  refine ⟨11815844376629611779639761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31508918337678964745706029 11815844376629611779639761)
                  ·
                    refine ⟨8861883282472208834729821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11815844376629611779639761 8861883282472208834729821)
                    ·
                      refine ⟨3323206230927078313023683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8861883282472208834729821 3323206230927078313023683)
                      ·
                        rfl

theorem cell23_6471921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_6471921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471921 prefixEnd_6471921 := by exact prefixLift 6471921
  have htrace : WordTrace (prefixWord ++ tailWord_6471921) baseStart_6471921 baseEnd_6471921 := by
    simpa [prefixWord, tailWord_6471921, baseEnd_6471921] using wordTrace_append hprefix tailTrace_6471921
  have hstable : (prefixWord ++ tailWord_6471921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471921).length < 2 ^ (prefixWord ++ tailWord_6471921).sum := by decide
  have hdescent : baseEnd_6471921 < baseStart_6471921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471965 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_6471965 : Nat := 118140960795 + 6471965 * 2 ^ 59
def prefixEnd_6471965 : Nat := 4983230072969 + 3 ^ 40 * 6471965 * 2
def baseEnd_6471965 : Nat := 3323228824075876140873481

theorem tailTrace_6471965 : CollatzResearch.WordTrace tailWord_6471965 prefixEnd_6471965 3323228824075876140873481 := by
  unfold tailWord_6471965
  simp only [CollatzResearch.WordTrace]
  refine ⟨236051955998183603467801349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157367970665455735645200899 236051955998183603467801349)
  ·
    refine ⟨44259741749659425650212753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236051955998183603467801349 44259741749659425650212753)
    ·
      refine ⟨33194806312244569237659565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44259741749659425650212753 33194806312244569237659565)
      ·
        refine ⟨12448052367091713464122337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33194806312244569237659565 12448052367091713464122337)
        ·
          refine ⟨9336039275318785098091753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12448052367091713464122337 9336039275318785098091753)
          ·
            refine ⟨7002029456489088823568815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9336039275318785098091753 7002029456489088823568815)
            ·
              refine ⟨10503044184733633235353223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002029456489088823568815 10503044184733633235353223)
              ·
                refine ⟨15754566277100449853029835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10503044184733633235353223 15754566277100449853029835)
                ·
                  refine ⟨23631849415650674779544753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15754566277100449853029835 23631849415650674779544753)
                  ·
                    refine ⟨17723887061738006084658565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23631849415650674779544753 17723887061738006084658565)
                    ·
                      refine ⟨3323228824075876140873481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17723887061738006084658565 3323228824075876140873481)
                      ·
                        rfl

theorem cell23_6471965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_6471965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471965 prefixEnd_6471965 := by exact prefixLift 6471965
  have htrace : WordTrace (prefixWord ++ tailWord_6471965) baseStart_6471965 baseEnd_6471965 := by
    simpa [prefixWord, tailWord_6471965, baseEnd_6471965] using wordTrace_append hprefix tailTrace_6471965
  have hstable : (prefixWord ++ tailWord_6471965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471965).length < 2 ^ (prefixWord ++ tailWord_6471965).sum := by decide
  have hdescent : baseEnd_6471965 < baseStart_6471965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471968 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 3]
def baseStart_6471968 : Nat := 118140960795 + 6471968 * 2 ^ 59
def prefixEnd_6471968 : Nat := 4983230072969 + 3 ^ 40 * 6471968 * 2
def baseEnd_6471968 : Nat := 3323230364517839629135967

theorem tailTrace_6471968 : CollatzResearch.WordTrace tailWord_6471968 prefixEnd_6471968 3323230364517839629135967 := by
  unfold tailWord_6471968
  simp only [CollatzResearch.WordTrace]
  refine ⟨118026032708586367490080279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157368043611448489986773705 118026032708586367490080279)
  ·
    refine ⟨177039049062879551235120419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118026032708586367490080279 177039049062879551235120419)
    ·
      refine ⟨265558573594319326852680629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177039049062879551235120419 265558573594319326852680629)
      ·
        refine ⟨24896116274467436892438809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265558573594319326852680629 24896116274467436892438809)
        ·
          refine ⟨18672087205850577669329107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24896116274467436892438809 18672087205850577669329107)
          ·
            refine ⟨28008130808775866503993661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18672087205850577669329107 28008130808775866503993661)
            ·
              refine ⟨10503049053290949938997623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28008130808775866503993661 10503049053290949938997623)
              ·
                refine ⟨15754573579936424908496435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10503049053290949938997623 15754573579936424908496435)
                ·
                  refine ⟨23631860369904637362744653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15754573579936424908496435 23631860369904637362744653)
                  ·
                    refine ⟨8861947638714239011029245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23631860369904637362744653 8861947638714239011029245)
                    ·
                      refine ⟨3323230364517839629135967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8861947638714239011029245 3323230364517839629135967)
                      ·
                        rfl

theorem cell23_6471968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_6471968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471968 prefixEnd_6471968 := by exact prefixLift 6471968
  have htrace : WordTrace (prefixWord ++ tailWord_6471968) baseStart_6471968 baseEnd_6471968 := by
    simpa [prefixWord, tailWord_6471968, baseEnd_6471968] using wordTrace_append hprefix tailTrace_6471968
  have hstable : (prefixWord ++ tailWord_6471968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471968).length < 2 ^ (prefixWord ++ tailWord_6471968).sum := by decide
  have hdescent : baseEnd_6471968 < baseStart_6471968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471975 : List Nat := [1, 1, 8, 1, 1, 1, 1, 9]
def baseStart_6471975 : Nat := 118140960795 + 6471975 * 2 ^ 59
def prefixEnd_6471975 : Nat := 4983230072969 + 3 ^ 40 * 6471975 * 2
def baseEnd_6471975 : Nat := 123082739217867448212905

theorem tailTrace_6471975 : CollatzResearch.WordTrace tailWord_6471975 prefixEnd_6471975 123082739217867448212905 := by
  unfold tailWord_6471975
  simp only [CollatzResearch.WordTrace]
  refine ⟨236052320728147375175665379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157368213818764916783776919 236052320728147375175665379)
  ·
    refine ⟨354078481092221062763498069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236052320728147375175665379 354078481092221062763498069)
    ·
      refine ⟨4149357200299465579259743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 354078481092221062763498069 4149357200299465579259743)
      ·
        refine ⟨6224035800449198368889615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4149357200299465579259743 6224035800449198368889615)
        ·
          refine ⟨9336053700673797553334423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224035800449198368889615 9336053700673797553334423)
          ·
            refine ⟨14004080551010696330001635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336053700673797553334423 14004080551010696330001635)
            ·
              refine ⟨21006120826516044495002453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14004080551010696330001635 21006120826516044495002453)
              ·
                refine ⟨123082739217867448212905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21006120826516044495002453 123082739217867448212905)
                ·
                  rfl

theorem cell23_6471975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 9].length) (baseStart_6471975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471975 prefixEnd_6471975 := by exact prefixLift 6471975
  have htrace : WordTrace (prefixWord ++ tailWord_6471975) baseStart_6471975 baseEnd_6471975 := by
    simpa [prefixWord, tailWord_6471975, baseEnd_6471975] using wordTrace_append hprefix tailTrace_6471975
  have hstable : (prefixWord ++ tailWord_6471975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471975).length < 2 ^ (prefixWord ++ tailWord_6471975).sum := by decide
  have hdescent : baseEnd_6471975 < baseStart_6471975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471984 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 4, 6]
def baseStart_6471984 : Nat := 118140960795 + 6471984 * 2 ^ 59
def prefixEnd_6471984 : Nat := 4983230072969 + 3 ^ 40 * 6471984 * 2
def baseEnd_6471984 : Nat := 1107746193402770522178631

theorem tailTrace_6471984 : CollatzResearch.WordTrace tailWord_6471984 prefixEnd_6471984 1107746193402770522178631 := by
  unfold tailWord_6471984
  simp only [CollatzResearch.WordTrace]
  refine ⟨118026324492557384856371503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157368432656743179808495337 118026324492557384856371503)
  ·
    refine ⟨177039486738836077284557255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118026324492557384856371503 177039486738836077284557255)
    ·
      refine ⟨265559230108254115926835883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177039486738836077284557255 265559230108254115926835883)
      ·
        refine ⟨398338845162381173890253825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265559230108254115926835883 398338845162381173890253825)
        ·
          refine ⟨298754133871785880417690369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398338845162381173890253825 298754133871785880417690369)
          ·
            refine ⟨224065600403839410313267777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298754133871785880417690369 224065600403839410313267777)
            ·
              refine ⟨168049200302879557734950833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224065600403839410313267777 168049200302879557734950833)
              ·
                refine ⟨126036900227159668301213125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168049200302879557734950833 126036900227159668301213125)
                ·
                  refine ⟨23631918792592437806477461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126036900227159668301213125 23631918792592437806477461)
                  ·
                    refine ⟨1107746193402770522178631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23631918792592437806477461 1107746193402770522178631)
                    ·
                      rfl

theorem cell23_6471984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_6471984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471984 prefixEnd_6471984 := by exact prefixLift 6471984
  have htrace : WordTrace (prefixWord ++ tailWord_6471984) baseStart_6471984 baseEnd_6471984 := by
    simpa [prefixWord, tailWord_6471984, baseEnd_6471984] using wordTrace_append hprefix tailTrace_6471984
  have hstable : (prefixWord ++ tailWord_6471984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471984).length < 2 ^ (prefixWord ++ tailWord_6471984).sum := by decide
  have hdescent : baseEnd_6471984 < baseStart_6471984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471986 : List Nat := [3, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_6471986 : Nat := 118140960795 + 6471986 * 2 ^ 59
def prefixEnd_6471986 : Nat := 4983230072969 + 3 ^ 40 * 6471986 * 2
def baseEnd_6471986 : Nat := 3323239607169620558710885

theorem tailTrace_6471986 : CollatzResearch.WordTrace tailWord_6471986 prefixEnd_6471986 3323239607169620558710885 := by
  unfold tailWord_6471986
  simp only [CollatzResearch.WordTrace]
  refine ⟨59013180482776881013578953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157368481287405016036210541 59013180482776881013578953)
  ·
    refine ⟨44259885362082660760184215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59013180482776881013578953 44259885362082660760184215)
    ·
      refine ⟨66389828043123991140276323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44259885362082660760184215 66389828043123991140276323)
      ·
        refine ⟨99584742064685986710414485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66389828043123991140276323 99584742064685986710414485)
        ·
          refine ⟨4668034784282155627050679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99584742064685986710414485 4668034784282155627050679)
          ·
            refine ⟨7002052176423233440576019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668034784282155627050679 7002052176423233440576019)
            ·
              refine ⟨10503078264634850160864029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002052176423233440576019 10503078264634850160864029)
              ·
                refine ⟨3938654349238068810324011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10503078264634850160864029 3938654349238068810324011)
                ·
                  refine ⟨5907981523857103215486017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938654349238068810324011 5907981523857103215486017)
                  ·
                    refine ⟨4430986142892827411614513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5907981523857103215486017 4430986142892827411614513)
                    ·
                      refine ⟨3323239607169620558710885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430986142892827411614513 3323239607169620558710885)
                      ·
                        rfl

theorem cell23_6471986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_6471986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471986 prefixEnd_6471986 := by exact prefixLift 6471986
  have htrace : WordTrace (prefixWord ++ tailWord_6471986) baseStart_6471986 baseEnd_6471986 := by
    simpa [prefixWord, tailWord_6471986, baseEnd_6471986] using wordTrace_append hprefix tailTrace_6471986
  have hstable : (prefixWord ++ tailWord_6471986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471986).length < 2 ^ (prefixWord ++ tailWord_6471986).sum := by decide
  have hdescent : baseEnd_6471986 < baseStart_6471986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472065 : List Nat := [1, 2, 4, 3, 1, 2, 1, 4, 5]
def baseStart_6472065 : Nat := 118140960795 + 6472065 * 2 ^ 59
def prefixEnd_6472065 : Nat := 4983230072969 + 3 ^ 40 * 6472065 * 2
def baseEnd_6472065 : Nat := 369253352460147305513669

theorem tailTrace_6472065 : CollatzResearch.WordTrace tailWord_6472065 prefixEnd_6472065 369253352460147305513669 := by
  unfold tailWord_6472065
  simp only [CollatzResearch.WordTrace]
  refine ⟨236055603297821320546441649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157370402198547547030961099 236055603297821320546441649)
  ·
    refine ⟨177041702473365990409831237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236055603297821320546441649 177041702473365990409831237)
    ·
      refine ⟨33195319213756123201843357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177041702473365990409831237 33195319213756123201843357)
      ·
        refine ⟨12448244705158546200691259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33195319213756123201843357 12448244705158546200691259)
        ·
          refine ⟨18672367057737819301036889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12448244705158546200691259 18672367057737819301036889)
          ·
            refine ⟨14004275293303364475777667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18672367057737819301036889 14004275293303364475777667)
            ·
              refine ⟨21006412939955046713666501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14004275293303364475777667 21006412939955046713666501)
              ·
                refine ⟨3938702426241571258812469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21006412939955046713666501 3938702426241571258812469)
                ·
                  refine ⟨369253352460147305513669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3938702426241571258812469 369253352460147305513669)
                  ·
                    rfl

theorem cell23_6472065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 5].length) (baseStart_6472065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472065 prefixEnd_6472065 := by exact prefixLift 6472065
  have htrace : WordTrace (prefixWord ++ tailWord_6472065) baseStart_6472065 baseEnd_6472065 := by
    simpa [prefixWord, tailWord_6472065, baseEnd_6472065] using wordTrace_append hprefix tailTrace_6472065
  have hstable : (prefixWord ++ tailWord_6472065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472065).length < 2 ^ (prefixWord ++ tailWord_6472065).sum := by decide
  have hdescent : baseEnd_6472065 < baseStart_6472065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472068 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_6472068 : Nat := 118140960795 + 6472068 * 2 ^ 59
def prefixEnd_6472068 : Nat := 4983230072969 + 3 ^ 40 * 6472068 * 2
def baseEnd_6472068 : Nat := 3323281712583289237885507

theorem tailTrace_6472068 : CollatzResearch.WordTrace tailWord_6472068 prefixEnd_6472068 3323281712583289237885507 := by
  unfold tailWord_6472068
  simp only [CollatzResearch.WordTrace]
  refine ⟨118027856358405226029400429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157370475144540301372533905 118027856358405226029400429)
  ·
    refine ⟨44260446134401959761025161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118027856358405226029400429 44260446134401959761025161)
    ·
      refine ⟨33195334600801469820768871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44260446134401959761025161 33195334600801469820768871)
      ·
        refine ⟨49793001901202204731153307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33195334600801469820768871 49793001901202204731153307)
        ·
          refine ⟨74689502851803307096729961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49793001901202204731153307 74689502851803307096729961)
          ·
            refine ⟨56017127138852480322547471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74689502851803307096729961 56017127138852480322547471)
            ·
              refine ⟨84025690708278720483821207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56017127138852480322547471 84025690708278720483821207)
              ·
                refine ⟨126038536062418080725731811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84025690708278720483821207 126038536062418080725731811)
                ·
                  refine ⟨189057804093627121088597717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126038536062418080725731811 189057804093627121088597717)
                  ·
                    refine ⟨4431042283444385650514009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 189057804093627121088597717 4431042283444385650514009)
                    ·
                      refine ⟨3323281712583289237885507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431042283444385650514009 3323281712583289237885507)
                      ·
                        rfl

theorem cell23_6472068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_6472068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472068 prefixEnd_6472068 := by exact prefixLift 6472068
  have htrace : WordTrace (prefixWord ++ tailWord_6472068) baseStart_6472068 baseEnd_6472068 := by
    simpa [prefixWord, tailWord_6472068, baseEnd_6472068] using wordTrace_append hprefix tailTrace_6472068
  have hstable : (prefixWord ++ tailWord_6472068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472068).length < 2 ^ (prefixWord ++ tailWord_6472068).sum := by decide
  have hdescent : baseEnd_6472068 < baseStart_6472068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472071 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_6472071 : Nat := 118140960795 + 6472071 * 2 ^ 59
def prefixEnd_6472071 : Nat := 4983230072969 + 3 ^ 40 * 6472071 * 2
def baseEnd_6472071 : Nat := 3323283253025252726147993

theorem tailTrace_6472071 : CollatzResearch.WordTrace tailWord_6472071 prefixEnd_6472071 3323283253025252726147993 := by
  unfold tailWord_6472071
  simp only [CollatzResearch.WordTrace]
  refine ⟨236055822135799583571160067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157370548090533055714106711 236055822135799583571160067)
  ·
    refine ⟨354083733203699375356740101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236055822135799583571160067 354083733203699375356740101)
    ·
      refine ⟨66390699975693632879388769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354083733203699375356740101 66390699975693632879388769)
      ·
        refine ⟨49793024981770224659541577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66390699975693632879388769 49793024981770224659541577)
        ·
          refine ⟨37344768736327668494656183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49793024981770224659541577 37344768736327668494656183)
          ·
            refine ⟨56017153104491502741984275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37344768736327668494656183 56017153104491502741984275)
            ·
              refine ⟨84025729656737254112976413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56017153104491502741984275 84025729656737254112976413)
              ·
                refine ⟨31509648621276470292366155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84025729656737254112976413 31509648621276470292366155)
                ·
                  refine ⟨47264472931914705438549233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31509648621276470292366155 47264472931914705438549233)
                  ·
                    refine ⟨35448354698936029078911925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47264472931914705438549233 35448354698936029078911925)
                    ·
                      refine ⟨3323283253025252726147993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35448354698936029078911925 3323283253025252726147993)
                      ·
                        rfl

theorem cell23_6472071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_6472071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472071 prefixEnd_6472071 := by exact prefixLift 6472071
  have htrace : WordTrace (prefixWord ++ tailWord_6472071) baseStart_6472071 baseEnd_6472071 := by
    simpa [prefixWord, tailWord_6472071, baseEnd_6472071] using wordTrace_append hprefix tailTrace_6472071
  have hstable : (prefixWord ++ tailWord_6472071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472071).length < 2 ^ (prefixWord ++ tailWord_6472071).sum := by decide
  have hdescent : baseEnd_6472071 < baseStart_6472071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472098 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_6472098 : Nat := 118140960795 + 6472098 * 2 ^ 59
def prefixEnd_6472098 : Nat := 4983230072969 + 3 ^ 40 * 6472098 * 2
def baseEnd_6472098 : Nat := 3323297117002924120510369

theorem tailTrace_6472098 : CollatzResearch.WordTrace tailWord_6472098 prefixEnd_6472098 3323297117002924120510369 := by
  unfold tailWord_6472098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59014201726675441795598237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157371204604467844788261965 59014201726675441795598237)
  ·
    refine ⟨22130325647503290673349339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59014201726675441795598237 22130325647503290673349339)
    ·
      refine ⟨33195488471254936010024009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22130325647503290673349339 33195488471254936010024009)
      ·
        refine ⟨24896616353441202007518007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33195488471254936010024009 24896616353441202007518007)
        ·
          refine ⟨37344924530161803011277011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24896616353441202007518007 37344924530161803011277011)
          ·
            refine ⟨56017386795242704516915517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37344924530161803011277011 56017386795242704516915517)
            ·
              refine ⟨21006520048216014193843319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56017386795242704516915517 21006520048216014193843319)
              ·
                refine ⟨31509780072324021290764979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21006520048216014193843319 31509780072324021290764979)
                ·
                  refine ⟨47264670108486031936147469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31509780072324021290764979 47264670108486031936147469)
                  ·
                    refine ⟨17724251290682261976055301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47264670108486031936147469 17724251290682261976055301)
                    ·
                      refine ⟨3323297117002924120510369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17724251290682261976055301 3323297117002924120510369)
                      ·
                        rfl

theorem cell23_6472098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_6472098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472098 prefixEnd_6472098 := by exact prefixLift 6472098
  have htrace : WordTrace (prefixWord ++ tailWord_6472098) baseStart_6472098 baseEnd_6472098 := by
    simpa [prefixWord, tailWord_6472098, baseEnd_6472098] using wordTrace_append hprefix tailTrace_6472098
  have hstable : (prefixWord ++ tailWord_6472098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472098).length < 2 ^ (prefixWord ++ tailWord_6472098).sum := by decide
  have hdescent : baseEnd_6472098 < baseStart_6472098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472125 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_6472125 : Nat := 118140960795 + 6472125 * 2 ^ 59
def prefixEnd_6472125 : Nat := 4983230072969 + 3 ^ 40 * 6472125 * 2
def baseEnd_6472125 : Nat := 1107770326993531838290915

theorem tailTrace_6472125 : CollatzResearch.WordTrace tailWord_6472125 prefixEnd_6472125 1107770326993531838290915 := by
  unfold tailWord_6472125
  simp only [CollatzResearch.WordTrace]
  refine ⟨236057791677603950793625829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157371861118402633862417219 236057791677603950793625829)
  ·
    refine ⟨44260835939550740773804843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236057791677603950793625829 44260835939550740773804843)
    ·
      refine ⟨66391253909326111160707265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44260835939550740773804843 66391253909326111160707265)
      ·
        refine ⟨49793440431994583370530449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66391253909326111160707265 49793440431994583370530449)
        ·
          refine ⟨37345080323995937527897837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49793440431994583370530449 37345080323995937527897837)
          ·
            refine ⟨14004405121498476572961689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37345080323995937527897837 14004405121498476572961689)
            ·
              refine ⟨10503303841123857429721267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14004405121498476572961689 10503303841123857429721267)
              ·
                refine ⟨15754955761685786144581901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10503303841123857429721267 15754955761685786144581901)
                ·
                  refine ⟨5908108410632169804218213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15754955761685786144581901 5908108410632169804218213)
                  ·
                    refine ⟨1107770326993531838290915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908108410632169804218213 1107770326993531838290915)
                    ·
                      rfl

theorem cell23_6472125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_6472125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472125 prefixEnd_6472125 := by exact prefixLift 6472125
  have htrace : WordTrace (prefixWord ++ tailWord_6472125) baseStart_6472125 baseEnd_6472125 := by
    simpa [prefixWord, tailWord_6472125, baseEnd_6472125] using wordTrace_append hprefix tailTrace_6472125
  have hstable : (prefixWord ++ tailWord_6472125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472125).length < 2 ^ (prefixWord ++ tailWord_6472125).sum := by decide
  have hdescent : baseEnd_6472125 < baseStart_6472125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472188 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_6472188 : Nat := 118140960795 + 6472188 * 2 ^ 59
def prefixEnd_6472188 : Nat := 4983230072969 + 3 ^ 40 * 6472188 * 2
def baseEnd_6472188 : Nat := 3323343330261828768384955

theorem tailTrace_6472188 : CollatzResearch.WordTrace tailWord_6472188 prefixEnd_6472188 3323343330261828768384955 := by
  unfold tailWord_6472188
  simp only [CollatzResearch.WordTrace]
  refine ⟨118030044738187856276584609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157373392984250475035446145 118030044738187856276584609)
  ·
    refine ⟨88522533553640892207438457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118030044738187856276584609 88522533553640892207438457)
    ·
      refine ⟨66391900165230669155578843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88522533553640892207438457 66391900165230669155578843)
      ·
        refine ⟨99587850247846003733368265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66391900165230669155578843 99587850247846003733368265)
        ·
          refine ⟨74690887685884502800026199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99587850247846003733368265 74690887685884502800026199)
          ·
            refine ⟨112036331528826754200039299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74690887685884502800026199 112036331528826754200039299)
            ·
              refine ⟨168054497293240131300058949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112036331528826754200039299 168054497293240131300058949)
              ·
                refine ⟨31510218242482524618761053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168054497293240131300058949 31510218242482524618761053)
                ·
                  refine ⟨11816331840930946732035395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31510218242482524618761053 11816331840930946732035395)
                  ·
                    refine ⟨17724497761396420098053093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11816331840930946732035395 17724497761396420098053093)
                    ·
                      refine ⟨3323343330261828768384955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17724497761396420098053093 3323343330261828768384955)
                      ·
                        rfl

theorem cell23_6472188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_6472188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472188 prefixEnd_6472188 := by exact prefixLift 6472188
  have htrace : WordTrace (prefixWord ++ tailWord_6472188) baseStart_6472188 baseEnd_6472188 := by
    simpa [prefixWord, tailWord_6472188, baseEnd_6472188] using wordTrace_append hprefix tailTrace_6472188
  have hstable : (prefixWord ++ tailWord_6472188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472188).length < 2 ^ (prefixWord ++ tailWord_6472188).sum := by decide
  have hdescent : baseEnd_6472188 < baseStart_6472188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472211 : List Nat := [1, 1, 1, 2, 1, 5, 1, 11]
def baseStart_6472211 : Nat := 118140960795 + 6472211 * 2 ^ 59
def prefixEnd_6472211 : Nat := 4983230072969 + 3 ^ 40 * 6472211 * 2
def baseEnd_6472211 : Nat := 123087227419143784385087

theorem tailTrace_6472211 : CollatzResearch.WordTrace tailWord_6472211 prefixEnd_6472211 123087227419143784385087 := by
  unfold tailWord_6472211
  simp only [CollatzResearch.WordTrace]
  refine ⟨236060928355292387481256487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157373952236861591654170991 236060928355292387481256487)
  ·
    refine ⟨354091392532938581221884731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236060928355292387481256487 354091392532938581221884731)
    ·
      refine ⟨531137088799407871832827097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354091392532938581221884731 531137088799407871832827097)
      ·
        refine ⟨398352816599555903874620323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531137088799407871832827097 398352816599555903874620323)
        ·
          refine ⟨597529224899333855811930485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398352816599555903874620323 597529224899333855811930485)
          ·
            refine ⟨56018364834312548982368483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 597529224899333855811930485 56018364834312548982368483)
            ·
              refine ⟨84027547251468823473552725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56018364834312548982368483 84027547251468823473552725)
              ·
                refine ⟨123087227419143784385087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84027547251468823473552725 123087227419143784385087)
                ·
                  rfl

theorem cell23_6472211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 11].length) (baseStart_6472211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472211 prefixEnd_6472211 := by exact prefixLift 6472211
  have htrace : WordTrace (prefixWord ++ tailWord_6472211) baseStart_6472211 baseEnd_6472211 := by
    simpa [prefixWord, tailWord_6472211, baseEnd_6472211] using wordTrace_append hprefix tailTrace_6472211
  have hstable : (prefixWord ++ tailWord_6472211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472211).length < 2 ^ (prefixWord ++ tailWord_6472211).sum := by decide
  have hdescent : baseEnd_6472211 < baseStart_6472211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472218 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_6472218 : Nat := 118140960795 + 6472218 * 2 ^ 59
def prefixEnd_6472218 : Nat := 4983230072969 + 3 ^ 40 * 6472218 * 2
def baseEnd_6472218 : Nat := 3323358734681463651009817

theorem tailTrace_6472218 : CollatzResearch.WordTrace tailWord_6472218 prefixEnd_6472218 3323358734681463651009817 := by
  unfold tailWord_6472218
  simp only [CollatzResearch.WordTrace]
  refine ⟨59015295916566756919190327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157374122444178018451174205 59015295916566756919190327)
  ·
    refine ⟨88522943874850135378785491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59015295916566756919190327 88522943874850135378785491)
    ·
      refine ⟨132784415812275203068178237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88522943874850135378785491 132784415812275203068178237)
      ·
        refine ⟨49794155929603201150566839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132784415812275203068178237 49794155929603201150566839)
        ·
          refine ⟨74691233894404801725850259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49794155929603201150566839 74691233894404801725850259)
          ·
            refine ⟨112036850841607202588775389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74691233894404801725850259 112036850841607202588775389)
            ·
              refine ⟨42013819065602700970790771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112036850841607202588775389 42013819065602700970790771)
              ·
                refine ⟨63020728598404051456186157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42013819065602700970790771 63020728598404051456186157)
                ·
                  refine ⟨23632773224401519296069809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63020728598404051456186157 23632773224401519296069809)
                  ·
                    refine ⟨17724579918301139472052357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23632773224401519296069809 17724579918301139472052357)
                    ·
                      refine ⟨3323358734681463651009817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17724579918301139472052357 3323358734681463651009817)
                      ·
                        rfl

theorem cell23_6472218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_6472218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472218 prefixEnd_6472218 := by exact prefixLift 6472218
  have htrace : WordTrace (prefixWord ++ tailWord_6472218) baseStart_6472218 baseEnd_6472218 := by
    simpa [prefixWord, tailWord_6472218, baseEnd_6472218] using wordTrace_append hprefix tailTrace_6472218
  have hstable : (prefixWord ++ tailWord_6472218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472218).length < 2 ^ (prefixWord ++ tailWord_6472218).sum := by decide
  have hdescent : baseEnd_6472218 < baseStart_6472218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472228 : List Nat := [2, 3, 1, 5, 12]
def baseStart_6472228 : Nat := 118140960795 + 6472228 * 2 ^ 59
def prefixEnd_6472228 : Nat := 4983230072969 + 3 ^ 40 * 6472228 * 2
def baseEnd_6472228 : Nat := 4558798174880670249499

theorem tailTrace_6472228 : CollatzResearch.WordTrace tailWord_6472228 prefixEnd_6472228 4558798174880670249499 := by
  unfold tailWord_6472228
  simp only [CollatzResearch.WordTrace]
  refine ⟨118030774198115399692312669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157374365597487199589750225 118030774198115399692312669)
  ·
    refine ⟨44261540324293274884617251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118030774198115399692312669 44261540324293274884617251)
    ·
      refine ⟨66392310486439912326925877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44261540324293274884617251 66392310486439912326925877)
      ·
        refine ⟨6224279108103741780649301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66392310486439912326925877 6224279108103741780649301)
        ·
          refine ⟨4558798174880670249499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6224279108103741780649301 4558798174880670249499)
          ·
            rfl

theorem cell23_6472228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 12].length) (baseStart_6472228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472228 prefixEnd_6472228 := by exact prefixLift 6472228
  have htrace : WordTrace (prefixWord ++ tailWord_6472228) baseStart_6472228 baseEnd_6472228 := by
    simpa [prefixWord, tailWord_6472228, baseEnd_6472228] using wordTrace_append hprefix tailTrace_6472228
  have hstable : (prefixWord ++ tailWord_6472228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472228).length < 2 ^ (prefixWord ++ tailWord_6472228).sum := by decide
  have hdescent : baseEnd_6472228 < baseStart_6472228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472232 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6472232 : Nat := 118140960795 + 6472232 * 2 ^ 59
def prefixEnd_6472232 : Nat := 4983230072969 + 3 ^ 40 * 6472232 * 2
def baseEnd_6472232 : Nat := 1107788641136875532078251

theorem tailTrace_6472232 : CollatzResearch.WordTrace tailWord_6472232 prefixEnd_6472232 1107788641136875532078251 := by
  unfold tailWord_6472232
  simp only [CollatzResearch.WordTrace]
  refine ⟨118030847144108154033885475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157374462858810872045180633 118030847144108154033885475)
  ·
    refine ⟨177046270716162231050828213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118030847144108154033885475 177046270716162231050828213)
    ·
      refine ⟨16598087879640209161015145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177046270716162231050828213 16598087879640209161015145)
      ·
        refine ⟨12448565909730156870761359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16598087879640209161015145 12448565909730156870761359)
        ·
          refine ⟨18672848864595235306142039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12448565909730156870761359 18672848864595235306142039)
          ·
            refine ⟨28009273296892852959213059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18672848864595235306142039 28009273296892852959213059)
            ·
              refine ⟨42013909945339279438819589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28009273296892852959213059 42013909945339279438819589)
              ·
                refine ⟨7877608114751114894778673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42013909945339279438819589 7877608114751114894778673)
                ·
                  refine ⟨5908206086063336171084005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7877608114751114894778673 5908206086063336171084005)
                  ·
                    refine ⟨1107788641136875532078251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908206086063336171084005 1107788641136875532078251)
                    ·
                      rfl

theorem cell23_6472232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6472232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472232 prefixEnd_6472232 := by exact prefixLift 6472232
  have htrace : WordTrace (prefixWord ++ tailWord_6472232) baseStart_6472232 baseEnd_6472232 := by
    simpa [prefixWord, tailWord_6472232, baseEnd_6472232] using wordTrace_append hprefix tailTrace_6472232
  have hstable : (prefixWord ++ tailWord_6472232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472232).length < 2 ^ (prefixWord ++ tailWord_6472232).sum := by decide
  have hdescent : baseEnd_6472232 < baseStart_6472232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472255 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 3]
def baseStart_6472255 : Nat := 118140960795 + 6472255 * 2 ^ 59
def prefixEnd_6472255 : Nat := 4983230072969 + 3 ^ 40 * 6472255 * 2
def baseEnd_6472255 : Nat := 3323377733465680006247147

theorem tailTrace_6472255 : CollatzResearch.WordTrace tailWord_6472255 prefixEnd_6472255 3323377733465680006247147 := by
  unfold tailWord_6472255
  simp only [CollatzResearch.WordTrace]
  refine ⟨236062533167132982995858219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157375022111421988663905479 236062533167132982995858219)
  ·
    refine ⟨354093799750699474493787329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236062533167132982995858219 354093799750699474493787329)
    ·
      refine ⟨265570349813024605870340497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354093799750699474493787329 265570349813024605870340497)
      ·
        refine ⟨199177762359768454402755373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265570349813024605870340497 199177762359768454402755373)
        ·
          refine ⟨74691660884913170401033265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199177762359768454402755373 74691660884913170401033265)
          ·
            refine ⟨56018745663684877800774949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74691660884913170401033265 56018745663684877800774949)
            ·
              refine ⟨10503514811940914587645303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56018745663684877800774949 10503514811940914587645303)
              ·
                refine ⟨15755272217911371881467955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10503514811940914587645303 15755272217911371881467955)
                ·
                  refine ⟨23632908326867057822201933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15755272217911371881467955 23632908326867057822201933)
                  ·
                    refine ⟨8862340622575146683325725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23632908326867057822201933 8862340622575146683325725)
                    ·
                      refine ⟨3323377733465680006247147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8862340622575146683325725 3323377733465680006247147)
                      ·
                        rfl

theorem cell23_6472255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_6472255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472255 prefixEnd_6472255 := by exact prefixLift 6472255
  have htrace : WordTrace (prefixWord ++ tailWord_6472255) baseStart_6472255 baseEnd_6472255 := by
    simpa [prefixWord, tailWord_6472255, baseEnd_6472255] using wordTrace_append hprefix tailTrace_6472255
  have hstable : (prefixWord ++ tailWord_6472255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472255).length < 2 ^ (prefixWord ++ tailWord_6472255).sum := by decide
  have hdescent : baseEnd_6472255 < baseStart_6472255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472260 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6472260 : Nat := 118140960795 + 6472260 * 2 ^ 59
def prefixEnd_6472260 : Nat := 4983230072969 + 3 ^ 40 * 6472260 * 2
def baseEnd_6472260 : Nat := 3323380300868952486684625

theorem tailTrace_6472260 : CollatzResearch.WordTrace tailWord_6472260 prefixEnd_6472260 3323380300868952486684625 := by
  unfold tailWord_6472260
  simp only [CollatzResearch.WordTrace]
  refine ⟨118031357766057434424895117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157375143688076579233193489 118031357766057434424895117)
  ·
    refine ⟨44261759162271537909335669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118031357766057434424895117 44261759162271537909335669)
    ·
      refine ⟨4149539921462956679000219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44261759162271537909335669 4149539921462956679000219)
      ·
        refine ⟨6224309882194435018500329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4149539921462956679000219 6224309882194435018500329)
        ·
          refine ⟨4668232411645826263875247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6224309882194435018500329 4668232411645826263875247)
          ·
            refine ⟨7002348617468739395812871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668232411645826263875247 7002348617468739395812871)
            ·
              refine ⟨10503522926203109093719307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002348617468739395812871 10503522926203109093719307)
              ·
                refine ⟨15755284389304663640578961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10503522926203109093719307 15755284389304663640578961)
                ·
                  refine ⟨11816463291978497730434221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15755284389304663640578961 11816463291978497730434221)
                  ·
                    refine ⟨4431173734491936648912833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11816463291978497730434221 4431173734491936648912833)
                    ·
                      refine ⟨3323380300868952486684625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431173734491936648912833 3323380300868952486684625)
                      ·
                        rfl

theorem cell23_6472260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6472260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472260 prefixEnd_6472260 := by exact prefixLift 6472260
  have htrace : WordTrace (prefixWord ++ tailWord_6472260) baseStart_6472260 baseEnd_6472260 := by
    simpa [prefixWord, tailWord_6472260, baseEnd_6472260] using wordTrace_append hprefix tailTrace_6472260
  have hstable : (prefixWord ++ tailWord_6472260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472260).length < 2 ^ (prefixWord ++ tailWord_6472260).sum := by decide
  have hdescent : baseEnd_6472260 < baseStart_6472260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472268 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_6472268 : Nat := 118140960795 + 6472268 * 2 ^ 59
def prefixEnd_6472268 : Nat := 4983230072969 + 3 ^ 40 * 6472268 * 2
def baseEnd_6472268 : Nat := 3323384408714188455384587

theorem tailTrace_6472268 : CollatzResearch.WordTrace tailWord_6472268 prefixEnd_6472268 3323384408714188455384587 := by
  unfold tailWord_6472268
  simp only [CollatzResearch.WordTrace]
  refine ⟨118031503658042943108040729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157375338210723924144054305 118031503658042943108040729)
  ·
    refine ⟨88523627743532207331030547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118031503658042943108040729 88523627743532207331030547)
    ·
      refine ⟨132785441615298310996545821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88523627743532207331030547 132785441615298310996545821)
      ·
        refine ⟨49794540605736866623704683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132785441615298310996545821 49794540605736866623704683)
        ·
          refine ⟨74691810908605299935557025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49794540605736866623704683 74691810908605299935557025)
          ·
            refine ⟨56018858181453974951667769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74691810908605299935557025 56018858181453974951667769)
            ·
              refine ⟨42014143636090481213750827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56018858181453974951667769 42014143636090481213750827)
              ·
                refine ⟨63021215454135721820626241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42014143636090481213750827 63021215454135721820626241)
                ·
                  refine ⟨47265911590601791365469681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63021215454135721820626241 47265911590601791365469681)
                  ·
                    refine ⟨35449433692951343524102261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47265911590601791365469681 35449433692951343524102261)
                    ·
                      refine ⟨3323384408714188455384587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35449433692951343524102261 3323384408714188455384587)
                      ·
                        rfl

theorem cell23_6472268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_6472268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472268 prefixEnd_6472268 := by exact prefixLift 6472268
  have htrace : WordTrace (prefixWord ++ tailWord_6472268) baseStart_6472268 baseEnd_6472268 := by
    simpa [prefixWord, tailWord_6472268, baseEnd_6472268] using wordTrace_append hprefix tailTrace_6472268
  have hstable : (prefixWord ++ tailWord_6472268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472268).length < 2 ^ (prefixWord ++ tailWord_6472268).sum := by decide
  have hdescent : baseEnd_6472268 < baseStart_6472268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472288 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 2, 6]
def baseStart_6472288 : Nat := 118140960795 + 6472288 * 2 ^ 59
def prefixEnd_6472288 : Nat := 4983230072969 + 3 ^ 40 * 6472288 * 2
def baseEnd_6472288 : Nat := 1107798226109092792378165

theorem tailTrace_6472288 : CollatzResearch.WordTrace tailWord_6472288 prefixEnd_6472288 1107798226109092792378165 := by
  unfold tailWord_6472288
  simp only [CollatzResearch.WordTrace]
  refine ⟨118031868388006714815904759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157375824517342286421206345 118031868388006714815904759)
  ·
    refine ⟨177047802582010072223857139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118031868388006714815904759 177047802582010072223857139)
    ·
      refine ⟨265571703873015108335785709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177047802582010072223857139 265571703873015108335785709)
      ·
        refine ⟨99589388952380665625919641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265571703873015108335785709 99589388952380665625919641)
        ·
          refine ⟨74692041714285499219439731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99589388952380665625919641 74692041714285499219439731)
          ·
            refine ⟨112038062571428248829159597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74692041714285499219439731 112038062571428248829159597)
            ·
              refine ⟨42014273464285593310934849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112038062571428248829159597 42014273464285593310934849)
              ·
                refine ⟨31510705098214194983201137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42014273464285593310934849 31510705098214194983201137)
                ·
                  refine ⟨23633028823660646237400853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31510705098214194983201137 23633028823660646237400853)
                  ·
                    refine ⟨1107798226109092792378165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23633028823660646237400853 1107798226109092792378165)
                    ·
                      rfl

theorem cell23_6472288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_6472288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472288 prefixEnd_6472288 := by exact prefixLift 6472288
  have htrace : WordTrace (prefixWord ++ tailWord_6472288) baseStart_6472288 baseEnd_6472288 := by
    simpa [prefixWord, tailWord_6472288, baseEnd_6472288] using wordTrace_append hprefix tailTrace_6472288
  have hstable : (prefixWord ++ tailWord_6472288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472288).length < 2 ^ (prefixWord ++ tailWord_6472288).sum := by decide
  have hdescent : baseEnd_6472288 < baseStart_6472288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472289 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_6472289 : Nat := 118140960795 + 6472289 * 2 ^ 59
def prefixEnd_6472289 : Nat := 4983230072969 + 3 ^ 40 * 6472289 * 2
def baseEnd_6472289 : Nat := 3323395191807932873221991

theorem tailTrace_6472289 : CollatzResearch.WordTrace tailWord_6472289 prefixEnd_6472289 3323395191807932873221991 := by
  unfold tailWord_6472289
  simp only [CollatzResearch.WordTrace]
  refine ⟨236063773249009806802595921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157375848832673204535063947 236063773249009806802595921)
  ·
    refine ⟨177047829936757355101946941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236063773249009806802595921 177047829936757355101946941)
    ·
      refine ⟨66392936226284008163230103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177047829936757355101946941 66392936226284008163230103)
      ·
        refine ⟨99589404339426012244845155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66392936226284008163230103 99589404339426012244845155)
        ·
          refine ⟨149384106509139018367267733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99589404339426012244845155 149384106509139018367267733)
          ·
            refine ⟨7002379992615891485965675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149384106509139018367267733 7002379992615891485965675)
            ·
              refine ⟨10503569988923837228948513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002379992615891485965675 10503569988923837228948513)
              ·
                refine ⟨7877677491692877921711385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10503569988923837228948513 7877677491692877921711385)
                ·
                  refine ⟨5908258118769658441283539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7877677491692877921711385 5908258118769658441283539)
                  ·
                    refine ⟨8862387178154487661925309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5908258118769658441283539 8862387178154487661925309)
                    ·
                      refine ⟨3323395191807932873221991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8862387178154487661925309 3323395191807932873221991)
                      ·
                        rfl

theorem cell23_6472289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_6472289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472289 prefixEnd_6472289 := by exact prefixLift 6472289
  have htrace : WordTrace (prefixWord ++ tailWord_6472289) baseStart_6472289 baseEnd_6472289 := by
    simpa [prefixWord, tailWord_6472289, baseEnd_6472289] using wordTrace_append hprefix tailTrace_6472289
  have hstable : (prefixWord ++ tailWord_6472289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472289).length < 2 ^ (prefixWord ++ tailWord_6472289).sum := by decide
  have hdescent : baseEnd_6472289 < baseStart_6472289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472306 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_6472306 : Nat := 118140960795 + 6472306 * 2 ^ 59
def prefixEnd_6472306 : Nat := 4983230072969 + 3 ^ 40 * 6472306 * 2
def baseEnd_6472306 : Nat := 3323403920979059306709413

theorem tailTrace_6472306 : CollatzResearch.WordTrace tailWord_6472306 prefixEnd_6472306 3323403920979059306709413 := by
  unfold tailWord_6472306
  simp only [CollatzResearch.WordTrace]
  refine ⟨59016098322487054676491193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157376262193298812470643181 59016098322487054676491193)
  ·
    refine ⟨44262073741865291007368395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59016098322487054676491193 44262073741865291007368395)
    ·
      refine ⟨66393110612797936511052593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44262073741865291007368395 66393110612797936511052593)
      ·
        refine ⟨49794832959598452383289445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66393110612797936511052593 49794832959598452383289445)
        ·
          refine ⟨9336531179924709821866771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49794832959598452383289445 9336531179924709821866771)
          ·
            refine ⟨14004796769887064732800157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336531179924709821866771 14004796769887064732800157)
            ·
              refine ⟨5251798788707649274800059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14004796769887064732800157 5251798788707649274800059)
              ·
                refine ⟨7877698183061473912200089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251798788707649274800059 7877698183061473912200089)
                ·
                  refine ⟨5908273637296105434150067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7877698183061473912200089 5908273637296105434150067)
                  ·
                    refine ⟨8862410455944158151225101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5908273637296105434150067 8862410455944158151225101)
                    ·
                      refine ⟨3323403920979059306709413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8862410455944158151225101 3323403920979059306709413)
                      ·
                        rfl

theorem cell23_6472306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_6472306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472306 prefixEnd_6472306 := by exact prefixLift 6472306
  have htrace : WordTrace (prefixWord ++ tailWord_6472306) baseStart_6472306 baseEnd_6472306 := by
    simpa [prefixWord, tailWord_6472306, baseEnd_6472306] using wordTrace_append hprefix tailTrace_6472306
  have hstable : (prefixWord ++ tailWord_6472306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472306).length < 2 ^ (prefixWord ++ tailWord_6472306).sum := by decide
  have hdescent : baseEnd_6472306 < baseStart_6472306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472352 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 7]
def baseStart_6472352 : Nat := 118140960795 + 6472352 * 2 ^ 59
def prefixEnd_6472352 : Nat := 4983230072969 + 3 ^ 40 * 6472352 * 2
def baseEnd_6472352 : Nat := 369269726787685125192689

theorem tailTrace_6472352 : CollatzResearch.WordTrace tailWord_6472352 prefixEnd_6472352 369269726787685125192689 := by
  unfold tailWord_6472352
  simp only [CollatzResearch.WordTrace]
  refine ⟨118033035523890784281069655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157377380698521045708092873 118033035523890784281069655)
  ·
    refine ⟨177049553285836176421604483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118033035523890784281069655 177049553285836176421604483)
    ·
      refine ⟨265574329928754264632406725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177049553285836176421604483 265574329928754264632406725)
      ·
        refine ⟨49795186861641424618576261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265574329928754264632406725 49795186861641424618576261)
        ·
          refine ⟨9336597536557767115983049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49795186861641424618576261 9336597536557767115983049)
          ·
            refine ⟨7002448152418325336987287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9336597536557767115983049 7002448152418325336987287)
            ·
              refine ⟨10503672228627488005480931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002448152418325336987287 10503672228627488005480931)
              ·
                refine ⟨15755508342941232008221397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10503672228627488005480931 15755508342941232008221397)
                ·
                  refine ⟨369269726787685125192689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15755508342941232008221397 369269726787685125192689)
                  ·
                    rfl

theorem cell23_6472352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 7].length) (baseStart_6472352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472352 prefixEnd_6472352 := by exact prefixLift 6472352
  have htrace : WordTrace (prefixWord ++ tailWord_6472352) baseStart_6472352 baseEnd_6472352 := by
    simpa [prefixWord, tailWord_6472352, baseEnd_6472352] using wordTrace_append hprefix tailTrace_6472352
  have hstable : (prefixWord ++ tailWord_6472352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472352).length < 2 ^ (prefixWord ++ tailWord_6472352).sum := by decide
  have hdescent : baseEnd_6472352 < baseStart_6472352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472382 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_6472382 : Nat := 118140960795 + 6472382 * 2 ^ 59
def prefixEnd_6472382 : Nat := 4983230072969 + 3 ^ 40 * 6472382 * 2
def baseEnd_6472382 : Nat := 1107814315169600336453021

theorem tailTrace_6472382 : CollatzResearch.WordTrace tailWord_6472382 prefixEnd_6472382 1107814315169600336453021 := by
  unfold tailWord_6472382
  simp only [CollatzResearch.WordTrace]
  refine ⟨29508395654709110460716425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157378110158448589123820933 29508395654709110460716425)
  ·
    refine ⟨22131296741031832845537319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29508395654709110460716425 22131296741031832845537319)
    ·
      refine ⟨33196945111547749268305979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22131296741031832845537319 33196945111547749268305979)
      ·
        refine ⟨49795417667321623902458969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33196945111547749268305979 49795417667321623902458969)
        ·
          refine ⟨37346563250491217926844227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49795417667321623902458969 37346563250491217926844227)
          ·
            refine ⟨56019844875736826890266341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37346563250491217926844227 56019844875736826890266341)
            ·
              refine ⟨10503720914200655041924939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56019844875736826890266341 10503720914200655041924939)
              ·
                refine ⟨15755581371300982562887409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10503720914200655041924939 15755581371300982562887409)
                ·
                  refine ⟨11816686028475736922165557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15755581371300982562887409 11816686028475736922165557)
                  ·
                    refine ⟨1107814315169600336453021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11816686028475736922165557 1107814315169600336453021)
                    ·
                      rfl

theorem cell23_6472382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_6472382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472382 prefixEnd_6472382 := by exact prefixLift 6472382
  have htrace : WordTrace (prefixWord ++ tailWord_6472382) baseStart_6472382 baseEnd_6472382 := by
    simpa [prefixWord, tailWord_6472382, baseEnd_6472382] using wordTrace_append hprefix tailTrace_6472382
  have hstable : (prefixWord ++ tailWord_6472382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472382).length < 2 ^ (prefixWord ++ tailWord_6472382).sum := by decide
  have hdescent : baseEnd_6472382 < baseStart_6472382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472419 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 2, 4, 2]
def baseStart_6472419 : Nat := 118140960795 + 6472419 * 2 ^ 59
def prefixEnd_6472419 : Nat := 4983230072969 + 3 ^ 40 * 6472419 * 2
def baseEnd_6472419 : Nat := 3323461944293017364596393

theorem tailTrace_6472419 : CollatzResearch.WordTrace tailWord_6472419 prefixEnd_6472419 3323461944293017364596393 := by
  unfold tailWord_6472419
  simp only [CollatzResearch.WordTrace]
  refine ⟨236068514738538839004828311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157379009825692559336552207 236068514738538839004828311)
  ·
    refine ⟨354102772107808258507242467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236068514738538839004828311 354102772107808258507242467)
    ·
      refine ⟨531154158161712387760863701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354102772107808258507242467 531154158161712387760863701)
      ·
        refine ⟨12448925581915134088145243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 531154158161712387760863701 12448925581915134088145243)
        ·
          refine ⟨18673388372872701132217865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12448925581915134088145243 18673388372872701132217865)
          ·
            refine ⟨14005041279654525849163399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18673388372872701132217865 14005041279654525849163399)
            ·
              refine ⟨21007561919481788773745099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14005041279654525849163399 21007561919481788773745099)
              ·
                refine ⟨31511342879222683160617649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21007561919481788773745099 31511342879222683160617649)
                ·
                  refine ⟨23633507159417012370463237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31511342879222683160617649 23633507159417012370463237)
                  ·
                    refine ⟨4431282592390689819461857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23633507159417012370463237 4431282592390689819461857)
                    ·
                      refine ⟨3323461944293017364596393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431282592390689819461857 3323461944293017364596393)
                      ·
                        rfl

theorem cell23_6472419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_6472419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472419 prefixEnd_6472419 := by exact prefixLift 6472419
  have htrace : WordTrace (prefixWord ++ tailWord_6472419) baseStart_6472419 baseEnd_6472419 := by
    simpa [prefixWord, tailWord_6472419, baseEnd_6472419] using wordTrace_append hprefix tailTrace_6472419
  have hstable : (prefixWord ++ tailWord_6472419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472419).length < 2 ^ (prefixWord ++ tailWord_6472419).sum := by decide
  have hdescent : baseEnd_6472419 < baseStart_6472419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472425 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 6]
def baseStart_6472425 : Nat := 118140960795 + 6472425 * 2 ^ 59
def prefixEnd_6472425 : Nat := 4983230072969 + 3 ^ 40 * 6472425 * 2
def baseEnd_6472425 : Nat := 369273891686327149013485

theorem tailTrace_6472425 : CollatzResearch.WordTrace tailWord_6472425 prefixEnd_6472425 369273891686327149013485 := by
  unfold tailWord_6472425
  simp only [CollatzResearch.WordTrace]
  refine ⟨236068733576517102029546729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157379155717678068019697819 236068733576517102029546729)
  ·
    refine ⟨177051550182387826522160047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236068733576517102029546729 177051550182387826522160047)
    ·
      refine ⟨265577325273581739783240071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177051550182387826522160047 265577325273581739783240071)
      ·
        refine ⟨398365987910372609674860107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265577325273581739783240071 398365987910372609674860107)
        ·
          refine ⟨597548981865558914512290161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398365987910372609674860107 597548981865558914512290161)
          ·
            refine ⟨448161736399169185884217621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597548981865558914512290161 448161736399169185884217621)
            ·
              refine ⟨21007581393711055588322701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 448161736399169185884217621 21007581393711055588322701)
              ·
                refine ⟨7877843022641645845621013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21007581393711055588322701 7877843022641645845621013)
                ·
                  refine ⟨369273891686327149013485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7877843022641645845621013 369273891686327149013485)
                  ·
                    rfl

theorem cell23_6472425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 6].length) (baseStart_6472425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472425 prefixEnd_6472425 := by exact prefixLift 6472425
  have htrace : WordTrace (prefixWord ++ tailWord_6472425) baseStart_6472425 baseEnd_6472425 := by
    simpa [prefixWord, tailWord_6472425, baseEnd_6472425] using wordTrace_append hprefix tailTrace_6472425
  have hstable : (prefixWord ++ tailWord_6472425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472425).length < 2 ^ (prefixWord ++ tailWord_6472425).sum := by decide
  have hdescent : baseEnd_6472425 < baseStart_6472425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472436 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6472436 : Nat := 118140960795 + 6472436 * 2 ^ 59
def prefixEnd_6472436 : Nat := 4983230072969 + 3 ^ 40 * 6472436 * 2
def baseEnd_6472436 : Nat := 3323470673464143798083815

theorem tailTrace_6472436 : CollatzResearch.WordTrace tailWord_6472436 prefixEnd_6472436 3323470673464143798083815 := by
  unfold tailWord_6472436
  simp only [CollatzResearch.WordTrace]
  refine ⟨118034567389738625454098581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157379423186318167272131441 118034567389738625454098581)
  ·
    refine ⟨5532870346393998068160871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118034567389738625454098581 5532870346393998068160871)
    ·
      refine ⟨8299305519590997102241307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5532870346393998068160871 8299305519590997102241307)
      ·
        refine ⟨12448958279386495653361961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299305519590997102241307 12448958279386495653361961)
        ·
          refine ⟨9336718709539871740021471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12448958279386495653361961 9336718709539871740021471)
          ·
            refine ⟨14005078064309807610032207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336718709539871740021471 14005078064309807610032207)
            ·
              refine ⟨21007617096464711415048311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14005078064309807610032207 21007617096464711415048311)
              ·
                refine ⟨31511425644697067122572467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21007617096464711415048311 31511425644697067122572467)
                ·
                  refine ⟨47267138467045600683858701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31511425644697067122572467 47267138467045600683858701)
                  ·
                    refine ⟨17725176925142100256447013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47267138467045600683858701 17725176925142100256447013)
                    ·
                      refine ⟨3323470673464143798083815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17725176925142100256447013 3323470673464143798083815)
                      ·
                        rfl

theorem cell23_6472436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6472436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472436 prefixEnd_6472436 := by exact prefixLift 6472436
  have htrace : WordTrace (prefixWord ++ tailWord_6472436) baseStart_6472436 baseEnd_6472436 := by
    simpa [prefixWord, tailWord_6472436, baseEnd_6472436] using wordTrace_append hprefix tailTrace_6472436
  have hstable : (prefixWord ++ tailWord_6472436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472436).length < 2 ^ (prefixWord ++ tailWord_6472436).sum := by decide
  have hdescent : baseEnd_6472436 < baseStart_6472436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472446 : List Nat := [4, 2, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_6472446 : Nat := 118140960795 + 6472446 * 2 ^ 59
def prefixEnd_6472446 : Nat := 4983230072969 + 3 ^ 40 * 6472446 * 2
def baseEnd_6472446 : Nat := 1107825269423562919652923

theorem tailTrace_6472446 : CollatzResearch.WordTrace tailWord_6472446 prefixEnd_6472446 1107825269423562919652923 := by
  unfold tailWord_6472446
  simp only [CollatzResearch.WordTrace]
  refine ⟨29508687438680127827007649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157379666339627348410707461 29508687438680127827007649)
  ·
    refine ⟨22131515579010095870255737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29508687438680127827007649 22131515579010095870255737)
    ·
      refine ⟨16598636684257571902691803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22131515579010095870255737 16598636684257571902691803)
      ·
        refine ⟨24897955026386357854037705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16598636684257571902691803 24897955026386357854037705)
        ·
          refine ⟨18673466269789768390528279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24897955026386357854037705 18673466269789768390528279)
          ·
            refine ⟨28010199404684652585792419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18673466269789768390528279 28010199404684652585792419)
            ·
              refine ⟨42015299107026978878688629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28010199404684652585792419 42015299107026978878688629)
              ·
                refine ⟨3938934291283779269877059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42015299107026978878688629 3938934291283779269877059)
                ·
                  refine ⟨5908401436925668904815589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938934291283779269877059 5908401436925668904815589)
                  ·
                    refine ⟨1107825269423562919652923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908401436925668904815589 1107825269423562919652923)
                    ·
                      rfl

theorem cell23_6472446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_6472446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472446 prefixEnd_6472446 := by exact prefixLift 6472446
  have htrace : WordTrace (prefixWord ++ tailWord_6472446) baseStart_6472446 baseEnd_6472446 := by
    simpa [prefixWord, tailWord_6472446, baseEnd_6472446] using wordTrace_append hprefix tailTrace_6472446
  have hstable : (prefixWord ++ tailWord_6472446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472446).length < 2 ^ (prefixWord ++ tailWord_6472446).sum := by decide
  have hdescent : baseEnd_6472446 < baseStart_6472446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472469 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_6472469 : Nat := 118140960795 + 6472469 * 2 ^ 59
def prefixEnd_6472469 : Nat := 4983230072969 + 3 ^ 40 * 6472469 * 2
def baseEnd_6472469 : Nat := 3323487618325742168971163

theorem tailTrace_6472469 : CollatzResearch.WordTrace tailWord_6472469 prefixEnd_6472469 3323487618325742168971163 := by
  unfold tailWord_6472469
  simp only [CollatzResearch.WordTrace]
  refine ⟨236070338388357697544148461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157380225592238465029432307 236070338388357697544148461)
  ·
    refine ⟨88526376895634136579055673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236070338388357697544148461 88526376895634136579055673)
    ·
      refine ⟨66394782671725602434291755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88526376895634136579055673 66394782671725602434291755)
      ·
        refine ⟨99592174007588403651437633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66394782671725602434291755 99592174007588403651437633)
        ·
          refine ⟨74694130505691302738578225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99592174007588403651437633 74694130505691302738578225)
          ·
            refine ⟨56020597879268477053933669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74694130505691302738578225 56020597879268477053933669)
            ·
              refine ⟨10503862102362839447612563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56020597879268477053933669 10503862102362839447612563)
              ·
                refine ⟨15755793153544259171418845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10503862102362839447612563 15755793153544259171418845)
                ·
                  refine ⟨5908422432579097189282067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15755793153544259171418845 5908422432579097189282067)
                  ·
                    refine ⟨8862633648868645783923101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5908422432579097189282067 8862633648868645783923101)
                    ·
                      refine ⟨3323487618325742168971163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8862633648868645783923101 3323487618325742168971163)
                      ·
                        rfl

theorem cell23_6472469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_6472469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472469 prefixEnd_6472469 := by exact prefixLift 6472469
  have htrace : WordTrace (prefixWord ++ tailWord_6472469) baseStart_6472469 baseEnd_6472469 := by
    simpa [prefixWord, tailWord_6472469, baseEnd_6472469] using wordTrace_append hprefix tailTrace_6472469
  have hstable : (prefixWord ++ tailWord_6472469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472469).length < 2 ^ (prefixWord ++ tailWord_6472469).sum := by decide
  have hdescent : baseEnd_6472469 < baseStart_6472469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472492 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 2, 6, 2]
def baseStart_6472492 : Nat := 118140960795 + 6472492 * 2 ^ 59
def prefixEnd_6472492 : Nat := 4983230072969 + 3 ^ 40 * 6472492 * 2
def baseEnd_6472492 : Nat := 3323499428380795578983557

theorem tailTrace_6472492 : CollatzResearch.WordTrace tailWord_6472492 prefixEnd_6472492 3323499428380795578983557 := by
  unfold tailWord_6472492
  simp only [CollatzResearch.WordTrace]
  refine ⟨118035588633637186236117865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157380784844849581648157153 118035588633637186236117865)
  ·
    refine ⟨88526691475227889677088399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118035588633637186236117865 88526691475227889677088399)
    ·
      refine ⟨132790037212841834515632599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88526691475227889677088399 132790037212841834515632599)
      ·
        refine ⟨199185055819262751773448899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132790037212841834515632599 199185055819262751773448899)
        ·
          refine ⟨298777583728894127660173349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199185055819262751773448899 298777583728894127660173349)
          ·
            refine ⟨56020796949167648936282503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298777583728894127660173349 56020796949167648936282503)
            ·
              refine ⟨84031195423751473404423755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56020796949167648936282503 84031195423751473404423755)
              ·
                refine ⟨126046793135627210106635633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84031195423751473404423755 126046793135627210106635633)
                ·
                  refine ⟨94535094851720407579976725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126046793135627210106635633 94535094851720407579976725)
                  ·
                    refine ⟨4431332571174394105311409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94535094851720407579976725 4431332571174394105311409)
                    ·
                      refine ⟨3323499428380795578983557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431332571174394105311409 3323499428380795578983557)
                      ·
                        rfl

theorem cell23_6472492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_6472492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472492 prefixEnd_6472492 := by exact prefixLift 6472492
  have htrace : WordTrace (prefixWord ++ tailWord_6472492) baseStart_6472492 baseEnd_6472492 := by
    simpa [prefixWord, tailWord_6472492, baseEnd_6472492] using wordTrace_append hprefix tailTrace_6472492
  have hstable : (prefixWord ++ tailWord_6472492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472492).length < 2 ^ (prefixWord ++ tailWord_6472492).sum := by decide
  have hdescent : baseEnd_6472492 < baseStart_6472492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472513 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6472513 : Nat := 118140960795 + 6472513 * 2 ^ 59
def prefixEnd_6472513 : Nat := 4983230072969 + 3 ^ 40 * 6472513 * 2
def baseEnd_6472513 : Nat := 3323510211474539996820961

theorem tailTrace_6472513 : CollatzResearch.WordTrace tailWord_6472513 prefixEnd_6472513 3323510211474539996820961 := by
  unfold tailWord_6472513
  simp only [CollatzResearch.WordTrace]
  refine ⟨236071943200198293058750193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157381295466798862039166795 236071943200198293058750193)
  ·
    refine ⟨177053957400148719794062645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236071943200198293058750193 177053957400148719794062645)
    ·
      refine ⟨16598808506263942480693373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177053957400148719794062645 16598808506263942480693373)
      ·
        refine ⟨6224553189848978430260015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16598808506263942480693373 6224553189848978430260015)
        ·
          refine ⟨9336829784773467645390023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224553189848978430260015 9336829784773467645390023)
          ·
            refine ⟨14005244677160201468085035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336829784773467645390023 14005244677160201468085035)
            ·
              refine ⟨21007867015740302202127553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14005244677160201468085035 21007867015740302202127553)
              ·
                refine ⟨15755900261805226651595665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21007867015740302202127553 15755900261805226651595665)
                ·
                  refine ⟨11816925196353919988696749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15755900261805226651595665 11816925196353919988696749)
                  ·
                    refine ⟨4431346948632719995761281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11816925196353919988696749 4431346948632719995761281)
                    ·
                      refine ⟨3323510211474539996820961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431346948632719995761281 3323510211474539996820961)
                      ·
                        rfl

theorem cell23_6472513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6472513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472513 prefixEnd_6472513 := by exact prefixLift 6472513
  have htrace : WordTrace (prefixWord ++ tailWord_6472513) baseStart_6472513 baseEnd_6472513 := by
    simpa [prefixWord, tailWord_6472513, baseEnd_6472513] using wordTrace_append hprefix tailTrace_6472513
  have hstable : (prefixWord ++ tailWord_6472513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472513).length < 2 ^ (prefixWord ++ tailWord_6472513).sum := by decide
  have hdescent : baseEnd_6472513 < baseStart_6472513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472545 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 4, 7]
def baseStart_6472545 : Nat := 118140960795 + 6472545 * 2 ^ 59
def prefixEnd_6472545 : Nat := 4983230072969 + 3 ^ 40 * 6472545 * 2
def baseEnd_6472545 : Nat := 1107842214285161290540271

theorem tailTrace_6472545 : CollatzResearch.WordTrace tailWord_6472545 prefixEnd_6472545 1107842214285161290540271 := by
  unfold tailWord_6472545
  simp only [CollatzResearch.WordTrace]
  refine ⟨236073110336082362523915089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157382073557388241682610059 236073110336082362523915089)
  ·
    refine ⟨177054832752061771892936317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236073110336082362523915089 177054832752061771892936317)
    ·
      refine ⟨66395562282023164459851119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177054832752061771892936317 66395562282023164459851119)
      ·
        refine ⟨99593343423034746689776679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66395562282023164459851119 99593343423034746689776679)
        ·
          refine ⟨149390015134552120034665019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99593343423034746689776679 149390015134552120034665019)
          ·
            refine ⟨224085022701828180051997529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149390015134552120034665019 224085022701828180051997529)
            ·
              refine ⟨168063767026371135038998147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224085022701828180051997529 168063767026371135038998147)
              ·
                refine ⟨252095650539556702558497221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168063767026371135038998147 252095650539556702558497221)
                ·
                  refine ⟨47267934476166881729718229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252095650539556702558497221 47267934476166881729718229)
                  ·
                    refine ⟨1107842214285161290540271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47267934476166881729718229 1107842214285161290540271)
                    ·
                      rfl

theorem cell23_6472545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_6472545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472545 prefixEnd_6472545 := by exact prefixLift 6472545
  have htrace : WordTrace (prefixWord ++ tailWord_6472545) baseStart_6472545 baseEnd_6472545 := by
    simpa [prefixWord, tailWord_6472545, baseEnd_6472545] using wordTrace_append hprefix tailTrace_6472545
  have hstable : (prefixWord ++ tailWord_6472545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472545).length < 2 ^ (prefixWord ++ tailWord_6472545).sum := by decide
  have hdescent : baseEnd_6472545 < baseStart_6472545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472546 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_6472546 : Nat := 118140960795 + 6472546 * 2 ^ 59
def prefixEnd_6472546 : Nat := 4983230072969 + 3 ^ 40 * 6472546 * 2
def baseEnd_6472546 : Nat := 3323527156336138367708309

theorem tailTrace_6472546 : CollatzResearch.WordTrace tailWord_6472546 prefixEnd_6472546 3323527156336138367708309 := by
  unfold tailWord_6472546
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018286702269684923675373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157382097872719159796467661 59018286702269684923675373)
  ·
    refine ⟨22131857513351131846378265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59018286702269684923675373 22131857513351131846378265)
    ·
      refine ⟨16598893135013348884783699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22131857513351131846378265 16598893135013348884783699)
      ·
        refine ⟨24898339702520023327175549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16598893135013348884783699 24898339702520023327175549)
        ·
          refine ⟨9336877388445008747690831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24898339702520023327175549 9336877388445008747690831)
          ·
            refine ⟨14005316082667513121536247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336877388445008747690831 14005316082667513121536247)
            ·
              refine ⟨21007974124001269682304371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14005316082667513121536247 21007974124001269682304371)
              ·
                refine ⟨31511961186001904523456557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21007974124001269682304371 31511961186001904523456557)
                ·
                  refine ⟨11816985444750714196296209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31511961186001904523456557 11816985444750714196296209)
                  ·
                    refine ⟨8862739083563035647222157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11816985444750714196296209 8862739083563035647222157)
                    ·
                      refine ⟨3323527156336138367708309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8862739083563035647222157 3323527156336138367708309)
                      ·
                        rfl

theorem cell23_6472546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_6472546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472546 prefixEnd_6472546 := by exact prefixLift 6472546
  have htrace : WordTrace (prefixWord ++ tailWord_6472546) baseStart_6472546 baseEnd_6472546 := by
    simpa [prefixWord, tailWord_6472546, baseEnd_6472546] using wordTrace_append hprefix tailTrace_6472546
  have hstable : (prefixWord ++ tailWord_6472546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472546).length < 2 ^ (prefixWord ++ tailWord_6472546).sum := by decide
  have hdescent : baseEnd_6472546 < baseStart_6472546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472555 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 5]
def baseStart_6472555 : Nat := 118140960795 + 6472555 * 2 ^ 59
def prefixEnd_6472555 : Nat := 4983230072969 + 3 ^ 40 * 6472555 * 2
def baseEnd_6472555 : Nat := 3323531777662028832495767

theorem tailTrace_6472555 : CollatzResearch.WordTrace tailWord_6472555 prefixEnd_6472555 3323531777662028832495767 := by
  unfold tailWord_6472555
  simp only [CollatzResearch.WordTrace]
  refine ⟨236073475066046134231779119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157382316710697422821186079 236073475066046134231779119)
  ·
    refine ⟨354110212599069201347668679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236073475066046134231779119 354110212599069201347668679)
    ·
      refine ⟨531165318898603802021503019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354110212599069201347668679 531165318898603802021503019)
      ·
        refine ⟨796747978347905703032254529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531165318898603802021503019 796747978347905703032254529)
        ·
          refine ⟨597560983760929277274190897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796747978347905703032254529 597560983760929277274190897)
          ·
            refine ⟨448170737820696957955643173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597560983760929277274190897 448170737820696957955643173)
            ·
              refine ⟨84032013341380679616683095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 448170737820696957955643173 84032013341380679616683095)
              ·
                refine ⟨126048020012071019425024643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84032013341380679616683095 126048020012071019425024643)
                ·
                  refine ⟨189072030018106529137536965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126048020012071019425024643 189072030018106529137536965)
                  ·
                    refine ⟨35451005628394974213288181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189072030018106529137536965 35451005628394974213288181)
                    ·
                      refine ⟨3323531777662028832495767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35451005628394974213288181 3323531777662028832495767)
                      ·
                        rfl

theorem cell23_6472555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_6472555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472555 prefixEnd_6472555 := by exact prefixLift 6472555
  have htrace : WordTrace (prefixWord ++ tailWord_6472555) baseStart_6472555 baseEnd_6472555 := by
    simpa [prefixWord, tailWord_6472555, baseEnd_6472555] using wordTrace_append hprefix tailTrace_6472555
  have hstable : (prefixWord ++ tailWord_6472555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472555).length < 2 ^ (prefixWord ++ tailWord_6472555).sum := by decide
  have hdescent : baseEnd_6472555 < baseStart_6472555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472586 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_6472586 : Nat := 118140960795 + 6472586 * 2 ^ 59
def prefixEnd_6472586 : Nat := 4983230072969 + 3 ^ 40 * 6472586 * 2
def baseEnd_6472586 : Nat := 3323547695562318211208125

theorem tailTrace_6472586 : CollatzResearch.WordTrace tailWord_6472586 prefixEnd_6472586 3323547695562318211208125 := by
  unfold tailWord_6472586
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018651432233456631539403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157383070485955884350771741 59018651432233456631539403)
  ·
    refine ⟨88527977148350184947309105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59018651432233456631539403 88527977148350184947309105)
    ·
      refine ⟨66395982861262638710481829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88527977148350184947309105 66395982861262638710481829)
      ·
        refine ⟨12449246786486744758215343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66395982861262638710481829 12449246786486744758215343)
        ·
          refine ⟨18673870179730117137323015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12449246786486744758215343 18673870179730117137323015)
          ·
            refine ⟨28010805269595175705984523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18673870179730117137323015 28010805269595175705984523)
            ·
              refine ⟨42016207904392763558976785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28010805269595175705984523 42016207904392763558976785)
              ·
                refine ⟨31512155928294572669232589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42016207904392763558976785 31512155928294572669232589)
                ·
                  refine ⟨11817058473110464750962221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31512155928294572669232589 11817058473110464750962221)
                  ·
                    refine ⟨4431396927416424281610833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11817058473110464750962221 4431396927416424281610833)
                    ·
                      refine ⟨3323547695562318211208125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431396927416424281610833 3323547695562318211208125)
                      ·
                        rfl

theorem cell23_6472586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_6472586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472586 prefixEnd_6472586 := by exact prefixLift 6472586
  have htrace : WordTrace (prefixWord ++ tailWord_6472586) baseStart_6472586 baseEnd_6472586 := by
    simpa [prefixWord, tailWord_6472586, baseEnd_6472586] using wordTrace_append hprefix tailTrace_6472586
  have hstable : (prefixWord ++ tailWord_6472586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472586).length < 2 ^ (prefixWord ++ tailWord_6472586).sum := by decide
  have hdescent : baseEnd_6472586 < baseStart_6472586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472612 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_6472612 : Nat := 118140960795 + 6472612 * 2 ^ 59
def prefixEnd_6472612 : Nat := 4983230072969 + 3 ^ 40 * 6472612 * 2
def baseEnd_6472612 : Nat := 3323561046059335109483005

theorem tailTrace_6472612 : CollatzResearch.WordTrace tailWord_6472612 prefixEnd_6472612 3323561046059335109483005 := by
  unfold tailWord_6472612
  simp only [CollatzResearch.WordTrace]
  refine ⟨118037777013419816483302045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157383702684559755311069393 118037777013419816483302045)
  ·
    refine ⟨44264166380032431181238267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118037777013419816483302045 44264166380032431181238267)
    ·
      refine ⟨66396249570048646771857401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44264166380032431181238267 66396249570048646771857401)
      ·
        refine ⟨49797187177536485078893051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66396249570048646771857401 49797187177536485078893051)
        ·
          refine ⟨74695780766304727618339577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49797187177536485078893051 74695780766304727618339577)
          ·
            refine ⟨56021835574728545713754683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74695780766304727618339577 56021835574728545713754683)
            ·
              refine ⟨84032753362092818570632025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56021835574728545713754683 84032753362092818570632025)
              ·
                refine ⟨63024565021569613927974019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84032753362092818570632025 63024565021569613927974019)
                ·
                  refine ⟨94536847532354420891961029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63024565021569613927974019 94536847532354420891961029)
                  ·
                    refine ⟨17725658912316453917242693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94536847532354420891961029 17725658912316453917242693)
                    ·
                      refine ⟨3323561046059335109483005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17725658912316453917242693 3323561046059335109483005)
                      ·
                        rfl

theorem cell23_6472612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_6472612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472612 prefixEnd_6472612 := by exact prefixLift 6472612
  have htrace : WordTrace (prefixWord ++ tailWord_6472612) baseStart_6472612 baseEnd_6472612 := by
    simpa [prefixWord, tailWord_6472612, baseEnd_6472612] using wordTrace_append hprefix tailTrace_6472612
  have hstable : (prefixWord ++ tailWord_6472612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472612).length < 2 ^ (prefixWord ++ tailWord_6472612).sum := by decide
  have hdescent : baseEnd_6472612 < baseStart_6472612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472633 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 2, 2, 2]
def baseStart_6472633 : Nat := 118140960795 + 6472633 * 2 ^ 59
def prefixEnd_6472633 : Nat := 4983230072969 + 3 ^ 40 * 6472633 * 2
def baseEnd_6472633 : Nat := 3323571829153079527320409

theorem tailTrace_6472633 : CollatzResearch.WordTrace tailWord_6472633 prefixEnd_6472633 3323571829153079527320409 := by
  unfold tailWord_6472633
  simp only [CollatzResearch.WordTrace]
  refine ⟨236076319959763553553118553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157384213306509035702079035 236076319959763553553118553)
  ·
    refine ⟨177057239969822665164838915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236076319959763553553118553 177057239969822665164838915)
    ·
      refine ⟨265585859954733997747258373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177057239969822665164838915 265585859954733997747258373)
      ·
        refine ⟨49797348741512624577610945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265585859954733997747258373 49797348741512624577610945)
        ·
          refine ⟨37348011556134468433208209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49797348741512624577610945 37348011556134468433208209)
          ·
            refine ⟨28011008667100851324906157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37348011556134468433208209 28011008667100851324906157)
            ·
              refine ⟨10504128250162819246839809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28011008667100851324906157 10504128250162819246839809)
              ·
                refine ⟨7878096187622114435129857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10504128250162819246839809 7878096187622114435129857)
                ·
                  refine ⟨5908572140716585826347393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7878096187622114435129857 5908572140716585826347393)
                  ·
                    refine ⟨4431429105537439369760545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5908572140716585826347393 4431429105537439369760545)
                    ·
                      refine ⟨3323571829153079527320409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431429105537439369760545 3323571829153079527320409)
                      ·
                        rfl

theorem cell23_6472633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_6472633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472633 prefixEnd_6472633 := by exact prefixLift 6472633
  have htrace : WordTrace (prefixWord ++ tailWord_6472633) baseStart_6472633 baseEnd_6472633 := by
    simpa [prefixWord, tailWord_6472633, baseEnd_6472633] using wordTrace_append hprefix tailTrace_6472633
  have hstable : (prefixWord ++ tailWord_6472633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472633).length < 2 ^ (prefixWord ++ tailWord_6472633).sum := by decide
  have hdescent : baseEnd_6472633 < baseStart_6472633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472652 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_6472652 : Nat := 118140960795 + 6472652 * 2 ^ 59
def prefixEnd_6472652 : Nat := 4983230072969 + 3 ^ 40 * 6472652 * 2
def baseEnd_6472652 : Nat := 1107860528428504984327607

theorem tailTrace_6472652 : CollatzResearch.WordTrace tailWord_6472652 prefixEnd_6472652 1107860528428504984327607 := by
  unfold tailWord_6472652
  simp only [CollatzResearch.WordTrace]
  refine ⟨118038506473347359899030105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157384675297796479865373473 118038506473347359899030105)
  ·
    refine ⟨88528879855010519924272579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118038506473347359899030105 88528879855010519924272579)
    ·
      refine ⟨132793319782515779886408869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88528879855010519924272579 132793319782515779886408869)
      ·
        refine ⟨24898747459221708728701663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132793319782515779886408869 24898747459221708728701663)
        ·
          refine ⟨37348121188832563093052495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24898747459221708728701663 37348121188832563093052495)
          ·
            refine ⟨56022181783248844639578743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37348121188832563093052495 56022181783248844639578743)
            ·
              refine ⟨84033272674873266959368115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56022181783248844639578743 84033272674873266959368115)
              ·
                refine ⟨126049909012309900439052173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84033272674873266959368115 126049909012309900439052173)
                ·
                  refine ⟨47268715879616212664644565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126049909012309900439052173 47268715879616212664644565)
                  ·
                    refine ⟨1107860528428504984327607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47268715879616212664644565 1107860528428504984327607)
                    ·
                      rfl

theorem cell23_6472652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_6472652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472652 prefixEnd_6472652 := by exact prefixLift 6472652
  have htrace : WordTrace (prefixWord ++ tailWord_6472652) baseStart_6472652 baseEnd_6472652 := by
    simpa [prefixWord, tailWord_6472652, baseEnd_6472652] using wordTrace_append hprefix tailTrace_6472652
  have hstable : (prefixWord ++ tailWord_6472652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472652).length < 2 ^ (prefixWord ++ tailWord_6472652).sum := by decide
  have hdescent : baseEnd_6472652 < baseStart_6472652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472669 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_6472669 : Nat := 118140960795 + 6472669 * 2 ^ 59
def prefixEnd_6472669 : Nat := 4983230072969 + 3 ^ 40 * 6472669 * 2
def baseEnd_6472669 : Nat := 1107863438152213795490081

theorem tailTrace_6472669 : CollatzResearch.WordTrace tailWord_6472669 prefixEnd_6472669 1107863438152213795490081 := by
  unfold tailWord_6472669
  simp only [CollatzResearch.WordTrace]
  refine ⟨236077632987633131701429061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157385088658422087800952707 236077632987633131701429061)
  ·
    refine ⟨44264556185181212194017949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236077632987633131701429061 44264556185181212194017949)
    ·
      refine ⟨16599208569442954572756731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44264556185181212194017949 16599208569442954572756731)
      ·
        refine ⟨24898812854164431859135097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16599208569442954572756731 24898812854164431859135097)
        ·
          refine ⟨18674109640623323894351323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24898812854164431859135097 18674109640623323894351323)
          ·
            refine ⟨28011164460934985841526985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18674109640623323894351323 28011164460934985841526985)
            ·
              refine ⟨21008373345701239381145239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28011164460934985841526985 21008373345701239381145239)
              ·
                refine ⟨31512560018551859071717859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21008373345701239381145239 31512560018551859071717859)
                ·
                  refine ⟨47268840027827788607576789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31512560018551859071717859 47268840027827788607576789)
                  ·
                    refine ⟨1107863438152213795490081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47268840027827788607576789 1107863438152213795490081)
                    ·
                      rfl

theorem cell23_6472669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_6472669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472669 prefixEnd_6472669 := by exact prefixLift 6472669
  have htrace : WordTrace (prefixWord ++ tailWord_6472669) baseStart_6472669 baseEnd_6472669 := by
    simpa [prefixWord, tailWord_6472669, baseEnd_6472669] using wordTrace_append hprefix tailTrace_6472669
  have hstable : (prefixWord ++ tailWord_6472669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472669).length < 2 ^ (prefixWord ++ tailWord_6472669).sum := by decide
  have hdescent : baseEnd_6472669 < baseStart_6472669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472686 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_6472686 : Nat := 118140960795 + 6472686 * 2 ^ 59
def prefixEnd_6472686 : Nat := 4983230072969 + 3 ^ 40 * 6472686 * 2
def baseEnd_6472686 : Nat := 1107866347875922606652555

theorem tailTrace_6472686 : CollatzResearch.WordTrace tailWord_6472686 prefixEnd_6472686 1107866347875922606652555 := by
  unfold tailWord_6472686
  simp only [CollatzResearch.WordTrace]
  refine ⟨29509781628571442950599739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157385502019047695736531941 29509781628571442950599739)
  ·
    refine ⟨44264672442857164425899609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29509781628571442950599739 44264672442857164425899609)
    ·
      refine ⟨33198504332142873319424707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44264672442857164425899609 33198504332142873319424707)
      ·
        refine ⟨49797756498214309979137061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33198504332142873319424707 49797756498214309979137061)
        ·
          refine ⟨9337079343415183121088199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49797756498214309979137061 9337079343415183121088199)
          ·
            refine ⟨14005619015122774681632299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9337079343415183121088199 14005619015122774681632299)
            ·
              refine ⟨21008428522684162022448449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14005619015122774681632299 21008428522684162022448449)
              ·
                refine ⟨15756321392013121516836337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21008428522684162022448449 15756321392013121516836337)
                ·
                  refine ⟨11817241044009841137627253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15756321392013121516836337 11817241044009841137627253)
                  ·
                    refine ⟨1107866347875922606652555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11817241044009841137627253 1107866347875922606652555)
                    ·
                      rfl

theorem cell23_6472686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_6472686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472686 prefixEnd_6472686 := by exact prefixLift 6472686
  have htrace : WordTrace (prefixWord ++ tailWord_6472686) baseStart_6472686 baseEnd_6472686 := by
    simpa [prefixWord, tailWord_6472686, baseEnd_6472686] using wordTrace_append hprefix tailTrace_6472686
  have hstable : (prefixWord ++ tailWord_6472686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472686).length < 2 ^ (prefixWord ++ tailWord_6472686).sum := by decide
  have hdescent : baseEnd_6472686 < baseStart_6472686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472689 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_6472689 : Nat := 118140960795 + 6472689 * 2 ^ 59
def prefixEnd_6472689 : Nat := 4983230072969 + 3 ^ 40 * 6472689 * 2
def baseEnd_6472689 : Nat := 3323600584069731308220151

theorem tailTrace_6472689 : CollatzResearch.WordTrace tailWord_6472689 prefixEnd_6472689 3323600584069731308220151 := by
  unfold tailWord_6472689
  simp only [CollatzResearch.WordTrace]
  refine ⟨236078362447560675117157121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157385574965040450078104747 236078362447560675117157121)
  ·
    refine ⟨177058771835670506337867841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236078362447560675117157121 177058771835670506337867841)
    ·
      refine ⟨132794078876752879753400881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177058771835670506337867841 132794078876752879753400881)
      ·
        refine ⟨99595559157564659815050661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132794078876752879753400881 99595559157564659815050661)
        ·
          refine ⟨18674167342043373715321999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99595559157564659815050661 18674167342043373715321999)
          ·
            refine ⟨28011251013065060572982999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18674167342043373715321999 28011251013065060572982999)
            ·
              refine ⟨42016876519597590859474499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28011251013065060572982999 42016876519597590859474499)
              ·
                refine ⟨63025314779396386289211749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42016876519597590859474499 63025314779396386289211749)
                ·
                  refine ⟨11817246521136822429227203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63025314779396386289211749 11817246521136822429227203)
                  ·
                    refine ⟨17725869781705233643840805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11817246521136822429227203 17725869781705233643840805)
                    ·
                      refine ⟨3323600584069731308220151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17725869781705233643840805 3323600584069731308220151)
                      ·
                        rfl

theorem cell23_6472689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_6472689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472689 prefixEnd_6472689 := by exact prefixLift 6472689
  have htrace : WordTrace (prefixWord ++ tailWord_6472689) baseStart_6472689 baseEnd_6472689 := by
    simpa [prefixWord, tailWord_6472689, baseEnd_6472689] using wordTrace_append hprefix tailTrace_6472689
  have hstable : (prefixWord ++ tailWord_6472689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472689).length < 2 ^ (prefixWord ++ tailWord_6472689).sum := by decide
  have hdescent : baseEnd_6472689 < baseStart_6472689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472690 : List Nat := [3, 2, 1, 5, 1, 1, 3, 2, 5]
def baseStart_6472690 : Nat := 118140960795 + 6472690 * 2 ^ 59
def prefixEnd_6472690 : Nat := 4983230072969 + 3 ^ 40 * 6472690 * 2
def baseEnd_6472690 : Nat := 369289010838931756034183

theorem tailTrace_6472690 : CollatzResearch.WordTrace tailWord_6472690 prefixEnd_6472690 369289010838931756034183 := by
  unfold tailWord_6472690
  simp only [CollatzResearch.WordTrace]
  refine ⟨59019599730139263071985881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157385599280371368191962349 59019599730139263071985881)
  ·
    refine ⟨44264699797604447303989411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59019599730139263071985881 44264699797604447303989411)
    ·
      refine ⟨66397049696406670955984117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44264699797604447303989411 66397049696406670955984117)
      ·
        refine ⟨6224723409038125402123511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66397049696406670955984117 6224723409038125402123511)
        ·
          refine ⟨9337085113557188103185267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224723409038125402123511 9337085113557188103185267)
          ·
            refine ⟨14005627670335782154777901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9337085113557188103185267 14005627670335782154777901)
            ·
              refine ⟨5252110376375918308041713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14005627670335782154777901 5252110376375918308041713)
              ·
                refine ⟨3939082782281938731031285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5252110376375918308041713 3939082782281938731031285)
                ·
                  refine ⟨369289010838931756034183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3939082782281938731031285 369289010838931756034183)
                  ·
                    rfl

theorem cell23_6472690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_6472690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472690 prefixEnd_6472690 := by exact prefixLift 6472690
  have htrace : WordTrace (prefixWord ++ tailWord_6472690) baseStart_6472690 baseEnd_6472690 := by
    simpa [prefixWord, tailWord_6472690, baseEnd_6472690] using wordTrace_append hprefix tailTrace_6472690
  have hstable : (prefixWord ++ tailWord_6472690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472690).length < 2 ^ (prefixWord ++ tailWord_6472690).sum := by decide
  have hdescent : baseEnd_6472690 < baseStart_6472690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472709 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_6472709 : Nat := 118140960795 + 6472709 * 2 ^ 59
def prefixEnd_6472709 : Nat := 4983230072969 + 3 ^ 40 * 6472709 * 2
def baseEnd_6472709 : Nat := 3323610853682821229970059

theorem tailTrace_6472709 : CollatzResearch.WordTrace tailWord_6472709 prefixEnd_6472709 3323610853682821229970059 := by
  unfold tailWord_6472709
  simp only [CollatzResearch.WordTrace]
  refine ⟨236079091907488218532885181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157386061271658812355256787 236079091907488218532885181)
  ·
    refine ⟨88529659465308081949831943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236079091907488218532885181 88529659465308081949831943)
    ·
      refine ⟨132794489197962122924747915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88529659465308081949831943 132794489197962122924747915)
      ·
        refine ⟨199191733796943184387121873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132794489197962122924747915 199191733796943184387121873)
        ·
          refine ⟨149393800347707388290341405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199191733796943184387121873 149393800347707388290341405)
          ·
            refine ⟨56022675130390270608878027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149393800347707388290341405 56022675130390270608878027)
            ·
              refine ⟨84034012695585405913317041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56022675130390270608878027 84034012695585405913317041)
              ·
                refine ⟨63025509521689054434987781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84034012695585405913317041 63025509521689054434987781)
                ·
                  refine ⟨11817283035316697706560209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63025509521689054434987781 11817283035316697706560209)
                  ·
                    refine ⟨8862962276487523279920157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11817283035316697706560209 8862962276487523279920157)
                    ·
                      refine ⟨3323610853682821229970059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8862962276487523279920157 3323610853682821229970059)
                      ·
                        rfl

theorem cell23_6472709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_6472709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472709 prefixEnd_6472709 := by exact prefixLift 6472709
  have htrace : WordTrace (prefixWord ++ tailWord_6472709) baseStart_6472709 baseEnd_6472709 := by
    simpa [prefixWord, tailWord_6472709, baseEnd_6472709] using wordTrace_append hprefix tailTrace_6472709
  have hstable : (prefixWord ++ tailWord_6472709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472709).length < 2 ^ (prefixWord ++ tailWord_6472709).sum := by decide
  have hdescent : baseEnd_6472709 < baseStart_6472709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472743 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6472743 : Nat := 118140960795 + 6472743 * 2 ^ 59
def prefixEnd_6472743 : Nat := 4983230072969 + 3 ^ 40 * 6472743 * 2
def baseEnd_6472743 : Nat := 3323628312025074096944903

theorem tailTrace_6472743 : CollatzResearch.WordTrace tailWord_6472743 prefixEnd_6472743 3323628312025074096944903 := by
  unfold tailWord_6472743
  simp only [CollatzResearch.WordTrace]
  refine ⟨236080331989365042339622883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157386887992910028226415255 236080331989365042339622883)
  ·
    refine ⟨354120497984047563509434325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236080331989365042339622883 354120497984047563509434325)
    ·
      refine ⟨8299699171501114769752367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 354120497984047563509434325 8299699171501114769752367)
      ·
        refine ⟨12449548757251672154628551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299699171501114769752367 12449548757251672154628551)
        ·
          refine ⟨18674323135877508231942827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12449548757251672154628551 18674323135877508231942827)
          ·
            refine ⟨28011484703816262347914241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18674323135877508231942827 28011484703816262347914241)
            ·
              refine ⟨21008613527862196760935681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28011484703816262347914241 21008613527862196760935681)
              ·
                refine ⟨15756460145896647570701761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21008613527862196760935681 15756460145896647570701761)
                ·
                  refine ⟨11817345109422485678026321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15756460145896647570701761 11817345109422485678026321)
                  ·
                    refine ⟨8863008832066864258519741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11817345109422485678026321 8863008832066864258519741)
                    ·
                      refine ⟨3323628312025074096944903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8863008832066864258519741 3323628312025074096944903)
                      ·
                        rfl

theorem cell23_6472743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6472743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472743 prefixEnd_6472743 := by exact prefixLift 6472743
  have htrace : WordTrace (prefixWord ++ tailWord_6472743) baseStart_6472743 baseEnd_6472743 := by
    simpa [prefixWord, tailWord_6472743, baseEnd_6472743] using wordTrace_append hprefix tailTrace_6472743
  have hstable : (prefixWord ++ tailWord_6472743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472743).length < 2 ^ (prefixWord ++ tailWord_6472743).sum := by decide
  have hdescent : baseEnd_6472743 < baseStart_6472743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472789 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_6472789 : Nat := 118140960795 + 6472789 * 2 ^ 59
def prefixEnd_6472789 : Nat := 4983230072969 + 3 ^ 40 * 6472789 * 2
def baseEnd_6472789 : Nat := 1107883977378393638989897

theorem tailTrace_6472789 : CollatzResearch.WordTrace tailWord_6472789 prefixEnd_6472789 1107883977378393638989897 := by
  unfold tailWord_6472789
  simp only [CollatzResearch.WordTrace]
  refine ⟨236082009747198392195797421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157388006498132261463864947 236082009747198392195797421)
  ·
    refine ⟨88530753655199397073424033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236082009747198392195797421 88530753655199397073424033)
    ·
      refine ⟨66398065241399547805068025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88530753655199397073424033 66398065241399547805068025)
      ·
        refine ⟨49798548931049660853801019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66398065241399547805068025 49798548931049660853801019)
        ·
          refine ⟨74697823396574491280701529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49798548931049660853801019 74697823396574491280701529)
          ·
            refine ⟨56023367547430868460526147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74697823396574491280701529 56023367547430868460526147)
            ·
              refine ⟨84035051321146302690789221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56023367547430868460526147 84035051321146302690789221)
              ·
                refine ⟨15756572122714931754522979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84035051321146302690789221 15756572122714931754522979)
                ·
                  refine ⟨23634858184072397631784469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15756572122714931754522979 23634858184072397631784469)
                  ·
                    refine ⟨1107883977378393638989897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23634858184072397631784469 1107883977378393638989897)
                    ·
                      rfl

theorem cell23_6472789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_6472789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472789 prefixEnd_6472789 := by exact prefixLift 6472789
  have htrace : WordTrace (prefixWord ++ tailWord_6472789) baseStart_6472789 baseEnd_6472789 := by
    simpa [prefixWord, tailWord_6472789, baseEnd_6472789] using wordTrace_append hprefix tailTrace_6472789
  have hstable : (prefixWord ++ tailWord_6472789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472789).length < 2 ^ (prefixWord ++ tailWord_6472789).sum := by decide
  have hdescent : baseEnd_6472789 < baseStart_6472789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472799 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_6472799 : Nat := 118140960795 + 6472799 * 2 ^ 59
def prefixEnd_6472799 : Nat := 4983230072969 + 3 ^ 40 * 6472799 * 2
def baseEnd_6472799 : Nat := 3323657066941725877844645

theorem tailTrace_6472799 : CollatzResearch.WordTrace tailWord_6472799 prefixEnd_6472799 3323657066941725877844645 := by
  unfold tailWord_6472799
  simp only [CollatzResearch.WordTrace]
  refine ⟨236082374477162163903661451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157388249651441442602440967 236082374477162163903661451)
  ·
    refine ⟨354123561715743245855492177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236082374477162163903661451 354123561715743245855492177)
    ·
      refine ⟨265592671286807434391619133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354123561715743245855492177 265592671286807434391619133)
      ·
        refine ⟨99597251732552787896857175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265592671286807434391619133 99597251732552787896857175)
        ·
          refine ⟨149395877598829181845285763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99597251732552787896857175 149395877598829181845285763)
          ·
            refine ⟨224093816398243772767928645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149395877598829181845285763 224093816398243772767928645)
            ·
              refine ⟨42017590574670707393986621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224093816398243772767928645 42017590574670707393986621)
              ·
                refine ⟨15756596465501515272744983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42017590574670707393986621 15756596465501515272744983)
                ·
                  refine ⟨23634894698252272909117475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15756596465501515272744983 23634894698252272909117475)
                  ·
                    refine ⟨35452342047378409363676213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23634894698252272909117475 35452342047378409363676213)
                    ·
                      refine ⟨3323657066941725877844645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35452342047378409363676213 3323657066941725877844645)
                      ·
                        rfl

theorem cell23_6472799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_6472799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472799 prefixEnd_6472799 := by exact prefixLift 6472799
  have htrace : WordTrace (prefixWord ++ tailWord_6472799) baseStart_6472799 baseEnd_6472799 := by
    simpa [prefixWord, tailWord_6472799, baseEnd_6472799] using wordTrace_append hprefix tailTrace_6472799
  have hstable : (prefixWord ++ tailWord_6472799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472799).length < 2 ^ (prefixWord ++ tailWord_6472799).sum := by decide
  have hdescent : baseEnd_6472799 < baseStart_6472799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472823 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 2, 4]
def baseStart_6472823 : Nat := 118140960795 + 6472823 * 2 ^ 59
def prefixEnd_6472823 : Nat := 4983230072969 + 3 ^ 40 * 6472823 * 2
def baseEnd_6472823 : Nat := 1107889796825811261314845

theorem tailTrace_6472823 : CollatzResearch.WordTrace tailWord_6472823 prefixEnd_6472823 1107889796825811261314845 := by
  unfold tailWord_6472823
  simp only [CollatzResearch.WordTrace]
  refine ⟨236083249829075216002535123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157388833219383477335023415 236083249829075216002535123)
  ·
    refine ⟨354124874743612824003802685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236083249829075216002535123 354124874743612824003802685)
    ·
      refine ⟨132796828028854809001426007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354124874743612824003802685 132796828028854809001426007)
      ·
        refine ⟨199195242043282213502139011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132796828028854809001426007 199195242043282213502139011)
        ·
          refine ⟨298792863064923320253208517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199195242043282213502139011 298792863064923320253208517)
          ·
            refine ⟨56023661824673122547476597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298792863064923320253208517 56023661824673122547476597)
            ·
              refine ⟨5252218296063105238825931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56023661824673122547476597 5252218296063105238825931)
              ·
                refine ⟨7878327444094657858238897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252218296063105238825931 7878327444094657858238897)
                ·
                  refine ⟨5908745583070993393679173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7878327444094657858238897 5908745583070993393679173)
                  ·
                    refine ⟨1107889796825811261314845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908745583070993393679173 1107889796825811261314845)
                    ·
                      rfl

theorem cell23_6472823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_6472823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472823 prefixEnd_6472823 := by exact prefixLift 6472823
  have htrace : WordTrace (prefixWord ++ tailWord_6472823) baseStart_6472823 baseEnd_6472823 := by
    simpa [prefixWord, tailWord_6472823, baseEnd_6472823] using wordTrace_append hprefix tailTrace_6472823
  have hstable : (prefixWord ++ tailWord_6472823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472823).length < 2 ^ (prefixWord ++ tailWord_6472823).sum := by decide
  have hdescent : baseEnd_6472823 < baseStart_6472823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472833 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_6472833 : Nat := 118140960795 + 6472833 * 2 ^ 59
def prefixEnd_6472833 : Nat := 4983230072969 + 3 ^ 40 * 6472833 * 2
def baseEnd_6472833 : Nat := 3323674525283978744819489

theorem tailTrace_6472833 : CollatzResearch.WordTrace tailWord_6472833 prefixEnd_6472833 3323674525283978744819489 := by
  unfold tailWord_6472833
  simp only [CollatzResearch.WordTrace]
  refine ⟨236083614559038987710399153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157389076372692658473599435 236083614559038987710399153)
  ·
    refine ⟨177062710919279240782799365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236083614559038987710399153 177062710919279240782799365)
    ·
      refine ⟨33199258297364857646774881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177062710919279240782799365 33199258297364857646774881)
      ·
        refine ⟨24899443723023643235081161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33199258297364857646774881 24899443723023643235081161)
        ·
          refine ⟨18674582792267732426310871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24899443723023643235081161 18674582792267732426310871)
          ·
            refine ⟨28011874188401598639466307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18674582792267732426310871 28011874188401598639466307)
            ·
              refine ⟨42017811282602397959199461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28011874188401598639466307 42017811282602397959199461)
              ·
                refine ⟨7878339615487949617349899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42017811282602397959199461 7878339615487949617349899)
                ·
                  refine ⟨11817509423231924426024849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7878339615487949617349899 11817509423231924426024849)
                  ·
                    refine ⟨8863132067423943319518637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11817509423231924426024849 8863132067423943319518637)
                    ·
                      refine ⟨3323674525283978744819489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8863132067423943319518637 3323674525283978744819489)
                      ·
                        rfl

theorem cell23_6472833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_6472833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472833 prefixEnd_6472833 := by exact prefixLift 6472833
  have htrace : WordTrace (prefixWord ++ tailWord_6472833) baseStart_6472833 baseEnd_6472833 := by
    simpa [prefixWord, tailWord_6472833, baseEnd_6472833] using wordTrace_append hprefix tailTrace_6472833
  have hstable : (prefixWord ++ tailWord_6472833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472833).length < 2 ^ (prefixWord ++ tailWord_6472833).sum := by decide
  have hdescent : baseEnd_6472833 < baseStart_6472833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472836 : List Nat := [2, 3, 2, 1, 2, 2, 4, 7]
def baseStart_6472836 : Nat := 118140960795 + 6472836 * 2 ^ 59
def prefixEnd_6472836 : Nat := 4983230072969 + 3 ^ 40 * 6472836 * 2
def baseEnd_6472836 : Nat := 123099113545405267891925

theorem tailTrace_6472836 : CollatzResearch.WordTrace tailWord_6472836 prefixEnd_6472836 123099113545405267891925 := by
  unfold tailWord_6472836
  simp only [CollatzResearch.WordTrace]
  refine ⟨118041861989014059611379181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157389149318685412815172241 118041861989014059611379181)
  ·
    refine ⟨44265698245880272354267193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118041861989014059611379181 44265698245880272354267193)
    ·
      refine ⟨33199273684410204265700395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44265698245880272354267193 33199273684410204265700395)
      ·
        refine ⟨49798910526615306398550593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33199273684410204265700395 49798910526615306398550593)
        ·
          refine ⟨37349182894961479798912945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49798910526615306398550593 37349182894961479798912945)
          ·
            refine ⟨28011887171221109849184709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37349182894961479798912945 28011887171221109849184709)
            ·
              refine ⟨5252228844603958096722133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28011887171221109849184709 5252228844603958096722133)
              ·
                refine ⟨123099113545405267891925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5252228844603958096722133 123099113545405267891925)
                ·
                  rfl

theorem cell23_6472836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 7].length) (baseStart_6472836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472836 prefixEnd_6472836 := by exact prefixLift 6472836
  have htrace : WordTrace (prefixWord ++ tailWord_6472836) baseStart_6472836 baseEnd_6472836 := by
    simpa [prefixWord, tailWord_6472836, baseEnd_6472836] using wordTrace_append hprefix tailTrace_6472836
  have hstable : (prefixWord ++ tailWord_6472836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472836).length < 2 ^ (prefixWord ++ tailWord_6472836).sum := by decide
  have hdescent : baseEnd_6472836 < baseStart_6472836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472879 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 2, 6]
def baseStart_6472879 : Nat := 118140960795 + 6472879 * 2 ^ 59
def prefixEnd_6472879 : Nat := 4983230072969 + 3 ^ 40 * 6472879 * 2
def baseEnd_6472879 : Nat := 1107899381798028521614759

theorem tailTrace_6472879 : CollatzResearch.WordTrace tailWord_6472879 prefixEnd_6472879 1107899381798028521614759 := by
  unfold tailWord_6472879
  simp only [CollatzResearch.WordTrace]
  refine ⟨236085292316872337566573691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157390194877914891711049127 236085292316872337566573691)
  ·
    refine ⟨354127938475308506349860537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236085292316872337566573691 354127938475308506349860537)
    ·
      refine ⟨265595953856481379762395403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354127938475308506349860537 265595953856481379762395403)
      ·
        refine ⟨398393930784722069643593105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265595953856481379762395403 398393930784722069643593105)
        ·
          refine ⟨298795448088541552232694829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398393930784722069643593105 298795448088541552232694829)
          ·
            refine ⟨112048293033203082087260561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298795448088541552232694829 112048293033203082087260561)
            ·
              refine ⟨84036219774902311565445421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112048293033203082087260561 84036219774902311565445421)
              ·
                refine ⟨31513582415588366837042033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84036219774902311565445421 31513582415588366837042033)
                ·
                  refine ⟨23635186811691275127781525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31513582415588366837042033 23635186811691275127781525)
                  ·
                    refine ⟨1107899381798028521614759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23635186811691275127781525 1107899381798028521614759)
                    ·
                      rfl

theorem cell23_6472879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_6472879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472879 prefixEnd_6472879 := by exact prefixLift 6472879
  have htrace : WordTrace (prefixWord ++ tailWord_6472879) baseStart_6472879 baseEnd_6472879 := by
    simpa [prefixWord, tailWord_6472879, baseEnd_6472879] using wordTrace_append hprefix tailTrace_6472879
  have hstable : (prefixWord ++ tailWord_6472879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472879).length < 2 ^ (prefixWord ++ tailWord_6472879).sum := by decide
  have hdescent : baseEnd_6472879 < baseStart_6472879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472899 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 4]
def baseStart_6472899 : Nat := 118140960795 + 6472899 * 2 ^ 59
def prefixEnd_6472899 : Nat := 4983230072969 + 3 ^ 40 * 6472899 * 2
def baseEnd_6472899 : Nat := 3323708415007175486594185

theorem tailTrace_6472899 : CollatzResearch.WordTrace tailWord_6472899 prefixEnd_6472899 3323708415007175486594185 := by
  unfold tailWord_6472899
  simp only [CollatzResearch.WordTrace]
  refine ⟨236086021776799880982301751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157390681184533253988201167 236086021776799880982301751)
  ·
    refine ⟨354129032665199821473452627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236086021776799880982301751 354129032665199821473452627)
    ·
      refine ⟨531193548997799732210178941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354129032665199821473452627 531193548997799732210178941)
      ·
        refine ⟨199197580874174899578817103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531193548997799732210178941 199197580874174899578817103)
        ·
          refine ⟨298796371311262349368225655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199197580874174899578817103 298796371311262349368225655)
          ·
            refine ⟨448194556966893524052338483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298796371311262349368225655 448194556966893524052338483)
            ·
              refine ⟨672291835450340286078507725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448194556966893524052338483 672291835450340286078507725)
              ·
                refine ⟨252109438293877607279440397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 672291835450340286078507725 252109438293877607279440397)
                ·
                  refine ⟨94541039360204102729790149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252109438293877607279440397 94541039360204102729790149)
                  ·
                    refine ⟨17726444880038269261835653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94541039360204102729790149 17726444880038269261835653)
                    ·
                      refine ⟨3323708415007175486594185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17726444880038269261835653 3323708415007175486594185)
                      ·
                        rfl

theorem cell23_6472899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_6472899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472899 prefixEnd_6472899 := by exact prefixLift 6472899
  have htrace : WordTrace (prefixWord ++ tailWord_6472899) baseStart_6472899 baseEnd_6472899 := by
    simpa [prefixWord, tailWord_6472899, baseEnd_6472899] using wordTrace_append hprefix tailTrace_6472899
  have hstable : (prefixWord ++ tailWord_6472899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472899).length < 2 ^ (prefixWord ++ tailWord_6472899).sum := by decide
  have hdescent : baseEnd_6472899 < baseStart_6472899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472903 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_6472903 : Nat := 118140960795 + 6472903 * 2 ^ 59
def prefixEnd_6472903 : Nat := 4983230072969 + 3 ^ 40 * 6472903 * 2
def baseEnd_6472903 : Nat := 3323710468929793470944167

theorem tailTrace_6472903 : CollatzResearch.WordTrace tailWord_6472903 prefixEnd_6472903 3323710468929793470944167 := by
  unfold tailWord_6472903
  simp only [CollatzResearch.WordTrace]
  refine ⟨236086167668785389665447363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157390778445856926443631575 236086167668785389665447363)
  ·
    refine ⟨354129251503178084498171045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236086167668785389665447363 354129251503178084498171045)
    ·
      refine ⟨66399234656845890843407071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354129251503178084498171045 66399234656845890843407071)
      ·
        refine ⟨99598851985268836265110607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66399234656845890843407071 99598851985268836265110607)
        ·
          refine ⟨149398277977903254397665911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99598851985268836265110607 149398277977903254397665911)
          ·
            refine ⟨224097416966854881596498867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149398277977903254397665911 224097416966854881596498867)
            ·
              refine ⟨336146125450282322394748301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224097416966854881596498867 336146125450282322394748301)
              ·
                refine ⟨126054797043855870898030613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336146125450282322394748301 126054797043855870898030613)
                ·
                  refine ⟨5908818611430743948345185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126054797043855870898030613 5908818611430743948345185)
                  ·
                    refine ⟨4431613958573057961258889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5908818611430743948345185 4431613958573057961258889)
                    ·
                      refine ⟨3323710468929793470944167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431613958573057961258889 3323710468929793470944167)
                      ·
                        rfl

theorem cell23_6472903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_6472903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472903 prefixEnd_6472903 := by exact prefixLift 6472903
  have htrace : WordTrace (prefixWord ++ tailWord_6472903) baseStart_6472903 baseEnd_6472903 := by
    simpa [prefixWord, tailWord_6472903, baseEnd_6472903] using wordTrace_append hprefix tailTrace_6472903
  have hstable : (prefixWord ++ tailWord_6472903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472903).length < 2 ^ (prefixWord ++ tailWord_6472903).sum := by decide
  have hdescent : baseEnd_6472903 < baseStart_6472903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472906 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_6472906 : Nat := 118140960795 + 6472906 * 2 ^ 59
def prefixEnd_6472906 : Nat := 4983230072969 + 3 ^ 40 * 6472906 * 2
def baseEnd_6472906 : Nat := 3323712009371756959206653

theorem tailTrace_6472906 : CollatzResearch.WordTrace tailWord_6472906 prefixEnd_6472906 3323712009371756959206653 := by
  unfold tailWord_6472906
  simp only [CollatzResearch.WordTrace]
  refine ⟨59021569271943630294451643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157390851391849680785204381 59021569271943630294451643)
  ·
    refine ⟨88532353907915445441677465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59021569271943630294451643 88532353907915445441677465)
    ·
      refine ⟨66399265430936584081258099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88532353907915445441677465 66399265430936584081258099)
      ·
        refine ⟨99598898146404876121887149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66399265430936584081258099 99598898146404876121887149)
        ·
          refine ⟨37349586804901828545707681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99598898146404876121887149 37349586804901828545707681)
          ·
            refine ⟨28012190103676371409280761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37349586804901828545707681 28012190103676371409280761)
            ·
              refine ⟨21009142577757278556960571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28012190103676371409280761 21009142577757278556960571)
              ·
                refine ⟨31513713866635917835440857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21009142577757278556960571 31513713866635917835440857)
                ·
                  refine ⟨23635285399976938376580643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31513713866635917835440857 23635285399976938376580643)
                  ·
                    refine ⟨35452928099965407564870965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23635285399976938376580643 35452928099965407564870965)
                    ·
                      refine ⟨3323712009371756959206653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35452928099965407564870965 3323712009371756959206653)
                      ·
                        rfl

theorem cell23_6472906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_6472906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472906 prefixEnd_6472906 := by exact prefixLift 6472906
  have htrace : WordTrace (prefixWord ++ tailWord_6472906) baseStart_6472906 baseEnd_6472906 := by
    simpa [prefixWord, tailWord_6472906, baseEnd_6472906] using wordTrace_append hprefix tailTrace_6472906
  have hstable : (prefixWord ++ tailWord_6472906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472906).length < 2 ^ (prefixWord ++ tailWord_6472906).sum := by decide
  have hdescent : baseEnd_6472906 < baseStart_6472906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472919 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_6472919 : Nat := 118140960795 + 6472919 * 2 ^ 59
def prefixEnd_6472919 : Nat := 4983230072969 + 3 ^ 40 * 6472919 * 2
def baseEnd_6472919 : Nat := 3323718684620265408344093

theorem tailTrace_6472919 : CollatzResearch.WordTrace tailWord_6472919 prefixEnd_6472919 3323718684620265408344093 := by
  unfold tailWord_6472919
  simp only [CollatzResearch.WordTrace]
  refine ⟨236086751236727424398029811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157391167491151616265353207 236086751236727424398029811)
  ·
    refine ⟨354130126855091136597044717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236086751236727424398029811 354130126855091136597044717)
    ·
      refine ⟨132798797570659176223891769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354130126855091136597044717 132798797570659176223891769)
      ·
        refine ⟨99599098177994382167918827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132798797570659176223891769 99599098177994382167918827)
        ·
          refine ⟨149398647266991573251878241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99599098177994382167918827 149398647266991573251878241)
          ·
            refine ⟨112048985450243679938908681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149398647266991573251878241 112048985450243679938908681)
            ·
              refine ⟨84036739087682759954181511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112048985450243679938908681 84036739087682759954181511)
              ·
                refine ⟨126055108631524139931272267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84036739087682759954181511 126055108631524139931272267)
                ·
                  refine ⟨189082662947286209896908401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126055108631524139931272267 189082662947286209896908401)
                  ·
                    refine ⟨141811997210464657422681301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189082662947286209896908401 141811997210464657422681301)
                    ·
                      refine ⟨3323718684620265408344093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141811997210464657422681301 3323718684620265408344093)
                      ·
                        rfl

theorem cell23_6472919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_6472919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472919 prefixEnd_6472919 := by exact prefixLift 6472919
  have htrace : WordTrace (prefixWord ++ tailWord_6472919) baseStart_6472919 baseEnd_6472919 := by
    simpa [prefixWord, tailWord_6472919, baseEnd_6472919] using wordTrace_append hprefix tailTrace_6472919
  have hstable : (prefixWord ++ tailWord_6472919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472919).length < 2 ^ (prefixWord ++ tailWord_6472919).sum := by decide
  have hdescent : baseEnd_6472919 < baseStart_6472919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6472933 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_6472933 : Nat := 118140960795 + 6472933 * 2 ^ 59
def prefixEnd_6472933 : Nat := 4983230072969 + 3 ^ 40 * 6472933 * 2
def baseEnd_6472933 : Nat := 3323725873349428353569029

theorem tailTrace_6472933 : CollatzResearch.WordTrace tailWord_6472933 prefixEnd_6472933 3323725873349428353569029 := by
  unfold tailWord_6472933
  simp only [CollatzResearch.WordTrace]
  refine ⟨236087261858676704789039453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157391507905784469859359635 236087261858676704789039453)
  ·
    refine ⟨88532723197003764295889795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236087261858676704789039453 88532723197003764295889795)
    ·
      refine ⟨132799084795505646443834693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88532723197003764295889795 132799084795505646443834693)
      ·
        refine ⟨24899828399157308708219005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132799084795505646443834693 24899828399157308708219005)
        ·
          refine ⟨9337435649683990765582127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24899828399157308708219005 9337435649683990765582127)
          ·
            refine ⟨14006153474525986148373191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9337435649683990765582127 14006153474525986148373191)
            ·
              refine ⟨21009230211788979222559787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14006153474525986148373191 21009230211788979222559787)
              ·
                refine ⟨31513845317683468833839681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21009230211788979222559787 31513845317683468833839681)
                ·
                  refine ⟨23635383988262601625379761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31513845317683468833839681 23635383988262601625379761)
                  ·
                    refine ⟨17726537991196951219034821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23635383988262601625379761 17726537991196951219034821)
                    ·
                      refine ⟨3323725873349428353569029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17726537991196951219034821 3323725873349428353569029)
                      ·
                        rfl

theorem cell23_6472933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_6472933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6472933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6472933 prefixEnd_6472933 := by exact prefixLift 6472933
  have htrace : WordTrace (prefixWord ++ tailWord_6472933) baseStart_6472933 baseEnd_6472933 := by
    simpa [prefixWord, tailWord_6472933, baseEnd_6472933] using wordTrace_append hprefix tailTrace_6472933
  have hstable : (prefixWord ++ tailWord_6472933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6472933).length < 2 ^ (prefixWord ++ tailWord_6472933).sum := by decide
  have hdescent : baseEnd_6472933 < baseStart_6472933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6472933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473013 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_6473013 : Nat := 118140960795 + 6473013 * 2 ^ 59
def prefixEnd_6473013 : Nat := 4983230072969 + 3 ^ 40 * 6473013 * 2
def baseEnd_6473013 : Nat := 3323766951801788040568661

theorem tailTrace_6473013 : CollatzResearch.WordTrace tailWord_6473013 prefixEnd_6473013 3323766951801788040568661 := by
  unfold tailWord_6473013
  simp only [CollatzResearch.WordTrace]
  refine ⟨236090179698386878451951693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157393453132257918967967795 236090179698386878451951693)
  ·
    refine ⟨88533817386895079419481885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236090179698386878451951693 88533817386895079419481885)
    ·
      refine ⟨33200181520085654782305707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88533817386895079419481885 33200181520085654782305707)
      ·
        refine ⟨49800272280128482173458561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33200181520085654782305707 49800272280128482173458561)
        ·
          refine ⟨37350204210096361630093921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49800272280128482173458561 37350204210096361630093921)
          ·
            refine ⟨28012653157572271222570441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37350204210096361630093921 28012653157572271222570441)
            ·
              refine ⟨21009489868179203416927831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28012653157572271222570441 21009489868179203416927831)
              ·
                refine ⟨31514234802268805125391747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21009489868179203416927831 31514234802268805125391747)
                ·
                  refine ⟨47271352203403207688087621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31514234802268805125391747 47271352203403207688087621)
                  ·
                    refine ⟨8863378538138101441516429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47271352203403207688087621 8863378538138101441516429)
                    ·
                      refine ⟨3323766951801788040568661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8863378538138101441516429 3323766951801788040568661)
                      ·
                        rfl

theorem cell23_6473013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_6473013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473013 prefixEnd_6473013 := by exact prefixLift 6473013
  have htrace : WordTrace (prefixWord ++ tailWord_6473013) baseStart_6473013 baseEnd_6473013 := by
    simpa [prefixWord, tailWord_6473013, baseEnd_6473013] using wordTrace_append hprefix tailTrace_6473013
  have hstable : (prefixWord ++ tailWord_6473013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473013).length < 2 ^ (prefixWord ++ tailWord_6473013).sum := by decide
  have hdescent : baseEnd_6473013 < baseStart_6473013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473093 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_6473093 : Nat := 118140960795 + 6473093 * 2 ^ 59
def prefixEnd_6473093 : Nat := 4983230072969 + 3 ^ 40 * 6473093 * 2
def baseEnd_6473093 : Nat := 1107936010084715909189431

theorem tailTrace_6473093 : CollatzResearch.WordTrace tailWord_6473093 prefixEnd_6473093 1107936010084715909189431 := by
  unfold tailWord_6473093
  simp only [CollatzResearch.WordTrace]
  refine ⟨236093097538097052114863933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157395398358731368076575955 236093097538097052114863933)
  ·
    refine ⟨88534911576786394543073975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236093097538097052114863933 88534911576786394543073975)
    ·
      refine ⟨132802367365179591814610963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88534911576786394543073975 132802367365179591814610963)
      ·
        refine ⟨199203551047769387721916445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132802367365179591814610963 199203551047769387721916445)
        ·
          refine ⟨74701331642913520395718667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199203551047769387721916445 74701331642913520395718667)
          ·
            refine ⟨112051997464370280593578001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74701331642913520395718667 112051997464370280593578001)
            ·
              refine ⟨84038998098277710445183501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112051997464370280593578001 84038998098277710445183501)
              ·
                refine ⟨31514624286854141416943813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84038998098277710445183501 31514624286854141416943813)
                ·
                  refine ⟨5908992053785151515676965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31514624286854141416943813 5908992053785151515676965)
                  ·
                    refine ⟨1107936010084715909189431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5908992053785151515676965 1107936010084715909189431)
                    ·
                      rfl

theorem cell23_6473093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_6473093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473093 prefixEnd_6473093 := by exact prefixLift 6473093
  have htrace : WordTrace (prefixWord ++ tailWord_6473093) baseStart_6473093 baseEnd_6473093 := by
    simpa [prefixWord, tailWord_6473093, baseEnd_6473093] using wordTrace_append hprefix tailTrace_6473093
  have hstable : (prefixWord ++ tailWord_6473093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473093).length < 2 ^ (prefixWord ++ tailWord_6473093).sum := by decide
  have hdescent : baseEnd_6473093 < baseStart_6473093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473113 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_6473113 : Nat := 118140960795 + 6473113 * 2 ^ 59
def prefixEnd_6473113 : Nat := 4983230072969 + 3 ^ 40 * 6473113 * 2
def baseEnd_6473113 : Nat := 3323818299867237649318201

theorem tailTrace_6473113 : CollatzResearch.WordTrace tailWord_6473113 prefixEnd_6473113 3323818299867237649318201 := by
  unfold tailWord_6473113
  simp only [CollatzResearch.WordTrace]
  refine ⟨236093826998024595530591993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157395884665349730353727995 236093826998024595530591993)
  ·
    refine ⟨177070370248518446647943995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236093826998024595530591993 177070370248518446647943995)
    ·
      refine ⟨265605555372777669971915993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177070370248518446647943995 265605555372777669971915993)
      ·
        refine ⟨199204166529583252478936995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265605555372777669971915993 199204166529583252478936995)
        ·
          refine ⟨298806249794374878718405493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199204166529583252478936995 298806249794374878718405493)
          ·
            refine ⟨28013085918222644879850515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298806249794374878718405493 28013085918222644879850515)
            ·
              refine ⟨42019628877333967319775773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28013085918222644879850515 42019628877333967319775773)
              ·
                refine ⟨15757360829000237744915915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42019628877333967319775773 15757360829000237744915915)
                ·
                  refine ⟨23636041243500356617373873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15757360829000237744915915 23636041243500356617373873)
                  ·
                    refine ⟨17727030932625267463030405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23636041243500356617373873 17727030932625267463030405)
                    ·
                      refine ⟨3323818299867237649318201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17727030932625267463030405 3323818299867237649318201)
                      ·
                        rfl

theorem cell23_6473113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_6473113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473113 prefixEnd_6473113 := by exact prefixLift 6473113
  have htrace : WordTrace (prefixWord ++ tailWord_6473113) baseStart_6473113 baseEnd_6473113 := by
    simpa [prefixWord, tailWord_6473113, baseEnd_6473113] using wordTrace_append hprefix tailTrace_6473113
  have hstable : (prefixWord ++ tailWord_6473113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473113).length < 2 ^ (prefixWord ++ tailWord_6473113).sum := by decide
  have hdescent : baseEnd_6473113 < baseStart_6473113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473117 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_6473117 : Nat := 118140960795 + 6473117 * 2 ^ 59
def prefixEnd_6473117 : Nat := 4983230072969 + 3 ^ 40 * 6473117 * 2
def baseEnd_6473117 : Nat := 3323820353789855633668183

theorem tailTrace_6473117 : CollatzResearch.WordTrace tailWord_6473117 prefixEnd_6473117 3323820353789855633668183 := by
  unfold tailWord_6473117
  simp only [CollatzResearch.WordTrace]
  refine ⟨236093972890010104213737605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157395981926673402809158403 236093972890010104213737605)
  ·
    refine ⟨44267619916876894540075801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236093972890010104213737605 44267619916876894540075801)
    ·
      refine ⟨33200714937657670905056851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44267619916876894540075801 33200714937657670905056851)
      ·
        refine ⟨49801072406486506357585277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33200714937657670905056851 49801072406486506357585277)
        ·
          refine ⟨18675402152432439884094479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49801072406486506357585277 18675402152432439884094479)
          ·
            refine ⟨28013103228648659826141719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18675402152432439884094479 28013103228648659826141719)
            ·
              refine ⟨42019654842972989739212579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28013103228648659826141719 42019654842972989739212579)
              ·
                refine ⟨63029482264459484608818869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42019654842972989739212579 63029482264459484608818869)
                ·
                  refine ⟨5909013962293076682076769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63029482264459484608818869 5909013962293076682076769)
                  ·
                    refine ⟨4431760471719807511557577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5909013962293076682076769 4431760471719807511557577)
                    ·
                      refine ⟨3323820353789855633668183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431760471719807511557577 3323820353789855633668183)
                      ·
                        rfl

theorem cell23_6473117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_6473117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473117 prefixEnd_6473117 := by exact prefixLift 6473117
  have htrace : WordTrace (prefixWord ++ tailWord_6473117) baseStart_6473117 baseEnd_6473117 := by
    simpa [prefixWord, tailWord_6473117, baseEnd_6473117] using wordTrace_append hprefix tailTrace_6473117
  have hstable : (prefixWord ++ tailWord_6473117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473117).length < 2 ^ (prefixWord ++ tailWord_6473117).sum := by decide
  have hdescent : baseEnd_6473117 < baseStart_6473117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473120 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 3]
def baseStart_6473120 : Nat := 118140960795 + 6473120 * 2 ^ 59
def prefixEnd_6473120 : Nat := 4983230072969 + 3 ^ 40 * 6473120 * 2
def baseEnd_6473120 : Nat := 3323821894231819121930669

theorem tailTrace_6473120 : CollatzResearch.WordTrace tailWord_6473120 prefixEnd_6473120 3323821894231819121930669 := by
  unfold tailWord_6473120
  simp only [CollatzResearch.WordTrace]
  refine ⟨118047041154499617863048407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157396054872666157150731209 118047041154499617863048407)
  ·
    refine ⟨177070561731749426794572611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118047041154499617863048407 177070561731749426794572611)
    ·
      refine ⟨265605842597624140191858917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177070561731749426794572611 265605842597624140191858917)
      ·
        refine ⟨49801095487054526285973547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265605842597624140191858917 49801095487054526285973547)
        ·
          refine ⟨74701643230581789428960321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49801095487054526285973547 74701643230581789428960321)
          ·
            refine ⟨56026232422936342071720241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74701643230581789428960321 56026232422936342071720241)
            ·
              refine ⟨42019674317202256553790181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56026232422936342071720241 42019674317202256553790181)
              ·
                refine ⟨7878688934475423103835659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42019674317202256553790181 7878688934475423103835659)
                ·
                  refine ⟨11818033401713134655753489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7878688934475423103835659 11818033401713134655753489)
                  ·
                    refine ⟨8863525051284850991815117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11818033401713134655753489 8863525051284850991815117)
                    ·
                      refine ⟨3323821894231819121930669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8863525051284850991815117 3323821894231819121930669)
                      ·
                        rfl

theorem cell23_6473120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_6473120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473120 prefixEnd_6473120 := by exact prefixLift 6473120
  have htrace : WordTrace (prefixWord ++ tailWord_6473120) baseStart_6473120 baseEnd_6473120 := by
    simpa [prefixWord, tailWord_6473120, baseEnd_6473120] using wordTrace_append hprefix tailTrace_6473120
  have hstable : (prefixWord ++ tailWord_6473120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473120).length < 2 ^ (prefixWord ++ tailWord_6473120).sum := by decide
  have hdescent : baseEnd_6473120 < baseStart_6473120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473123 : List Nat := [1, 1, 1, 4, 1, 3, 5, 7]
def baseStart_6473123 : Nat := 118140960795 + 6473123 * 2 ^ 59
def prefixEnd_6473123 : Nat := 4983230072969 + 3 ^ 40 * 6473123 * 2
def baseEnd_6473123 : Nat := 123104571654584541118265

theorem tailTrace_6473123 : CollatzResearch.WordTrace tailWord_6473123 prefixEnd_6473123 123104571654584541118265 := by
  unfold tailWord_6473123
  simp only [CollatzResearch.WordTrace]
  refine ⟨236094191727988367238456023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157396127818658911492304015 236094191727988367238456023)
  ·
    refine ⟨354141287591982550857684035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236094191727988367238456023 354141287591982550857684035)
    ·
      refine ⟨531211931387973826286526053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354141287591982550857684035 531211931387973826286526053)
      ·
        refine ⟨99602237135245092428723635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 531211931387973826286526053 99602237135245092428723635)
        ·
          refine ⟨149403355702867638643085453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99602237135245092428723635 149403355702867638643085453)
          ·
            refine ⟨56026258388575364491157045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149403355702867638643085453 56026258388575364491157045)
            ·
              refine ⟨5252461723928940421045973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56026258388575364491157045 5252461723928940421045973)
              ·
                refine ⟨123104571654584541118265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5252461723928940421045973 123104571654584541118265)
                ·
                  rfl

theorem cell23_6473123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 7].length) (baseStart_6473123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473123 prefixEnd_6473123 := by exact prefixLift 6473123
  have htrace : WordTrace (prefixWord ++ tailWord_6473123) baseStart_6473123 baseEnd_6473123 := by
    simpa [prefixWord, tailWord_6473123, baseEnd_6473123] using wordTrace_append hprefix tailTrace_6473123
  have hstable : (prefixWord ++ tailWord_6473123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473123).length < 2 ^ (prefixWord ++ tailWord_6473123).sum := by decide
  have hdescent : baseEnd_6473123 < baseStart_6473123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473136 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 1, 9]
def baseStart_6473136 : Nat := 118140960795 + 6473136 * 2 ^ 59
def prefixEnd_6473136 : Nat := 4983230072969 + 3 ^ 40 * 6473136 * 2
def baseEnd_6473136 : Nat := 1107943369974097019776865

theorem tailTrace_6473136 : CollatzResearch.WordTrace tailWord_6473136 prefixEnd_6473136 1107943369974097019776865 := by
  unfold tailWord_6473136
  simp only [CollatzResearch.WordTrace]
  refine ⟨118047332938470635229339631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157396443917960846972452841 118047332938470635229339631)
  ·
    refine ⟨177070999407705952844009447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118047332938470635229339631 177070999407705952844009447)
    ·
      refine ⟨265606499111558929266014171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177070999407705952844009447 265606499111558929266014171)
      ·
        refine ⟨398409748667338393899021257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265606499111558929266014171 398409748667338393899021257)
        ·
          refine ⟨298807311500503795424265943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398409748667338393899021257 298807311500503795424265943)
          ·
            refine ⟨448210967250755693136398915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298807311500503795424265943 448210967250755693136398915)
            ·
              refine ⟨672316450876133539704598373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448210967250755693136398915 672316450876133539704598373)
              ·
                refine ⟨126059334539275038694612195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672316450876133539704598373 126059334539275038694612195)
                ·
                  refine ⟨189089001808912558041918293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126059334539275038694612195 189089001808912558041918293)
                  ·
                    refine ⟨1107943369974097019776865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 189089001808912558041918293 1107943369974097019776865)
                    ·
                      rfl

theorem cell23_6473136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_6473136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473136 prefixEnd_6473136 := by exact prefixLift 6473136
  have htrace : WordTrace (prefixWord ++ tailWord_6473136) baseStart_6473136 baseEnd_6473136 := by
    simpa [prefixWord, tailWord_6473136, baseEnd_6473136] using wordTrace_append hprefix tailTrace_6473136
  have hstable : (prefixWord ++ tailWord_6473136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473136).length < 2 ^ (prefixWord ++ tailWord_6473136).sum := by decide
  have hdescent : baseEnd_6473136 < baseStart_6473136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473177 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 1, 3, 2]
def baseStart_6473177 : Nat := 118140960795 + 6473177 * 2 ^ 59
def prefixEnd_6473177 : Nat := 4983230072969 + 3 ^ 40 * 6473177 * 2
def baseEnd_6473177 : Nat := 3323851162629125398917907

theorem tailTrace_6473177 : CollatzResearch.WordTrace tailWord_6473177 prefixEnd_6473177 3323851162629125398917907 := by
  unfold tailWord_6473177
  simp only [CollatzResearch.WordTrace]
  refine ⟨236096161269792734460921785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157397440846528489640614523 236096161269792734460921785)
  ·
    refine ⟨177072120952344550845691339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236096161269792734460921785 177072120952344550845691339)
    ·
      refine ⟨265608181428516826268537009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177072120952344550845691339 265608181428516826268537009)
      ·
        refine ⟨199206136071387619701402757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265608181428516826268537009 199206136071387619701402757)
        ·
          refine ⟨37351150513385178694013017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199206136071387619701402757 37351150513385178694013017)
          ·
            refine ⟨28013362885038884020509763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37351150513385178694013017 28013362885038884020509763)
            ·
              refine ⟨42020044327558326030764645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28013362885038884020509763 42020044327558326030764645)
              ·
                refine ⟨7878758311417186130768371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42020044327558326030764645 7878758311417186130768371)
                ·
                  refine ⟨11818137467125779196152557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7878758311417186130768371 11818137467125779196152557)
                  ·
                    refine ⟨4431801550172167198557209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11818137467125779196152557 4431801550172167198557209)
                    ·
                      refine ⟨3323851162629125398917907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4431801550172167198557209 3323851162629125398917907)
                      ·
                        rfl

theorem cell23_6473177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_6473177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473177 prefixEnd_6473177 := by exact prefixLift 6473177
  have htrace : WordTrace (prefixWord ++ tailWord_6473177) baseStart_6473177 baseEnd_6473177 := by
    simpa [prefixWord, tailWord_6473177, baseEnd_6473177] using wordTrace_append hprefix tailTrace_6473177
  have hstable : (prefixWord ++ tailWord_6473177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473177).length < 2 ^ (prefixWord ++ tailWord_6473177).sum := by decide
  have hdescent : baseEnd_6473177 < baseStart_6473177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473203 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 4]
def baseStart_6473203 : Nat := 118140960795 + 6473203 * 2 ^ 59
def prefixEnd_6473203 : Nat := 4983230072969 + 3 ^ 40 * 6473203 * 2
def baseEnd_6473203 : Nat := 3323864513126142297192787

theorem tailTrace_6473203 : CollatzResearch.WordTrace tailWord_6473203 prefixEnd_6473203 3323864513126142297192787 := by
  unfold tailWord_6473203
  simp only [CollatzResearch.WordTrace]
  refine ⟨236097109567698540901368263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157398073045132360600912175 236097109567698540901368263)
  ·
    refine ⟨354145664351547811352052395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236097109567698540901368263 354145664351547811352052395)
    ·
      refine ⟨531218496527321717028078593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354145664351547811352052395 531218496527321717028078593)
      ·
        refine ⟨398413872395491287771058945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531218496527321717028078593 398413872395491287771058945)
        ·
          refine ⟨298810404296618465828294209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398413872395491287771058945 298810404296618465828294209)
          ·
            refine ⟨224107803222463849371220657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298810404296618465828294209 224107803222463849371220657)
            ·
              refine ⟨168080852416847887028415493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224107803222463849371220657 168080852416847887028415493)
              ·
                refine ⟨31515159828158978817827905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168080852416847887028415493 31515159828158978817827905)
                ·
                  refine ⟨23636369871119234113370929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31515159828158978817827905 23636369871119234113370929)
                  ·
                    refine ⟨17727277403339425585028197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23636369871119234113370929 17727277403339425585028197)
                    ·
                      refine ⟨3323864513126142297192787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17727277403339425585028197 3323864513126142297192787)
                      ·
                        rfl

theorem cell23_6473203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_6473203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473203 prefixEnd_6473203 := by exact prefixLift 6473203
  have htrace : WordTrace (prefixWord ++ tailWord_6473203) baseStart_6473203 baseEnd_6473203 := by
    simpa [prefixWord, tailWord_6473203, baseEnd_6473203] using wordTrace_append hprefix tailTrace_6473203
  have hstable : (prefixWord ++ tailWord_6473203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473203).length < 2 ^ (prefixWord ++ tailWord_6473203).sum := by decide
  have hdescent : baseEnd_6473203 < baseStart_6473203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473218 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_6473218 : Nat := 118140960795 + 6473218 * 2 ^ 59
def prefixEnd_6473218 : Nat := 4983230072969 + 3 ^ 40 * 6473218 * 2
def baseEnd_6473218 : Nat := 3323872215335959738505219

theorem tailTrace_6473218 : CollatzResearch.WordTrace tailWord_6473218 prefixEnd_6473218 3323872215335959738505219 := by
  unfold tailWord_6473218
  simp only [CollatzResearch.WordTrace]
  refine ⟨59024414165661049615791077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157398437775096132308776205 59024414165661049615791077)
  ·
    refine ⟨11067077656061446802960827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59024414165661049615791077 11067077656061446802960827)
    ·
      refine ⟨16600616484092170204441241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11067077656061446802960827 16600616484092170204441241)
      ·
        refine ⟨12450462363069127653330931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16600616484092170204441241 12450462363069127653330931)
        ·
          refine ⟨18675693544603691479996397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12450462363069127653330931 18675693544603691479996397)
          ·
            refine ⟨7003385079226384304998649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18675693544603691479996397 7003385079226384304998649)
            ·
              refine ⟨5252538809419788228748987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7003385079226384304998649 5252538809419788228748987)
              ·
                refine ⟨7878808214129682343123481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252538809419788228748987 7878808214129682343123481)
                ·
                  refine ⟨5909106160597261757342611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7878808214129682343123481 5909106160597261757342611)
                  ·
                    refine ⟨8863659240895892636013917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5909106160597261757342611 8863659240895892636013917)
                    ·
                      refine ⟨3323872215335959738505219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8863659240895892636013917 3323872215335959738505219)
                      ·
                        rfl

theorem cell23_6473218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_6473218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473218 prefixEnd_6473218 := by exact prefixLift 6473218
  have htrace : WordTrace (prefixWord ++ tailWord_6473218) baseStart_6473218 baseEnd_6473218 := by
    simpa [prefixWord, tailWord_6473218, baseEnd_6473218] using wordTrace_append hprefix tailTrace_6473218
  have hstable : (prefixWord ++ tailWord_6473218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473218).length < 2 ^ (prefixWord ++ tailWord_6473218).sum := by decide
  have hdescent : baseEnd_6473218 < baseStart_6473218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473337 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 6]
def baseStart_6473337 : Nat := 118140960795 + 6473337 * 2 ^ 59
def prefixEnd_6473337 : Nat := 4983230072969 + 3 ^ 40 * 6473337 * 2
def baseEnd_6473337 : Nat := 369325924392649419213019

theorem tailTrace_6473337 : CollatzResearch.WordTrace tailWord_6473337 prefixEnd_6473337 369325924392649419213019 := by
  unfold tailWord_6473337
  simp only [CollatzResearch.WordTrace]
  refine ⟨236101996949213081786746265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157401331299475387857830843 236101996949213081786746265)
  ·
    refine ⟨177076497711909811340059699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236101996949213081786746265 177076497711909811340059699)
    ·
      refine ⟨265614746567864717010089549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177076497711909811340059699 265614746567864717010089549)
      ·
        refine ⟨99605529962949268878783581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265614746567864717010089549 99605529962949268878783581)
        ·
          refine ⟨37352073736105975829543843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99605529962949268878783581 37352073736105975829543843)
          ·
            refine ⟨56028110604158963744315765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37352073736105975829543843 56028110604158963744315765)
            ·
              refine ⟨5252635369139902851029603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56028110604158963744315765 5252635369139902851029603)
              ·
                refine ⟨7878953053709854276544405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252635369139902851029603 7878953053709854276544405)
                ·
                  refine ⟨369325924392649419213019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7878953053709854276544405 369325924392649419213019)
                  ·
                    rfl

theorem cell23_6473337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 6].length) (baseStart_6473337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473337 prefixEnd_6473337 := by exact prefixLift 6473337
  have htrace : WordTrace (prefixWord ++ tailWord_6473337) baseStart_6473337 baseEnd_6473337 := by
    simpa [prefixWord, tailWord_6473337, baseEnd_6473337] using wordTrace_append hprefix tailTrace_6473337
  have hstable : (prefixWord ++ tailWord_6473337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473337).length < 2 ^ (prefixWord ++ tailWord_6473337).sum := by decide
  have hdescent : baseEnd_6473337 < baseStart_6473337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473367 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 1, 5]
def baseStart_6473367 : Nat := 118140960795 + 6473367 * 2 ^ 59
def prefixEnd_6473367 : Nat := 4983230072969 + 3 ^ 40 * 6473367 * 2
def baseEnd_6473367 : Nat := 1107982907984493218514011

theorem tailTrace_6473367 : CollatzResearch.WordTrace tailWord_6473367 prefixEnd_6473367 1107982907984493218514011 := by
  unfold tailWord_6473367
  simp only [CollatzResearch.WordTrace]
  refine ⟨236103091139104396910338355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157402060759402931273558903 236103091139104396910338355)
  ·
    refine ⟨354154636708656595365507533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236103091139104396910338355 354154636708656595365507533)
    ·
      refine ⟨132807988765746223262065325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354154636708656595365507533 132807988765746223262065325)
      ·
        refine ⟨49802995787154833723274497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132807988765746223262065325 49802995787154833723274497)
        ·
          refine ⟨37352246840366125292455873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49802995787154833723274497 37352246840366125292455873)
          ·
            refine ⟨28014185130274593969341905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37352246840366125292455873 28014185130274593969341905)
            ·
              refine ⟨21010638847705945477006429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28014185130274593969341905 21010638847705945477006429)
              ·
                refine ⟨7878989567889729553877411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21010638847705945477006429 7878989567889729553877411)
                ·
                  refine ⟨11818484351834594330816117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7878989567889729553877411 11818484351834594330816117)
                  ·
                    refine ⟨1107982907984493218514011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11818484351834594330816117 1107982907984493218514011)
                    ·
                      rfl

theorem cell23_6473367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_6473367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473367 prefixEnd_6473367 := by exact prefixLift 6473367
  have htrace : WordTrace (prefixWord ++ tailWord_6473367) baseStart_6473367 baseEnd_6473367 := by
    simpa [prefixWord, tailWord_6473367, baseEnd_6473367] using wordTrace_append hprefix tailTrace_6473367
  have hstable : (prefixWord ++ tailWord_6473367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473367).length < 2 ^ (prefixWord ++ tailWord_6473367).sum := by decide
  have hdescent : baseEnd_6473367 < baseStart_6473367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473400 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_6473400 : Nat := 118140960795 + 6473400 * 2 ^ 59
def prefixEnd_6473400 : Nat := 4983230072969 + 3 ^ 40 * 6473400 * 2
def baseEnd_6473400 : Nat := 3323965668815078026429381

theorem tailTrace_6473400 : CollatzResearch.WordTrace tailWord_6473400 prefixEnd_6473400 3323965668815078026429381 := by
  unfold tailWord_6473400
  simp only [CollatzResearch.WordTrace]
  refine ⟨118052147373992421773144827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157402863165323229030859769 118052147373992421773144827)
  ·
    refine ⟨177078221060988632659717241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118052147373992421773144827 177078221060988632659717241)
    ·
      refine ⟨132808665795741474494787931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177078221060988632659717241 132808665795741474494787931)
      ·
        refine ⟨199212998693612211742181897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132808665795741474494787931 199212998693612211742181897)
        ·
          refine ⟨149409749020209158806636423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199212998693612211742181897 149409749020209158806636423)
          ·
            refine ⟨224114623530313738209954635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149409749020209158806636423 224114623530313738209954635)
            ·
              refine ⟨336171935295470607314931953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224114623530313738209954635 336171935295470607314931953)
              ·
                refine ⟨252128951471602955486198965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336171935295470607314931953 252128951471602955486198965)
                ·
                  refine ⟨23637089200462777076831153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252128951471602955486198965 23637089200462777076831153)
                  ·
                    refine ⟨17727816900347082807623365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23637089200462777076831153 17727816900347082807623365)
                    ·
                      refine ⟨3323965668815078026429381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17727816900347082807623365 3323965668815078026429381)
                      ·
                        rfl

theorem cell23_6473400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_6473400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473400 prefixEnd_6473400 := by exact prefixLift 6473400
  have htrace : WordTrace (prefixWord ++ tailWord_6473400) baseStart_6473400 baseEnd_6473400 := by
    simpa [prefixWord, tailWord_6473400, baseEnd_6473400] using wordTrace_append hprefix tailTrace_6473400
  have hstable : (prefixWord ++ tailWord_6473400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473400).length < 2 ^ (prefixWord ++ tailWord_6473400).sum := by decide
  have hdescent : baseEnd_6473400 < baseStart_6473400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473404 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_6473404 : Nat := 118140960795 + 6473404 * 2 ^ 59
def prefixEnd_6473404 : Nat := 4983230072969 + 3 ^ 40 * 6473404 * 2
def baseEnd_6473404 : Nat := 3323967722737696010779363

theorem tailTrace_6473404 : CollatzResearch.WordTrace tailWord_6473404 prefixEnd_6473404 3323967722737696010779363 := by
  unfold tailWord_6473404
  simp only [CollatzResearch.WordTrace]
  refine ⟨118052220319985176114717633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157402960426646901486290177 118052220319985176114717633)
  ·
    refine ⟨88539165239988882086038225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118052220319985176114717633 88539165239988882086038225)
    ·
      refine ⟨66404373929991661564528669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88539165239988882086038225 66404373929991661564528669)
      ·
        refine ⟨24901640223746873086698251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66404373929991661564528669 24901640223746873086698251)
        ·
          refine ⟨37352460335620309630047377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24901640223746873086698251 37352460335620309630047377)
          ·
            refine ⟨28014345251715232222535533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37352460335620309630047377 28014345251715232222535533)
            ·
              refine ⟨10505379469393212083450825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28014345251715232222535533 10505379469393212083450825)
              ·
                refine ⟨7879034602044909062588119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10505379469393212083450825 7879034602044909062588119)
                ·
                  refine ⟨11818551903067363593882179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7879034602044909062588119 11818551903067363593882179)
                  ·
                    refine ⟨17727827854601045390823269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11818551903067363593882179 17727827854601045390823269)
                    ·
                      refine ⟨3323967722737696010779363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17727827854601045390823269 3323967722737696010779363)
                      ·
                        rfl

theorem cell23_6473404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_6473404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473404 prefixEnd_6473404 := by exact prefixLift 6473404
  have htrace : WordTrace (prefixWord ++ tailWord_6473404) baseStart_6473404 baseEnd_6473404 := by
    simpa [prefixWord, tailWord_6473404, baseEnd_6473404] using wordTrace_append hprefix tailTrace_6473404
  have hstable : (prefixWord ++ tailWord_6473404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473404).length < 2 ^ (prefixWord ++ tailWord_6473404).sum := by decide
  have hdescent : baseEnd_6473404 < baseStart_6473404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473407 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 3]
def baseStart_6473407 : Nat := 118140960795 + 6473407 * 2 ^ 59
def prefixEnd_6473407 : Nat := 4983230072969 + 3 ^ 40 * 6473407 * 2
def baseEnd_6473407 : Nat := 3323969263179659499041849

theorem tailTrace_6473407 : CollatzResearch.WordTrace tailWord_6473407 prefixEnd_6473407 3323969263179659499041849 := by
  unfold tailWord_6473407
  simp only [CollatzResearch.WordTrace]
  refine ⟨236104550058959483741794475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157403033372639655827862983 236104550058959483741794475)
  ·
    refine ⟨354156825088439225612691713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236104550058959483741794475 354156825088439225612691713)
    ·
      refine ⟨265617618816329419209518785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354156825088439225612691713 265617618816329419209518785)
      ·
        refine ⟨199213214112247064407139089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265617618816329419209518785 199213214112247064407139089)
        ·
          refine ⟨149409910584185298305354317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199213214112247064407139089 149409910584185298305354317)
          ·
            refine ⟨56028716469069486864507869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149409910584185298305354317 56028716469069486864507869)
            ·
              refine ⟨21010768675901057574190451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56028716469069486864507869 21010768675901057574190451)
              ·
                refine ⟨31516153013851586361285677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21010768675901057574190451 31516153013851586361285677)
                ·
                  refine ⟨11818557380194344885482129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31516153013851586361285677 11818557380194344885482129)
                  ·
                    refine ⟨8863918035145758664111597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11818557380194344885482129 8863918035145758664111597)
                    ·
                      refine ⟨3323969263179659499041849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8863918035145758664111597 3323969263179659499041849)
                      ·
                        rfl

theorem cell23_6473407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_6473407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473407 prefixEnd_6473407 := by exact prefixLift 6473407
  have htrace : WordTrace (prefixWord ++ tailWord_6473407) baseStart_6473407 baseEnd_6473407 := by
    simpa [prefixWord, tailWord_6473407, baseEnd_6473407] using wordTrace_append hprefix tailTrace_6473407
  have hstable : (prefixWord ++ tailWord_6473407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473407).length < 2 ^ (prefixWord ++ tailWord_6473407).sum := by decide
  have hdescent : baseEnd_6473407 < baseStart_6473407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473440 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 2, 7]
def baseStart_6473440 : Nat := 118140960795 + 6473440 * 2 ^ 59
def prefixEnd_6473440 : Nat := 4983230072969 + 3 ^ 40 * 6473440 * 2
def baseEnd_6473440 : Nat := 1107995402680419289976399

theorem tailTrace_6473440 : CollatzResearch.WordTrace tailWord_6473440 prefixEnd_6473440 1107995402680419289976399 := by
  unfold tailWord_6473440
  simp only [CollatzResearch.WordTrace]
  refine ⟨118052876833919965188872887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157403835778559953585163849 118052876833919965188872887)
  ·
    refine ⟨177079315250879947783309331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118052876833919965188872887 177079315250879947783309331)
    ·
      refine ⟨265618972876319921674963997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177079315250879947783309331 265618972876319921674963997)
      ·
        refine ⟨99607114828619970628111499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265618972876319921674963997 99607114828619970628111499)
        ·
          refine ⟨149410672242929955942167249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99607114828619970628111499 149410672242929955942167249)
          ·
            refine ⟨112058004182197466956625437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149410672242929955942167249 112058004182197466956625437)
            ·
              refine ⟨42021751568324050108734539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112058004182197466956625437 42021751568324050108734539)
              ·
                refine ⟨63032627352486075163101809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42021751568324050108734539 63032627352486075163101809)
                ·
                  refine ⟨47274470514364556372326357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63032627352486075163101809 47274470514364556372326357)
                  ·
                    refine ⟨1107995402680419289976399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47274470514364556372326357 1107995402680419289976399)
                    ·
                      rfl

theorem cell23_6473440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_6473440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473440 prefixEnd_6473440 := by exact prefixLift 6473440
  have htrace : WordTrace (prefixWord ++ tailWord_6473440) baseStart_6473440 baseEnd_6473440 := by
    simpa [prefixWord, tailWord_6473440, baseEnd_6473440] using wordTrace_append hprefix tailTrace_6473440
  have hstable : (prefixWord ++ tailWord_6473440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473440).length < 2 ^ (prefixWord ++ tailWord_6473440).sum := by decide
  have hdescent : baseEnd_6473440 < baseStart_6473440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473454 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_6473454 : Nat := 118140960795 + 6473454 * 2 ^ 59
def prefixEnd_6473454 : Nat := 4983230072969 + 3 ^ 40 * 6473454 * 2
def baseEnd_6473454 : Nat := 3323993396770420815154133

theorem tailTrace_6473454 : CollatzResearch.WordTrace tailWord_6473454 prefixEnd_6473454 3323993396770420815154133 := by
  unfold tailWord_6473454
  simp only [CollatzResearch.WordTrace]
  refine ⟨29513283036223651346094427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157404176193192807179170277 29513283036223651346094427)
  ·
    refine ⟨44269924554335477019141641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29513283036223651346094427 44269924554335477019141641)
    ·
      refine ⟨33202443415751607764356231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44269924554335477019141641 33202443415751607764356231)
      ·
        refine ⟨49803665123627411646534347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33202443415751607764356231 49803665123627411646534347)
        ·
          refine ⟨74705497685441117469801521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49803665123627411646534347 74705497685441117469801521)
          ·
            refine ⟨56029123264080838102351141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74705497685441117469801521 56029123264080838102351141)
            ·
              refine ⟨10505460612015157144190839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56029123264080838102351141 10505460612015157144190839)
              ·
                refine ⟨15758190918022735716286259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10505460612015157144190839 15758190918022735716286259)
                ·
                  refine ⟨23637286377034103574429389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15758190918022735716286259 23637286377034103574429389)
                  ·
                    refine ⟨8863982391387788840411021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23637286377034103574429389 8863982391387788840411021)
                    ·
                      refine ⟨3323993396770420815154133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8863982391387788840411021 3323993396770420815154133)
                      ·
                        rfl

theorem cell23_6473454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_6473454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473454 prefixEnd_6473454 := by exact prefixLift 6473454
  have htrace : WordTrace (prefixWord ++ tailWord_6473454) baseStart_6473454 baseEnd_6473454 := by
    simpa [prefixWord, tailWord_6473454, baseEnd_6473454] using wordTrace_append hprefix tailTrace_6473454
  have hstable : (prefixWord ++ tailWord_6473454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473454).length < 2 ^ (prefixWord ++ tailWord_6473454).sum := by decide
  have hdescent : baseEnd_6473454 < baseStart_6473454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473507 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 4]
def baseStart_6473507 : Nat := 118140960795 + 6473507 * 2 ^ 59
def prefixEnd_6473507 : Nat := 4983230072969 + 3 ^ 40 * 6473507 * 2
def baseEnd_6473507 : Nat := 3324020611245109107791389

theorem tailTrace_6473507 : CollatzResearch.WordTrace tailWord_6473507 prefixEnd_6473507 3324020611245109107791389 := by
  unfold tailWord_6473507
  simp only [CollatzResearch.WordTrace]
  refine ⟨236108197358597200820434775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157405464905731467213623183 236108197358597200820434775)
  ·
    refine ⟨354162296037895801230652163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236108197358597200820434775 354162296037895801230652163)
    ·
      refine ⟨531243444056843701845978245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354162296037895801230652163 531243444056843701845978245)
      ·
        refine ⟨99608145760658194096120921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 531243444056843701845978245 99608145760658194096120921)
        ·
          refine ⟨74706109320493645572090691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99608145760658194096120921 74706109320493645572090691)
          ·
            refine ⟨112059163980740468358136037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74706109320493645572090691 112059163980740468358136037)
            ·
              refine ⟨21011093246388837817150507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112059163980740468358136037 21011093246388837817150507)
              ·
                refine ⟨31516639869583256725725761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21011093246388837817150507 31516639869583256725725761)
                ·
                  refine ⟨23637479902187442544294321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31516639869583256725725761 23637479902187442544294321)
                  ·
                    refine ⟨17728109926640581908220741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23637479902187442544294321 17728109926640581908220741)
                    ·
                      refine ⟨3324020611245109107791389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17728109926640581908220741 3324020611245109107791389)
                      ·
                        rfl

theorem cell23_6473507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_6473507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473507 prefixEnd_6473507 := by exact prefixLift 6473507
  have htrace : WordTrace (prefixWord ++ tailWord_6473507) baseStart_6473507 baseEnd_6473507 := by
    simpa [prefixWord, tailWord_6473507, baseEnd_6473507] using wordTrace_append hprefix tailTrace_6473507
  have hstable : (prefixWord ++ tailWord_6473507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473507).length < 2 ^ (prefixWord ++ tailWord_6473507).sum := by decide
  have hdescent : baseEnd_6473507 < baseStart_6473507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473527 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_6473527 : Nat := 118140960795 + 6473527 * 2 ^ 59
def prefixEnd_6473527 : Nat := 4983230072969 + 3 ^ 40 * 6473527 * 2
def baseEnd_6473527 : Nat := 3324030880858199029541297

theorem tailTrace_6473527 : CollatzResearch.WordTrace tailWord_6473527 prefixEnd_6473527 3324030880858199029541297 := by
  unfold tailWord_6473527
  simp only [CollatzResearch.WordTrace]
  refine ⟨236108926818524744236162835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157405951212349829490775223 236108926818524744236162835)
  ·
    refine ⟨354163390227787116354244253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236108926818524744236162835 354163390227787116354244253)
    ·
      refine ⟨132811271335420168632841595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354163390227787116354244253 132811271335420168632841595)
      ·
        refine ⟨199216907003130252949262393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132811271335420168632841595 199216907003130252949262393)
        ·
          refine ⟨149412680252347689711946795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199216907003130252949262393 149412680252347689711946795)
          ·
            refine ⟨224119020378521534567920193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149412680252347689711946795 224119020378521534567920193)
            ·
              refine ⟨168089265283891150925940145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224119020378521534567920193 168089265283891150925940145)
              ·
                refine ⟨126066948962918363194455109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168089265283891150925940145 126066948962918363194455109)
                ·
                  refine ⟨23637552930547193098960333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126066948962918363194455109 23637552930547193098960333)
                  ·
                    refine ⟨8864082348955197412110125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23637552930547193098960333 8864082348955197412110125)
                    ·
                      refine ⟨3324030880858199029541297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8864082348955197412110125 3324030880858199029541297)
                      ·
                        rfl

theorem cell23_6473527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_6473527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473527 prefixEnd_6473527 := by exact prefixLift 6473527
  have htrace : WordTrace (prefixWord ++ tailWord_6473527) baseStart_6473527 baseEnd_6473527 := by
    simpa [prefixWord, tailWord_6473527, baseEnd_6473527] using wordTrace_append hprefix tailTrace_6473527
  have hstable : (prefixWord ++ tailWord_6473527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473527).length < 2 ^ (prefixWord ++ tailWord_6473527).sum := by decide
  have hdescent : baseEnd_6473527 < baseStart_6473527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473557 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_6473557 : Nat := 118140960795 + 6473557 * 2 ^ 59
def prefixEnd_6473557 : Nat := 4983230072969 + 3 ^ 40 * 6473557 * 2
def baseEnd_6473557 : Nat := 3324046285277833912166159

theorem tailTrace_6473557 : CollatzResearch.WordTrace tailWord_6473557 prefixEnd_6473557 3324046285277833912166159 := by
  unfold tailWord_6473557
  simp only [CollatzResearch.WordTrace]
  refine ⟨236110021008416059359754925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157406680672277372906503283 236110021008416059359754925)
  ·
    refine ⟨88541257878156022259908097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236110021008416059359754925 88541257878156022259908097)
    ·
      refine ⟨66405943408617016694931073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88541257878156022259908097 66405943408617016694931073)
      ·
        refine ⟨49804457556462762521198305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66405943408617016694931073 49804457556462762521198305)
        ·
          refine ⟨37353343167347071890898729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49804457556462762521198305 37353343167347071890898729)
          ·
            refine ⟨28015007375510303918174047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37353343167347071890898729 28015007375510303918174047)
            ·
              refine ⟨42022511063265455877261071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28015007375510303918174047 42022511063265455877261071)
              ·
                refine ⟨63033766594898183815891607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42022511063265455877261071 63033766594898183815891607)
                ·
                  refine ⟨94550649892347275723837411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63033766594898183815891607 94550649892347275723837411)
                  ·
                    refine ⟨141825974838520913585756117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94550649892347275723837411 141825974838520913585756117)
                    ·
                      refine ⟨3324046285277833912166159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141825974838520913585756117 3324046285277833912166159)
                      ·
                        rfl

theorem cell23_6473557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_6473557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473557 prefixEnd_6473557 := by exact prefixLift 6473557
  have htrace : WordTrace (prefixWord ++ tailWord_6473557) baseStart_6473557 baseEnd_6473557 := by
    simpa [prefixWord, tailWord_6473557, baseEnd_6473557] using wordTrace_append hprefix tailTrace_6473557
  have hstable : (prefixWord ++ tailWord_6473557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473557).length < 2 ^ (prefixWord ++ tailWord_6473557).sum := by decide
  have hdescent : baseEnd_6473557 < baseStart_6473557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473584 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 4, 4, 2]
def baseStart_6473584 : Nat := 118140960795 + 6473584 * 2 ^ 59
def prefixEnd_6473584 : Nat := 4983230072969 + 3 ^ 40 * 6473584 * 2
def baseEnd_6473584 : Nat := 3324060149255505306528535

theorem tailTrace_6473584 : CollatzResearch.WordTrace tailWord_6473584 prefixEnd_6473584 3324060149255505306528535 := by
  unfold tailWord_6473584
  simp only [CollatzResearch.WordTrace]
  refine ⟨118055502889659121485493903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157407337186212161980658537 118055502889659121485493903)
  ·
    refine ⟨177083254334488682228240855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118055502889659121485493903 177083254334488682228240855)
    ·
      refine ⟨265624881501733023342361283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177083254334488682228240855 265624881501733023342361283)
      ·
        refine ⟨398437322252599535013541925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265624881501733023342361283 398437322252599535013541925)
        ·
          refine ⟨74706997922362412815039111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398437322252599535013541925 74706997922362412815039111)
          ·
            refine ⟨112060496883543619222558667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74706997922362412815039111 112060496883543619222558667)
            ·
              refine ⟨168090745325315428833838001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112060496883543619222558667 168090745325315428833838001)
              ·
                refine ⟨126068058993986571625378501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168090745325315428833838001 126068058993986571625378501)
                ·
                  refine ⟨23637761061372482179758469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126068058993986571625378501 23637761061372482179758469)
                  ·
                    refine ⟨4432080199007340408704713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23637761061372482179758469 4432080199007340408704713)
                    ·
                      refine ⟨3324060149255505306528535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432080199007340408704713 3324060149255505306528535)
                      ·
                        rfl

theorem cell23_6473584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 4, 2].length) (baseStart_6473584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473584 prefixEnd_6473584 := by exact prefixLift 6473584
  have htrace : WordTrace (prefixWord ++ tailWord_6473584) baseStart_6473584 baseEnd_6473584 := by
    simpa [prefixWord, tailWord_6473584, baseEnd_6473584] using wordTrace_append hprefix tailTrace_6473584
  have hstable : (prefixWord ++ tailWord_6473584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473584).length < 2 ^ (prefixWord ++ tailWord_6473584).sum := by decide
  have hdescent : baseEnd_6473584 < baseStart_6473584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473597 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_6473597 : Nat := 118140960795 + 6473597 * 2 ^ 59
def prefixEnd_6473597 : Nat := 4983230072969 + 3 ^ 40 * 6473597 * 2
def baseEnd_6473597 : Nat := 3324066824504013755665975

theorem tailTrace_6473597 : CollatzResearch.WordTrace tailWord_6473597 prefixEnd_6473597 3324066824504013755665975 := by
  unfold tailWord_6473597
  simp only [CollatzResearch.WordTrace]
  refine ⟨236111479928271146191211045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157407653285514097460807363 236111479928271146191211045)
  ·
    refine ⟨44270902486550839910852071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236111479928271146191211045 44270902486550839910852071)
    ·
      refine ⟨66406353729826259866278107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44270902486550839910852071 66406353729826259866278107)
      ·
        refine ⟨99609530594739389799417161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66406353729826259866278107 99609530594739389799417161)
        ·
          refine ⟨74707147946054542349562871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99609530594739389799417161 74707147946054542349562871)
          ·
            refine ⟨112060721919081813524344307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74707147946054542349562871 112060721919081813524344307)
            ·
              refine ⟨168091082878622720286516461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112060721919081813524344307 168091082878622720286516461)
              ·
                refine ⟨63034156079483520107443673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168091082878622720286516461 63034156079483520107443673)
                ·
                  refine ⟨47275617059612640080582755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63034156079483520107443673 47275617059612640080582755)
                  ·
                    refine ⟨70913425589418960120874133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47275617059612640080582755 70913425589418960120874133)
                    ·
                      refine ⟨3324066824504013755665975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70913425589418960120874133 3324066824504013755665975)
                      ·
                        rfl

theorem cell23_6473597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_6473597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473597 prefixEnd_6473597 := by exact prefixLift 6473597
  have htrace : WordTrace (prefixWord ++ tailWord_6473597) baseStart_6473597 baseEnd_6473597 := by
    simpa [prefixWord, tailWord_6473597, baseEnd_6473597] using wordTrace_append hprefix tailTrace_6473597
  have hstable : (prefixWord ++ tailWord_6473597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473597).length < 2 ^ (prefixWord ++ tailWord_6473597).sum := by decide
  have hdescent : baseEnd_6473597 < baseStart_6473597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473618 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_6473618 : Nat := 118140960795 + 6473618 * 2 ^ 59
def prefixEnd_6473618 : Nat := 4983230072969 + 3 ^ 40 * 6473618 * 2
def baseEnd_6473618 : Nat := 3324077607597758173503379

theorem tailTrace_6473618 : CollatzResearch.WordTrace tailWord_6473618 prefixEnd_6473618 3324077607597758173503379 := by
  unfold tailWord_6473618
  simp only [CollatzResearch.WordTrace]
  refine ⟨59028061465298766694431377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157408163907463377851817005 59028061465298766694431377)
  ·
    refine ⟨44271046098974075020823533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59028061465298766694431377 44271046098974075020823533)
    ·
      refine ⟨16601642287115278132808825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44271046098974075020823533 16601642287115278132808825)
      ·
        refine ⟨12451231715336458599606619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16601642287115278132808825 12451231715336458599606619)
        ·
          refine ⟨18676847573004687899409929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12451231715336458599606619 18676847573004687899409929)
          ·
            refine ⟨14007635679753515924557447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18676847573004687899409929 14007635679753515924557447)
            ·
              refine ⟨21011453519630273886836171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14007635679753515924557447 21011453519630273886836171)
              ·
                refine ⟨31517180279445410830254257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21011453519630273886836171 31517180279445410830254257)
                ·
                  refine ⟨23637885209584058122690693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31517180279445410830254257 23637885209584058122690693)
                  ·
                    refine ⟨4432103476797010898004505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23637885209584058122690693 4432103476797010898004505)
                    ·
                      refine ⟨3324077607597758173503379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432103476797010898004505 3324077607597758173503379)
                      ·
                        rfl

theorem cell23_6473618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_6473618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473618 prefixEnd_6473618 := by exact prefixLift 6473618
  have htrace : WordTrace (prefixWord ++ tailWord_6473618) baseStart_6473618 baseEnd_6473618 := by
    simpa [prefixWord, tailWord_6473618, baseEnd_6473618] using wordTrace_append hprefix tailTrace_6473618
  have hstable : (prefixWord ++ tailWord_6473618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473618).length < 2 ^ (prefixWord ++ tailWord_6473618).sum := by decide
  have hdescent : baseEnd_6473618 < baseStart_6473618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473674 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_6473674 : Nat := 118140960795 + 6473674 * 2 ^ 59
def prefixEnd_6473674 : Nat := 4983230072969 + 3 ^ 40 * 6473674 * 2
def baseEnd_6473674 : Nat := 3324106362514409954403121

theorem tailTrace_6473674 : CollatzResearch.WordTrace tailWord_6473674 prefixEnd_6473674 3324106362514409954403121 := by
  unfold tailWord_6473674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59028572087248047085441019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157409525565994792227842717 59028572087248047085441019)
  ·
    refine ⟨88542858130872070628161529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59028572087248047085441019 88542858130872070628161529)
    ·
      refine ⟨66407143598154052971121147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88542858130872070628161529 66407143598154052971121147)
      ·
        refine ⟨99610715397231079456681721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66407143598154052971121147 99610715397231079456681721)
        ·
          refine ⟨74708036547923309592511291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99610715397231079456681721 74708036547923309592511291)
          ·
            refine ⟨112062054821884964388766937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74708036547923309592511291 112062054821884964388766937)
            ·
              refine ⟨84046541116413723291575203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112062054821884964388766937 84046541116413723291575203)
              ·
                refine ⟨126069811674620584937362805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84046541116413723291575203 126069811674620584937362805)
                ·
                  refine ⟨11819044844495679837877763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126069811674620584937362805 11819044844495679837877763)
                  ·
                    refine ⟨17728567266743519756816645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11819044844495679837877763 17728567266743519756816645)
                    ·
                      refine ⟨3324106362514409954403121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17728567266743519756816645 3324106362514409954403121)
                      ·
                        rfl

theorem cell23_6473674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_6473674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473674 prefixEnd_6473674 := by exact prefixLift 6473674
  have htrace : WordTrace (prefixWord ++ tailWord_6473674) baseStart_6473674 baseEnd_6473674 := by
    simpa [prefixWord, tailWord_6473674, baseEnd_6473674] using wordTrace_append hprefix tailTrace_6473674
  have hstable : (prefixWord ++ tailWord_6473674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473674).length < 2 ^ (prefixWord ++ tailWord_6473674).sum := by decide
  have hdescent : baseEnd_6473674 < baseStart_6473674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473704 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_6473704 : Nat := 118140960795 + 6473704 * 2 ^ 59
def prefixEnd_6473704 : Nat := 4983230072969 + 3 ^ 40 * 6473704 * 2
def baseEnd_6473704 : Nat := 3324121766934044837027983

theorem tailTrace_6473704 : CollatzResearch.WordTrace tailWord_6473704 prefixEnd_6473704 3324121766934044837027983 := by
  unfold tailWord_6473704
  simp only [CollatzResearch.WordTrace]
  refine ⟨118057691269441751732678083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157410255025922335643570777 118057691269441751732678083)
  ·
    refine ⟨177086536904162627599017125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118057691269441751732678083 177086536904162627599017125)
    ·
      refine ⟨33203725669530492674815711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177086536904162627599017125 33203725669530492674815711)
      ·
        refine ⟨49805588504295739012223567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33203725669530492674815711 49805588504295739012223567)
        ·
          refine ⟨74708382756443608518335351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49805588504295739012223567 74708382756443608518335351)
          ·
            refine ⟨112062574134665412777503027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74708382756443608518335351 112062574134665412777503027)
            ·
              refine ⟨168093861201998119166254541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112062574134665412777503027 168093861201998119166254541)
              ·
                refine ⟨63035197950749294687345453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168093861201998119166254541 63035197950749294687345453)
                ·
                  refine ⟨23638199231530985507754545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63035197950749294687345453 23638199231530985507754545)
                  ·
                    refine ⟨17728649423648239130815909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23638199231530985507754545 17728649423648239130815909)
                    ·
                      refine ⟨3324121766934044837027983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17728649423648239130815909 3324121766934044837027983)
                      ·
                        rfl

theorem cell23_6473704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_6473704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473704 prefixEnd_6473704 := by exact prefixLift 6473704
  have htrace : WordTrace (prefixWord ++ tailWord_6473704) baseStart_6473704 baseEnd_6473704 := by
    simpa [prefixWord, tailWord_6473704, baseEnd_6473704] using wordTrace_append hprefix tailTrace_6473704
  have hstable : (prefixWord ++ tailWord_6473704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473704).length < 2 ^ (prefixWord ++ tailWord_6473704).sum := by decide
  have hdescent : baseEnd_6473704 < baseStart_6473704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473711 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 3]
def baseStart_6473711 : Nat := 118140960795 + 6473711 * 2 ^ 59
def prefixEnd_6473711 : Nat := 4983230072969 + 3 ^ 40 * 6473711 * 2
def baseEnd_6473711 : Nat := 3324125361298626309640451

theorem tailTrace_6473711 : CollatzResearch.WordTrace tailWord_6473711 prefixEnd_6473711 3324125361298626309640451 := by
  unfold tailWord_6473711
  simp only [CollatzResearch.WordTrace]
  refine ⟨236115637849858143660860987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157410425233238762440573991 236115637849858143660860987)
  ·
    refine ⟨354173456774787215491291481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236115637849858143660860987 354173456774787215491291481)
    ·
      refine ⟨265630092581090411618468611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354173456774787215491291481 265630092581090411618468611)
      ·
        refine ⟨398445138871635617427702917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265630092581090411618468611 398445138871635617427702917)
        ·
          refine ⟨74708463538431678267694297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398445138871635617427702917 74708463538431678267694297)
          ·
            refine ⟨56031347653823758700770723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74708463538431678267694297 56031347653823758700770723)
            ·
              refine ⟨84047021480735638051156085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56031347653823758700770723 84047021480735638051156085)
              ·
                refine ⟨7879408263818966067295883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84047021480735638051156085 7879408263818966067295883)
                ·
                  refine ⟨11819112395728449100943825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7879408263818966067295883 11819112395728449100943825)
                  ·
                    refine ⟨8864334296796336825707869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11819112395728449100943825 8864334296796336825707869)
                    ·
                      refine ⟨3324125361298626309640451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8864334296796336825707869 3324125361298626309640451)
                      ·
                        rfl

theorem cell23_6473711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 3].length) (baseStart_6473711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473711 prefixEnd_6473711 := by exact prefixLift 6473711
  have htrace : WordTrace (prefixWord ++ tailWord_6473711) baseStart_6473711 baseEnd_6473711 := by
    simpa [prefixWord, tailWord_6473711, baseEnd_6473711] using wordTrace_append hprefix tailTrace_6473711
  have hstable : (prefixWord ++ tailWord_6473711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473711).length < 2 ^ (prefixWord ++ tailWord_6473711).sum := by decide
  have hdescent : baseEnd_6473711 < baseStart_6473711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473725 : List Nat := [1, 4, 1, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_6473725 : Nat := 118140960795 + 6473725 * 2 ^ 59
def prefixEnd_6473725 : Nat := 4983230072969 + 3 ^ 40 * 6473725 * 2
def baseEnd_6473725 : Nat := 3324132550027789254865387

theorem tailTrace_6473725 : CollatzResearch.WordTrace tailWord_6473725 prefixEnd_6473725 3324132550027789254865387 := by
  unfold tailWord_6473725
  simp only [CollatzResearch.WordTrace]
  refine ⟨236116148471807424051870629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157410765647871616034580419 236116148471807424051870629)
  ·
    refine ⟨44271777838463892009725743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236116148471807424051870629 44271777838463892009725743)
    ·
      refine ⟨66407666757695838014588615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44271777838463892009725743 66407666757695838014588615)
      ·
        refine ⟨99611500136543757021882923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66407666757695838014588615 99611500136543757021882923)
        ·
          refine ⟨149417250204815635532824385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99611500136543757021882923 149417250204815635532824385)
          ·
            refine ⟨112062937653611726649618289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149417250204815635532824385 112062937653611726649618289)
            ·
              refine ⟨84047203240208794987213717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112062937653611726649618289 84047203240208794987213717)
              ·
                refine ⟨3939712651884787265025643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84047203240208794987213717 3939712651884787265025643)
                ·
                  refine ⟨5909568977827180897538465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939712651884787265025643 5909568977827180897538465)
                  ·
                    refine ⟨4432176733370385673153849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5909568977827180897538465 4432176733370385673153849)
                    ·
                      refine ⟨3324132550027789254865387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432176733370385673153849 3324132550027789254865387)
                      ·
                        rfl

theorem cell23_6473725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_6473725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473725 prefixEnd_6473725 := by exact prefixLift 6473725
  have htrace : WordTrace (prefixWord ++ tailWord_6473725) baseStart_6473725 baseEnd_6473725 := by
    simpa [prefixWord, tailWord_6473725, baseEnd_6473725] using wordTrace_append hprefix tailTrace_6473725
  have hstable : (prefixWord ++ tailWord_6473725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473725).length < 2 ^ (prefixWord ++ tailWord_6473725).sum := by decide
  have hdescent : baseEnd_6473725 < baseStart_6473725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473735 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 2, 4]
def baseStart_6473735 : Nat := 118140960795 + 6473735 * 2 ^ 59
def prefixEnd_6473735 : Nat := 4983230072969 + 3 ^ 40 * 6473735 * 2
def baseEnd_6473735 : Nat := 1108045894944778071913447

theorem tailTrace_6473735 : CollatzResearch.WordTrace tailWord_6473735 prefixEnd_6473735 1108045894944778071913447 := by
  unfold tailWord_6473735
  simp only [CollatzResearch.WordTrace]
  refine ⟨236116513201771195759734659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157411008801180797173156439 236116513201771195759734659)
  ·
    refine ⟨354174769802656793639601989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236116513201771195759734659 354174769802656793639601989)
    ·
      refine ⟨66407769337998148807425373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354174769802656793639601989 66407769337998148807425373)
      ·
        refine ⟨24902913501749305802784515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66407769337998148807425373 24902913501749305802784515)
        ·
          refine ⟨37354370252623958704176773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24902913501749305802784515 37354370252623958704176773)
          ·
            refine ⟨7003944422366992257033145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37354370252623958704176773 7003944422366992257033145)
            ·
              refine ⟨5252958316775244192774859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7003944422366992257033145 5252958316775244192774859)
              ·
                refine ⟨7879437475162866289162289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252958316775244192774859 7879437475162866289162289)
                ·
                  refine ⟨5909578106372149716871717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7879437475162866289162289 5909578106372149716871717)
                  ·
                    refine ⟨1108045894944778071913447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5909578106372149716871717 1108045894944778071913447)
                    ·
                      rfl

theorem cell23_6473735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_6473735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473735 prefixEnd_6473735 := by exact prefixLift 6473735
  have htrace : WordTrace (prefixWord ++ tailWord_6473735) baseStart_6473735 baseEnd_6473735 := by
    simpa [prefixWord, tailWord_6473735, baseEnd_6473735] using wordTrace_append hprefix tailTrace_6473735
  have hstable : (prefixWord ++ tailWord_6473735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473735).length < 2 ^ (prefixWord ++ tailWord_6473735).sum := by decide
  have hdescent : baseEnd_6473735 < baseStart_6473735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473798 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6473798 : Nat := 118140960795 + 6473798 * 2 ^ 59
def prefixEnd_6473798 : Nat := 4983230072969 + 3 ^ 40 * 6473798 * 2
def baseEnd_6473798 : Nat := 3324170034115567469252551

theorem tailTrace_6473798 : CollatzResearch.WordTrace tailWord_6473798 prefixEnd_6473798 3324170034115567469252551 := by
  unfold tailWord_6473798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378712843766967422477439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157412540667028638346185365 7378712843766967422477439)
  ·
    refine ⟨11068069265650451133716159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7378712843766967422477439 11068069265650451133716159)
    ·
      refine ⟨16602103898475676700574239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11068069265650451133716159 16602103898475676700574239)
      ·
        refine ⟨24903155847713515050861359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16602103898475676700574239 24903155847713515050861359)
        ·
          refine ⟨37354733771570272576292039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24903155847713515050861359 37354733771570272576292039)
          ·
            refine ⟨56032100657355408864438059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37354733771570272576292039 56032100657355408864438059)
            ·
              refine ⟨84048150986033113296657089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56032100657355408864438059 84048150986033113296657089)
              ·
                refine ⟨63036113239524834972492817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84048150986033113296657089 63036113239524834972492817)
                ·
                  refine ⟨47277084929643626229369613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63036113239524834972492817 47277084929643626229369613)
                  ·
                    refine ⟨17728906848616359836013605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47277084929643626229369613 17728906848616359836013605)
                    ·
                      refine ⟨3324170034115567469252551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17728906848616359836013605 3324170034115567469252551)
                      ·
                        rfl

theorem cell23_6473798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6473798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473798 prefixEnd_6473798 := by exact prefixLift 6473798
  have htrace : WordTrace (prefixWord ++ tailWord_6473798) baseStart_6473798 baseEnd_6473798 := by
    simpa [prefixWord, tailWord_6473798, baseEnd_6473798] using wordTrace_append hprefix tailTrace_6473798
  have hstable : (prefixWord ++ tailWord_6473798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473798).length < 2 ^ (prefixWord ++ tailWord_6473798).sum := by decide
  have hdescent : baseEnd_6473798 < baseStart_6473798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473804 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 9]
def baseStart_6473804 : Nat := 118140960795 + 6473804 * 2 ^ 59
def prefixEnd_6473804 : Nat := 4983230072969 + 3 ^ 40 * 6473804 * 2
def baseEnd_6473804 : Nat := 369352568333277160641947

theorem tailTrace_6473804 : CollatzResearch.WordTrace tailWord_6473804 prefixEnd_6473804 369352568333277160641947 := by
  unfold tailWord_6473804
  simp only [CollatzResearch.WordTrace]
  refine ⟨118059514919260610271998233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157412686559014147029330977 118059514919260610271998233)
  ·
    refine ⟨88544636189445457703998675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118059514919260610271998233 88544636189445457703998675)
    ·
      refine ⟨132816954284168186555998013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88544636189445457703998675 132816954284168186555998013)
      ·
        refine ⟨49806357856563069958499255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132816954284168186555998013 49806357856563069958499255)
        ·
          refine ⟨74709536784844604937748883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49806357856563069958499255 74709536784844604937748883)
          ·
            refine ⟨112064305177266907406623325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74709536784844604937748883 112064305177266907406623325)
            ·
              refine ⟨42024114441475090277483747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112064305177266907406623325 42024114441475090277483747)
              ·
                refine ⟨63036171662212635416225621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42024114441475090277483747 63036171662212635416225621)
                ·
                  refine ⟨369352568333277160641947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63036171662212635416225621 369352568333277160641947)
                  ·
                    rfl

theorem cell23_6473804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_6473804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473804 prefixEnd_6473804 := by exact prefixLift 6473804
  have htrace : WordTrace (prefixWord ++ tailWord_6473804) baseStart_6473804 baseEnd_6473804 := by
    simpa [prefixWord, tailWord_6473804, baseEnd_6473804] using wordTrace_append hprefix tailTrace_6473804
  have hstable : (prefixWord ++ tailWord_6473804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473804).length < 2 ^ (prefixWord ++ tailWord_6473804).sum := by decide
  have hdescent : baseEnd_6473804 < baseStart_6473804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473831 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_6473831 : Nat := 118140960795 + 6473831 * 2 ^ 59
def prefixEnd_6473831 : Nat := 4983230072969 + 3 ^ 40 * 6473831 * 2
def baseEnd_6473831 : Nat := 3324186978977165840139899

theorem tailTrace_6473831 : CollatzResearch.WordTrace tailWord_6473831 prefixEnd_6473831 3324186978977165840139899 := by
  unfold tailWord_6473831
  simp only [CollatzResearch.WordTrace]
  refine ⟨236120014609423404155229347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157413343072948936103486231 236120014609423404155229347)
  ·
    refine ⟨354180021914135106232844021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236120014609423404155229347 354180021914135106232844021)
    ·
      refine ⟨33204377054450166209329127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 354180021914135106232844021 33204377054450166209329127)
      ·
        refine ⟨49806565581675249313993691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33204377054450166209329127 49806565581675249313993691)
        ·
          refine ⟨74709848372512873970990537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49806565581675249313993691 74709848372512873970990537)
          ·
            refine ⟨56032386279384655478242903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74709848372512873970990537 56032386279384655478242903)
            ·
              refine ⟨84048579419076983217364355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56032386279384655478242903 84048579419076983217364355)
              ·
                refine ⟨126072869128615474826046533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84048579419076983217364355 126072869128615474826046533)
                ·
                  refine ⟨23638662961615401529883725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126072869128615474826046533 23638662961615401529883725)
                  ·
                    refine ⟨8864498610605775573706397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23638662961615401529883725 8864498610605775573706397)
                    ·
                      refine ⟨3324186978977165840139899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8864498610605775573706397 3324186978977165840139899)
                      ·
                        rfl

theorem cell23_6473831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_6473831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473831 prefixEnd_6473831 := by exact prefixLift 6473831
  have htrace : WordTrace (prefixWord ++ tailWord_6473831) baseStart_6473831 baseEnd_6473831 := by
    simpa [prefixWord, tailWord_6473831, baseEnd_6473831] using wordTrace_append hprefix tailTrace_6473831
  have hstable : (prefixWord ++ tailWord_6473831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473831).length < 2 ^ (prefixWord ++ tailWord_6473831).sum := by decide
  have hdescent : baseEnd_6473831 < baseStart_6473831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473838 : List Nat := [4, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_6473838 : Nat := 118140960795 + 6473838 * 2 ^ 59
def prefixEnd_6473838 : Nat := 4983230072969 + 3 ^ 40 * 6473838 * 2
def baseEnd_6473838 : Nat := 369354508149083034750263

theorem tailTrace_6473838 : CollatzResearch.WordTrace tailWord_6473838 prefixEnd_6473838 369354508149083034750263 := by
  unfold tailWord_6473838
  simp only [CollatzResearch.WordTrace]
  refine ⟨29515033740049755543841771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157413513280265362900489445 29515033740049755543841771)
  ·
    refine ⟨44272550610074633315762657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29515033740049755543841771 44272550610074633315762657)
    ·
      refine ⟨33204412957555974986821993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44272550610074633315762657 33204412957555974986821993)
      ·
        refine ⟨24903309718166981240116495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33204412957555974986821993 24903309718166981240116495)
        ·
          refine ⟨37354964577250471860174743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24903309718166981240116495 37354964577250471860174743)
          ·
            refine ⟨56032446865875707790262115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37354964577250471860174743 56032446865875707790262115)
            ·
              refine ⟨84048670298813561685393173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56032446865875707790262115 84048670298813561685393173)
              ·
                refine ⟨3939781420256885704002805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84048670298813561685393173 3939781420256885704002805)
                ·
                  refine ⟨369354508149083034750263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3939781420256885704002805 369354508149083034750263)
                  ·
                    rfl

theorem cell23_6473838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_6473838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473838 prefixEnd_6473838 := by exact prefixLift 6473838
  have htrace : WordTrace (prefixWord ++ tailWord_6473838) baseStart_6473838 baseEnd_6473838 := by
    simpa [prefixWord, tailWord_6473838, baseEnd_6473838] using wordTrace_append hprefix tailTrace_6473838
  have hstable : (prefixWord ++ tailWord_6473838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473838).length < 2 ^ (prefixWord ++ tailWord_6473838).sum := by decide
  have hdescent : baseEnd_6473838 < baseStart_6473838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473881 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 5, 4]
def baseStart_6473881 : Nat := 118140960795 + 6473881 * 2 ^ 59
def prefixEnd_6473881 : Nat := 4983230072969 + 3 ^ 40 * 6473881 * 2
def baseEnd_6473881 : Nat := 1108070884336630214838223

theorem tailTrace_6473881 : CollatzResearch.WordTrace tailWord_6473881 prefixEnd_6473881 1108070884336630214838223 := by
  unfold tailWord_6473881
  simp only [CollatzResearch.WordTrace]
  refine ⟨236121838259242262694549497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157414558839494841796366331 236121838259242262694549497)
  ·
    refine ⟨177091378694431697020912123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236121838259242262694549497 177091378694431697020912123)
    ·
      refine ⟨265637068041647545531368185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177091378694431697020912123 265637068041647545531368185)
      ·
        refine ⟨199227801031235659148526139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265637068041647545531368185 199227801031235659148526139)
        ·
          refine ⟨298841701546853488722789209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199227801031235659148526139 298841701546853488722789209)
          ·
            refine ⟨224131276160140116542091907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298841701546853488722789209 224131276160140116542091907)
            ·
              refine ⟨336196914240210174813137861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224131276160140116542091907 336196914240210174813137861)
              ·
                refine ⟨63036921420039407777463349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336196914240210174813137861 63036921420039407777463349)
                ·
                  refine ⟨5909711383128694479137189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63036921420039407777463349 5909711383128694479137189)
                  ·
                    refine ⟨1108070884336630214838223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5909711383128694479137189 1108070884336630214838223)
                    ·
                      rfl

theorem cell23_6473881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 4].length) (baseStart_6473881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473881 prefixEnd_6473881 := by exact prefixLift 6473881
  have htrace : WordTrace (prefixWord ++ tailWord_6473881) baseStart_6473881 baseEnd_6473881 := by
    simpa [prefixWord, tailWord_6473881, baseEnd_6473881] using wordTrace_append hprefix tailTrace_6473881
  have hstable : (prefixWord ++ tailWord_6473881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473881).length < 2 ^ (prefixWord ++ tailWord_6473881).sum := by decide
  have hdescent : baseEnd_6473881 < baseStart_6473881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473888 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_6473888 : Nat := 118140960795 + 6473888 * 2 ^ 59
def prefixEnd_6473888 : Nat := 4983230072969 + 3 ^ 40 * 6473888 * 2
def baseEnd_6473888 : Nat := 3324216247374472117127137

theorem tailTrace_6473888 : CollatzResearch.WordTrace tailWord_6473888 prefixEnd_6473888 3324216247374472117127137 := by
  unfold tailWord_6473888
  simp only [CollatzResearch.WordTrace]
  refine ⟨118061046785108451445027159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157414729046811268593369545 118061046785108451445027159)
  ·
    refine ⟨177091570177662677167540739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118061046785108451445027159 177091570177662677167540739)
    ·
      refine ⟨265637355266494015751311109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177091570177662677167540739 265637355266494015751311109)
      ·
        refine ⟨49807004112467627953370833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265637355266494015751311109 49807004112467627953370833)
        ·
          refine ⟨37355253084350720965028125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49807004112467627953370833 37355253084350720965028125)
          ·
            refine ⟨14008219906631520361885547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37355253084350720965028125 14008219906631520361885547)
            ·
              refine ⟨21012329859947280542828321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14008219906631520361885547 21012329859947280542828321)
              ·
                refine ⟨15759247394960460407121241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21012329859947280542828321 15759247394960460407121241)
                ·
                  refine ⟨11819435546220345305340931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15759247394960460407121241 11819435546220345305340931)
                  ·
                    refine ⟨17729153319330517958011397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11819435546220345305340931 17729153319330517958011397)
                    ·
                      refine ⟨3324216247374472117127137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17729153319330517958011397 3324216247374472117127137)
                      ·
                        rfl

theorem cell23_6473888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_6473888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473888 prefixEnd_6473888 := by exact prefixLift 6473888
  have htrace : WordTrace (prefixWord ++ tailWord_6473888) baseStart_6473888 baseEnd_6473888 := by
    simpa [prefixWord, tailWord_6473888, baseEnd_6473888] using wordTrace_append hprefix tailTrace_6473888
  have hstable : (prefixWord ++ tailWord_6473888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473888).length < 2 ^ (prefixWord ++ tailWord_6473888).sum := by decide
  have hdescent : baseEnd_6473888 < baseStart_6473888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473922 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6473922 : Nat := 118140960795 + 6473922 * 2 ^ 59
def prefixEnd_6473922 : Nat := 4983230072969 + 3 ^ 40 * 6473922 * 2
def baseEnd_6473922 : Nat := 3324233705716724984101981

theorem tailTrace_6473922 : CollatzResearch.WordTrace tailWord_6473922 prefixEnd_6473922 3324233705716724984101981 := by
  unfold tailWord_6473922
  simp only [CollatzResearch.WordTrace]
  refine ⟨59030833413023431674198005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157415555768062484464528013 59030833413023431674198005)
  ·
    refine ⟨5534140632470946719456063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59030833413023431674198005 5534140632470946719456063)
    ·
      refine ⟨8301210948706420079184095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5534140632470946719456063 8301210948706420079184095)
      ·
        refine ⟨12451816423059630118776143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8301210948706420079184095 12451816423059630118776143)
        ·
          refine ⟨18677724634589445178164215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12451816423059630118776143 18677724634589445178164215)
          ·
            refine ⟨28016586951884167767246323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18677724634589445178164215 28016586951884167767246323)
            ·
              refine ⟨42024880427826251650869485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28016586951884167767246323 42024880427826251650869485)
              ·
                refine ⟨15759330160434844369076057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42024880427826251650869485 15759330160434844369076057)
                ·
                  refine ⟨11819497620326133276807043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15759330160434844369076057 11819497620326133276807043)
                  ·
                    refine ⟨17729246430489199915210565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11819497620326133276807043 17729246430489199915210565)
                    ·
                      refine ⟨3324233705716724984101981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17729246430489199915210565 3324233705716724984101981)
                      ·
                        rfl

theorem cell23_6473922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6473922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473922 prefixEnd_6473922 := by exact prefixLift 6473922
  have htrace : WordTrace (prefixWord ++ tailWord_6473922) baseStart_6473922 baseEnd_6473922 := by
    simpa [prefixWord, tailWord_6473922, baseEnd_6473922] using wordTrace_append hprefix tailTrace_6473922
  have hstable : (prefixWord ++ tailWord_6473922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473922).length < 2 ^ (prefixWord ++ tailWord_6473922).sum := by decide
  have hdescent : baseEnd_6473922 < baseStart_6473922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473942 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6473942 : Nat := 118140960795 + 6473942 * 2 ^ 59
def prefixEnd_6473942 : Nat := 4983230072969 + 3 ^ 40 * 6473942 * 2
def baseEnd_6473942 : Nat := 3324243975329814905851889

theorem tailTrace_6473942 : CollatzResearch.WordTrace tailWord_6473942 prefixEnd_6473942 3324243975329814905851889 := by
  unfold tailWord_6473942
  simp only [CollatzResearch.WordTrace]
  refine ⟨14757753944501329382032505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157416042074680846741680053 14757753944501329382032505)
  ·
    refine ⟨11068315458375997036524379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14757753944501329382032505 11068315458375997036524379)
    ·
      refine ⟨16602473187563995554786569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11068315458375997036524379 16602473187563995554786569)
      ·
        refine ⟨12451854890672996666089927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16602473187563995554786569 12451854890672996666089927)
        ·
          refine ⟨18677782336009494999134891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12451854890672996666089927 18677782336009494999134891)
          ·
            refine ⟨28016673504014242498702337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18677782336009494999134891 28016673504014242498702337)
            ·
              refine ⟨21012505128010681874026753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28016673504014242498702337 21012505128010681874026753)
              ·
                refine ⟨15759378846008011405520065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21012505128010681874026753 15759378846008011405520065)
                ·
                  refine ⟨11819534134506008554140049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15759378846008011405520065 11819534134506008554140049)
                  ·
                    refine ⟨8864650600879506415605037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11819534134506008554140049 8864650600879506415605037)
                    ·
                      refine ⟨3324243975329814905851889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8864650600879506415605037 3324243975329814905851889)
                      ·
                        rfl

theorem cell23_6473942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6473942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473942 prefixEnd_6473942 := by exact prefixLift 6473942
  have htrace : WordTrace (prefixWord ++ tailWord_6473942) baseStart_6473942 baseEnd_6473942 := by
    simpa [prefixWord, tailWord_6473942, baseEnd_6473942] using wordTrace_append hprefix tailTrace_6473942
  have hstable : (prefixWord ++ tailWord_6473942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473942).length < 2 ^ (prefixWord ++ tailWord_6473942).sum := by decide
  have hdescent : baseEnd_6473942 < baseStart_6473942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473949 : List Nat := [1, 4, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6473949 : Nat := 118140960795 + 6473949 * 2 ^ 59
def prefixEnd_6473949 : Nat := 4983230072969 + 3 ^ 40 * 6473949 * 2
def baseEnd_6473949 : Nat := 1108082523231465459488119

theorem tailTrace_6473949 : CollatzResearch.WordTrace tailWord_6473949 prefixEnd_6473949 1108082523231465459488119 := by
  unfold tailWord_6473949
  simp only [CollatzResearch.WordTrace]
  refine ⟨236124318422995910308024901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157416212281997273538683267 236124318422995910308024901)
  ·
    refine ⟨44273309704311733182754669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236124318422995910308024901 44273309704311733182754669)
    ·
      refine ⟨16602491139116899943533001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44273309704311733182754669 16602491139116899943533001)
      ·
        refine ⟨12451868354337674957649751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16602491139116899943533001 12451868354337674957649751)
        ·
          refine ⟨18677802531506512436474627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12451868354337674957649751 18677802531506512436474627)
          ·
            refine ⟨28016703797259768654711941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18677802531506512436474627 28016703797259768654711941)
            ·
              refine ⟨5253131961986206622758489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28016703797259768654711941 5253131961986206622758489)
              ·
                refine ⟨3939848971489654967068867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5253131961986206622758489 3939848971489654967068867)
                ·
                  refine ⟨5909773457234482450603301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939848971489654967068867 5909773457234482450603301)
                  ·
                    refine ⟨1108082523231465459488119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5909773457234482450603301 1108082523231465459488119)
                    ·
                      rfl

theorem cell23_6473949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6473949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473949 prefixEnd_6473949 := by exact prefixLift 6473949
  have htrace : WordTrace (prefixWord ++ tailWord_6473949) baseStart_6473949 baseEnd_6473949 := by
    simpa [prefixWord, tailWord_6473949, baseEnd_6473949] using wordTrace_append hprefix tailTrace_6473949
  have hstable : (prefixWord ++ tailWord_6473949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473949).length < 2 ^ (prefixWord ++ tailWord_6473949).sum := by decide
  have hdescent : baseEnd_6473949 < baseStart_6473949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473978 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_6473978 : Nat := 118140960795 + 6473978 * 2 ^ 59
def prefixEnd_6473978 : Nat := 4983230072969 + 3 ^ 40 * 6473978 * 2
def baseEnd_6473978 : Nat := 3324262460633376765001723

theorem tailTrace_6473978 : CollatzResearch.WordTrace tailWord_6473978 prefixEnd_6473978 3324262460633376765001723 := by
  unfold tailWord_6473978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59031344034972712065207647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157416917426593898840553725 59031344034972712065207647)
  ·
    refine ⟨88547016052459068097811471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59031344034972712065207647 88547016052459068097811471)
    ·
      refine ⟨132820524078688602146717207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88547016052459068097811471 132820524078688602146717207)
      ·
        refine ⟨199230786118032903220075811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132820524078688602146717207 199230786118032903220075811)
        ·
          refine ⟨298846179177049354830113717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199230786118032903220075811 298846179177049354830113717)
          ·
            refine ⟨28016829297848377015323161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298846179177049354830113717 28016829297848377015323161)
            ·
              refine ⟨21012621973386282761492371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28016829297848377015323161 21012621973386282761492371)
              ·
                refine ⟨31518932960079424142238557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21012621973386282761492371 31518932960079424142238557)
                ·
                  refine ⟨11819599860029784053339459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31518932960079424142238557 11819599860029784053339459)
                  ·
                    refine ⟨17729399790044676080009189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11819599860029784053339459 17729399790044676080009189)
                    ·
                      refine ⟨3324262460633376765001723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17729399790044676080009189 3324262460633376765001723)
                      ·
                        rfl

theorem cell23_6473978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_6473978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473978 prefixEnd_6473978 := by exact prefixLift 6473978
  have htrace : WordTrace (prefixWord ++ tailWord_6473978) baseStart_6473978 baseEnd_6473978 := by
    simpa [prefixWord, tailWord_6473978, baseEnd_6473978] using wordTrace_append hprefix tailTrace_6473978
  have hstable : (prefixWord ++ tailWord_6473978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473978).length < 2 ^ (prefixWord ++ tailWord_6473978).sum := by decide
  have hdescent : baseEnd_6473978 < baseStart_6473978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473992 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 1, 5]
def baseStart_6473992 : Nat := 118140960795 + 6473992 * 2 ^ 59
def prefixEnd_6473992 : Nat := 4983230072969 + 3 ^ 40 * 6473992 * 2
def baseEnd_6473992 : Nat := 1108089883120846570075553

theorem tailTrace_6473992 : CollatzResearch.WordTrace tailWord_6473992 prefixEnd_6473992 1108089883120846570075553 := by
  unfold tailWord_6473992
  simp only [CollatzResearch.WordTrace]
  refine ⟨118062943380920064325920115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157417257841226752434560153 118062943380920064325920115)
  ·
    refine ⟨177094415071380096488880173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118062943380920064325920115 177094415071380096488880173)
    ·
      refine ⟨66410405651767536183330065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177094415071380096488880173 66410405651767536183330065)
      ·
        refine ⟨49807804238825652137497549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66410405651767536183330065 49807804238825652137497549)
        ·
          refine ⟨18677926589559619551561581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49807804238825652137497549 18677926589559619551561581)
          ·
            refine ⟨7004222471084857331835593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18677926589559619551561581 7004222471084857331835593)
            ·
              refine ⟨5253166853313642998876695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7004222471084857331835593 5253166853313642998876695)
              ·
                refine ⟨7879750279970464498315043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253166853313642998876695 7879750279970464498315043)
                ·
                  refine ⟨11819625419955696747472565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7879750279970464498315043 11819625419955696747472565)
                  ·
                    refine ⟨1108089883120846570075553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11819625419955696747472565 1108089883120846570075553)
                    ·
                      rfl

theorem cell23_6473992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_6473992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473992 prefixEnd_6473992 := by exact prefixLift 6473992
  have htrace : WordTrace (prefixWord ++ tailWord_6473992) baseStart_6473992 baseEnd_6473992 := by
    simpa [prefixWord, tailWord_6473992, baseEnd_6473992] using wordTrace_append hprefix tailTrace_6473992
  have hstable : (prefixWord ++ tailWord_6473992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473992).length < 2 ^ (prefixWord ++ tailWord_6473992).sum := by decide
  have hdescent : baseEnd_6473992 < baseStart_6473992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473995 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 5, 2, 2]
def baseStart_6473995 : Nat := 118140960795 + 6473995 * 2 ^ 59
def prefixEnd_6473995 : Nat := 4983230072969 + 3 ^ 40 * 6473995 * 2
def baseEnd_6473995 : Nat := 3324271189804503198489145

theorem tailTrace_6473995 : CollatzResearch.WordTrace tailWord_6473995 prefixEnd_6473995 3324271189804503198489145 := by
  unfold tailWord_6473995
  simp only [CollatzResearch.WordTrace]
  refine ⟨236125996180829260164199439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157417330787219506776132959 236125996180829260164199439)
  ·
    refine ⟨354188994271243890246299159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236125996180829260164199439 354188994271243890246299159)
    ·
      refine ⟨531283491406865835369448739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354188994271243890246299159 531283491406865835369448739)
      ·
        refine ⟨796925237110298753054173109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531283491406865835369448739 796925237110298753054173109)
        ·
          refine ⟨74711740979090508098828729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 796925237110298753054173109 74711740979090508098828729)
          ·
            refine ⟨56033805734317881074121547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74711740979090508098828729 56033805734317881074121547)
            ·
              refine ⟨84050708601476821611182321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56033805734317881074121547 84050708601476821611182321)
              ·
                refine ⟨63038031451107616208386741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84050708601476821611182321 63038031451107616208386741)
                ·
                  refine ⟨5909815448541339019536257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63038031451107616208386741 5909815448541339019536257)
                  ·
                    refine ⟨4432361586406004264652193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5909815448541339019536257 4432361586406004264652193)
                    ·
                      refine ⟨3324271189804503198489145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432361586406004264652193 3324271189804503198489145)
                      ·
                        rfl

theorem cell23_6473995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 2, 2].length) (baseStart_6473995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473995 prefixEnd_6473995 := by exact prefixLift 6473995
  have htrace : WordTrace (prefixWord ++ tailWord_6473995) baseStart_6473995 baseEnd_6473995 := by
    simpa [prefixWord, tailWord_6473995, baseEnd_6473995] using wordTrace_append hprefix tailTrace_6473995
  have hstable : (prefixWord ++ tailWord_6473995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473995).length < 2 ^ (prefixWord ++ tailWord_6473995).sum := by decide
  have hdescent : baseEnd_6473995 < baseStart_6473995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6473998 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6473998 : Nat := 118140960795 + 6473998 * 2 ^ 59
def prefixEnd_6473998 : Nat := 4983230072969 + 3 ^ 40 * 6473998 * 2
def baseEnd_6473998 : Nat := 3324272730246466686751631

theorem tailTrace_6473998 : CollatzResearch.WordTrace tailWord_6473998 prefixEnd_6473998 3324272730246466686751631 := by
  unfold tailWord_6473998
  simp only [CollatzResearch.WordTrace]
  refine ⟨29515763199977298959569831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157417403733212261117705765 29515763199977298959569831)
  ·
    refine ⟨44273644799965948439354747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29515763199977298959569831 44273644799965948439354747)
    ·
      refine ⟨66410467199948922659032121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44273644799965948439354747 66410467199948922659032121)
      ·
        refine ⟨49807850399961691994274091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66410467199948922659032121 49807850399961691994274091)
        ·
          refine ⟨74711775599942537991411137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49807850399961691994274091 74711775599942537991411137)
          ·
            refine ⟨56033831699956903493558353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74711775599942537991411137 56033831699956903493558353)
            ·
              refine ⟨42025373774967677620168765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56033831699956903493558353 42025373774967677620168765)
              ·
                refine ⟨15759515165612879107563287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42025373774967677620168765 15759515165612879107563287)
                ·
                  refine ⟨23639272748419318661344931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15759515165612879107563287 23639272748419318661344931)
                  ·
                    refine ⟨35458909122628977992017397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23639272748419318661344931 35458909122628977992017397)
                    ·
                      refine ⟨3324272730246466686751631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35458909122628977992017397 3324272730246466686751631)
                      ·
                        rfl

theorem cell23_6473998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6473998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6473998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6473998 prefixEnd_6473998 := by exact prefixLift 6473998
  have htrace : WordTrace (prefixWord ++ tailWord_6473998) baseStart_6473998 baseEnd_6473998 := by
    simpa [prefixWord, tailWord_6473998, baseEnd_6473998] using wordTrace_append hprefix tailTrace_6473998
  have hstable : (prefixWord ++ tailWord_6473998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6473998).length < 2 ^ (prefixWord ++ tailWord_6473998).sum := by decide
  have hdescent : baseEnd_6473998 < baseStart_6473998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6473998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474001 : List Nat := [1, 2, 2, 1, 1, 6, 10]
def baseStart_6474001 : Nat := 118140960795 + 6474001 * 2 ^ 59
def prefixEnd_6474001 : Nat := 4983230072969 + 3 ^ 40 * 6474001 * 2
def baseEnd_6474001 : Nat := 41040423094918891049557

theorem tailTrace_6474001 : CollatzResearch.WordTrace tailWord_6474001 prefixEnd_6474001 41040423094918891049557 := by
  unfold tailWord_6474001
  simp only [CollatzResearch.WordTrace]
  refine ⟨236126215018807523188917857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157417476679205015459278571 236126215018807523188917857)
  ·
    refine ⟨177094661264105642391688393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236126215018807523188917857 177094661264105642391688393)
    ·
      refine ⟨132820995948079231793766295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177094661264105642391688393 132820995948079231793766295)
      ·
        refine ⟨199231493922118847690649443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132820995948079231793766295 199231493922118847690649443)
        ·
          refine ⟨298847240883178271535974165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199231493922118847690649443 298847240883178271535974165)
          ·
            refine ⟨14008464416398981478248789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 298847240883178271535974165 14008464416398981478248789)
            ·
              refine ⟨41040423094918891049557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14008464416398981478248789 41040423094918891049557)
              ·
                rfl

theorem cell23_6474001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 10].length) (baseStart_6474001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474001 prefixEnd_6474001 := by exact prefixLift 6474001
  have htrace : WordTrace (prefixWord ++ tailWord_6474001) baseStart_6474001 baseEnd_6474001 := by
    simpa [prefixWord, tailWord_6474001, baseEnd_6474001] using wordTrace_append hprefix tailTrace_6474001
  have hstable : (prefixWord ++ tailWord_6474001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474001).length < 2 ^ (prefixWord ++ tailWord_6474001).sum := by decide
  have hdescent : baseEnd_6474001 < baseStart_6474001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474005 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_6474005 : Nat := 118140960795 + 6474005 * 2 ^ 59
def prefixEnd_6474005 : Nat := 4983230072969 + 3 ^ 40 * 6474005 * 2
def baseEnd_6474005 : Nat := 1108092108203682719788033

theorem tailTrace_6474005 : CollatzResearch.WordTrace tailWord_6474005 prefixEnd_6474005 1108092108203682719788033 := by
  unfold tailWord_6474005
  simp only [CollatzResearch.WordTrace]
  refine ⟨236126360910793031872063469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157417573940528687914708979 236126360910793031872063469)
  ·
    refine ⟨88547385341547386952023801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236126360910793031872063469 88547385341547386952023801)
    ·
      refine ⟨66410539006160540214017851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88547385341547386952023801 66410539006160540214017851)
      ·
        refine ⟨99615808509240810321026777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66410539006160540214017851 99615808509240810321026777)
        ·
          refine ⟨74711856381930607740770083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99615808509240810321026777 74711856381930607740770083)
          ·
            refine ⟨112067784572895911611155125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74711856381930607740770083 112067784572895911611155125)
            ·
              refine ⟨10506354803708991713545793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112067784572895911611155125 10506354803708991713545793)
              ·
                refine ⟨7879766102781743785159345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10506354803708991713545793 7879766102781743785159345)
                ·
                  refine ⟨5909824577086307838869509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7879766102781743785159345 5909824577086307838869509)
                  ·
                    refine ⟨1108092108203682719788033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5909824577086307838869509 1108092108203682719788033)
                    ·
                      rfl

theorem cell23_6474005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_6474005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474005 prefixEnd_6474005 := by exact prefixLift 6474005
  have htrace : WordTrace (prefixWord ++ tailWord_6474005) baseStart_6474005 baseEnd_6474005 := by
    simpa [prefixWord, tailWord_6474005, baseEnd_6474005] using wordTrace_append hprefix tailTrace_6474005
  have hstable : (prefixWord ++ tailWord_6474005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474005).length < 2 ^ (prefixWord ++ tailWord_6474005).sum := by decide
  have hdescent : baseEnd_6474005 < baseStart_6474005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474029 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_6474029 : Nat := 118140960795 + 6474029 * 2 ^ 59
def prefixEnd_6474029 : Nat := 4983230072969 + 3 ^ 40 * 6474029 * 2
def baseEnd_6474029 : Nat := 3324288648146756065463989

theorem tailTrace_6474029 : CollatzResearch.WordTrace tailWord_6474029 prefixEnd_6474029 3324288648146756065463989 := by
  unfold tailWord_6474029
  simp only [CollatzResearch.WordTrace]
  refine ⟨236127236262706083970937141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157418157508470722647291427 236127236262706083970937141)
  ·
    refine ⟨22136928399628695372275357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236127236262706083970937141 22136928399628695372275357)
    ·
      refine ⟨8301348149860760764603259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22136928399628695372275357 8301348149860760764603259)
      ·
        refine ⟨12452022224791141146904889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8301348149860760764603259 12452022224791141146904889)
        ·
          refine ⟨9339016668593355860178667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12452022224791141146904889 9339016668593355860178667)
          ·
            refine ⟨14008525002890033790268001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9339016668593355860178667 14008525002890033790268001)
            ·
              refine ⟨10506393752167525342701001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14008525002890033790268001 10506393752167525342701001)
              ·
                refine ⟨7879795314125644007025751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10506393752167525342701001 7879795314125644007025751)
                ·
                  refine ⟨11819692971188466010538627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7879795314125644007025751 11819692971188466010538627)
                  ·
                    refine ⟨17729539456782699015807941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11819692971188466010538627 17729539456782699015807941)
                    ·
                      refine ⟨3324288648146756065463989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17729539456782699015807941 3324288648146756065463989)
                      ·
                        rfl

theorem cell23_6474029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_6474029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474029 prefixEnd_6474029 := by exact prefixLift 6474029
  have htrace : WordTrace (prefixWord ++ tailWord_6474029) baseStart_6474029 baseEnd_6474029 := by
    simpa [prefixWord, tailWord_6474029, baseEnd_6474029] using wordTrace_append hprefix tailTrace_6474029
  have hstable : (prefixWord ++ tailWord_6474029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474029).length < 2 ^ (prefixWord ++ tailWord_6474029).sum := by decide
  have hdescent : baseEnd_6474029 < baseStart_6474029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474031 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 2, 7]
def baseStart_6474031 : Nat := 118140960795 + 6474031 * 2 ^ 59
def prefixEnd_6474031 : Nat := 4983230072969 + 3 ^ 40 * 6474031 * 2
def baseEnd_6474031 : Nat := 1108096558369355019212993

theorem tailTrace_6474031 : CollatzResearch.WordTrace tailWord_6474031 prefixEnd_6474031 1108096558369355019212993 := by
  unfold tailWord_6474031
  simp only [CollatzResearch.WordTrace]
  refine ⟨236127309208698838312509947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157418206139132558875006631 236127309208698838312509947)
  ·
    refine ⟨354190963813048257468764921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236127309208698838312509947 354190963813048257468764921)
    ·
      refine ⟨265643222859786193101573691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354190963813048257468764921 265643222859786193101573691)
      ·
        refine ⟨398464834289679289652360537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265643222859786193101573691 398464834289679289652360537)
        ·
          refine ⟨298848625717259467239270403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398464834289679289652360537 298848625717259467239270403)
          ·
            refine ⟨448272938575889200858905605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298848625717259467239270403 448272938575889200858905605)
            ·
              refine ⟨84051175982979225161044801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 448272938575889200858905605 84051175982979225161044801)
              ·
                refine ⟨63038381987234418870783601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84051175982979225161044801 63038381987234418870783601)
                ·
                  refine ⟨47278786490425814153087701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63038381987234418870783601 47278786490425814153087701)
                  ·
                    refine ⟨1108096558369355019212993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47278786490425814153087701 1108096558369355019212993)
                    ·
                      rfl

theorem cell23_6474031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_6474031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474031 prefixEnd_6474031 := by exact prefixLift 6474031
  have htrace : WordTrace (prefixWord ++ tailWord_6474031) baseStart_6474031 baseEnd_6474031 := by
    simpa [prefixWord, tailWord_6474031, baseEnd_6474031] using wordTrace_append hprefix tailTrace_6474031
  have hstable : (prefixWord ++ tailWord_6474031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474031).length < 2 ^ (prefixWord ++ tailWord_6474031).sum := by decide
  have hdescent : baseEnd_6474031 < baseStart_6474031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474046 : List Nat := [4, 2, 1, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_6474046 : Nat := 118140960795 + 6474046 * 2 ^ 59
def prefixEnd_6474046 : Nat := 4983230072969 + 3 ^ 40 * 6474046 * 2
def baseEnd_6474046 : Nat := 3324297377317882498951411

theorem tailTrace_6474046 : CollatzResearch.WordTrace tailWord_6474046 prefixEnd_6474046 3324297377317882498951411 := by
  unfold tailWord_6474046
  simp only [CollatzResearch.WordTrace]
  refine ⟨29515982037955561984288249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157418570869096330582870661 29515982037955561984288249)
  ·
    refine ⟨22136986528466671488216187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29515982037955561984288249 22136986528466671488216187)
    ·
      refine ⟨33205479792700007232324281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22136986528466671488216187 33205479792700007232324281)
      ·
        refine ⟨24904109844525005424243211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33205479792700007232324281 24904109844525005424243211)
        ·
          refine ⟨37356164766787508136364817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24904109844525005424243211 37356164766787508136364817)
          ·
            refine ⟨28017123575090631102273613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37356164766787508136364817 28017123575090631102273613)
            ·
              refine ⟨10506421340658986663352605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28017123575090631102273613 10506421340658986663352605)
              ·
                refine ⟨3939908002747119998757227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10506421340658986663352605 3939908002747119998757227)
                ·
                  refine ⟨5909862004120679998135841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939908002747119998757227 5909862004120679998135841)
                  ·
                    refine ⟨4432396503090509998601881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5909862004120679998135841 4432396503090509998601881)
                    ·
                      refine ⟨3324297377317882498951411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432396503090509998601881 3324297377317882498951411)
                      ·
                        rfl

theorem cell23_6474046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_6474046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474046 prefixEnd_6474046 := by exact prefixLift 6474046
  have htrace : WordTrace (prefixWord ++ tailWord_6474046) baseStart_6474046 baseEnd_6474046 := by
    simpa [prefixWord, tailWord_6474046, baseEnd_6474046] using wordTrace_append hprefix tailTrace_6474046
  have hstable : (prefixWord ++ tailWord_6474046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474046).length < 2 ^ (prefixWord ++ tailWord_6474046).sum := by decide
  have hdescent : baseEnd_6474046 < baseStart_6474046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474052 : List Nat := [2, 3, 4, 1, 3, 1, 9]
def baseStart_6474052 : Nat := 118140960795 + 6474052 * 2 ^ 59
def prefixEnd_6474052 : Nat := 4983230072969 + 3 ^ 40 * 6474052 * 2
def baseEnd_6474052 : Nat := 41040746397553203400943

theorem tailTrace_6474052 : CollatzResearch.WordTrace tailWord_6474052 prefixEnd_6474052 41040746397553203400943 := by
  unfold tailWord_6474052
  simp only [CollatzResearch.WordTrace]
  refine ⟨118064037570811379449512205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157418716761081839266016273 118064037570811379449512205)
  ·
    refine ⟨44274014089054267293567077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118064037570811379449512205 44274014089054267293567077)
    ·
      refine ⟨8301377641697675117543827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44274014089054267293567077 8301377641697675117543827)
      ·
        refine ⟨12452066462546512676315741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8301377641697675117543827 12452066462546512676315741)
        ·
          refine ⟨4669524923454942253618403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12452066462546512676315741 4669524923454942253618403)
          ·
            refine ⟨7004287385182413380427605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669524923454942253618403 7004287385182413380427605)
            ·
              refine ⟨41040746397553203400943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7004287385182413380427605 41040746397553203400943)
              ·
                rfl

theorem cell23_6474052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 9].length) (baseStart_6474052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474052 prefixEnd_6474052 := by exact prefixLift 6474052
  have htrace : WordTrace (prefixWord ++ tailWord_6474052) baseStart_6474052 baseEnd_6474052 := by
    simpa [prefixWord, tailWord_6474052, baseEnd_6474052] using wordTrace_append hprefix tailTrace_6474052
  have hstable : (prefixWord ++ tailWord_6474052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474052).length < 2 ^ (prefixWord ++ tailWord_6474052).sum := by decide
  have hdescent : baseEnd_6474052 < baseStart_6474052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474119 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_6474119 : Nat := 118140960795 + 6474119 * 2 ^ 59
def prefixEnd_6474119 : Nat := 4983230072969 + 3 ^ 40 * 6474119 * 2
def baseEnd_6474119 : Nat := 3324334861405660713338575

theorem tailTrace_6474119 : CollatzResearch.WordTrace tailWord_6474119 prefixEnd_6474119 3324334861405660713338575 := by
  unfold tailWord_6474119
  simp only [CollatzResearch.WordTrace]
  refine ⟨236130518832380029341713411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157420345888253352894475607 236130518832380029341713411)
  ·
    refine ⟨354195778248570044012570117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236130518832380029341713411 354195778248570044012570117)
    ·
      refine ⟨66411708421606883252356897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354195778248570044012570117 66411708421606883252356897)
      ·
        refine ⟨49808781316205162439267673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66411708421606883252356897 49808781316205162439267673)
        ·
          refine ⟨37356585987153871829450755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49808781316205162439267673 37356585987153871829450755)
          ·
            refine ⟨56034878980730807744176133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37356585987153871829450755 56034878980730807744176133)
            ·
              refine ⟨10506539808887026452033025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56034878980730807744176133 10506539808887026452033025)
              ·
                refine ⟨7879904856665269839024769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10506539808887026452033025 7879904856665269839024769)
                ·
                  refine ⟨5909928642498952379268577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7879904856665269839024769 5909928642498952379268577)
                  ·
                    refine ⟨4432446481874214284451433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5909928642498952379268577 4432446481874214284451433)
                    ·
                      refine ⟨3324334861405660713338575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432446481874214284451433 3324334861405660713338575)
                      ·
                        rfl

theorem cell23_6474119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_6474119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474119 prefixEnd_6474119 := by exact prefixLift 6474119
  have htrace : WordTrace (prefixWord ++ tailWord_6474119) baseStart_6474119 baseEnd_6474119 := by
    simpa [prefixWord, tailWord_6474119, baseEnd_6474119] using wordTrace_append hprefix tailTrace_6474119
  have hstable : (prefixWord ++ tailWord_6474119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474119).length < 2 ^ (prefixWord ++ tailWord_6474119).sum := by decide
  have hdescent : baseEnd_6474119 < baseStart_6474119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474132 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_6474132 : Nat := 118140960795 + 6474132 * 2 ^ 59
def prefixEnd_6474132 : Nat := 4983230072969 + 3 ^ 40 * 6474132 * 2
def baseEnd_6474132 : Nat := 3324341536654169162476015

theorem tailTrace_6474132 : CollatzResearch.WordTrace tailWord_6474132 prefixEnd_6474132 3324341536654169162476015 := by
  unfold tailWord_6474132
  simp only [CollatzResearch.WordTrace]
  refine ⟨118065496490666466280968325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157420661987555288374624433 118065496490666466280968325)
  ·
    refine ⟨22137280591999962427681561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118065496490666466280968325 22137280591999962427681561)
    ·
      refine ⟨16602960443999971820761171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22137280591999962427681561 16602960443999971820761171)
      ·
        refine ⟨24904440665999957731141757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16602960443999971820761171 24904440665999957731141757)
        ·
          refine ⟨9339165249749984149178159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24904440665999957731141757 9339165249749984149178159)
          ·
            refine ⟨14008747874624976223767239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9339165249749984149178159 14008747874624976223767239)
            ·
              refine ⟨21013121811937464335650859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14008747874624976223767239 21013121811937464335650859)
              ·
                refine ⟨31519682717906196503476289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21013121811937464335650859 31519682717906196503476289)
                ·
                  refine ⟨23639762038429647377607217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31519682717906196503476289 23639762038429647377607217)
                  ·
                    refine ⟨17729821528822235533205413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23639762038429647377607217 17729821528822235533205413)
                    ·
                      refine ⟨3324341536654169162476015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17729821528822235533205413 3324341536654169162476015)
                      ·
                        rfl

theorem cell23_6474132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_6474132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474132 prefixEnd_6474132 := by exact prefixLift 6474132
  have htrace : WordTrace (prefixWord ++ tailWord_6474132) baseStart_6474132 baseEnd_6474132 := by
    simpa [prefixWord, tailWord_6474132, baseEnd_6474132] using wordTrace_append hprefix tailTrace_6474132
  have hstable : (prefixWord ++ tailWord_6474132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474132).length < 2 ^ (prefixWord ++ tailWord_6474132).sum := by decide
  have hdescent : baseEnd_6474132 < baseStart_6474132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474142 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_6474142 : Nat := 118140960795 + 6474142 * 2 ^ 59
def prefixEnd_6474142 : Nat := 4983230072969 + 3 ^ 40 * 6474142 * 2
def baseEnd_6474142 : Nat := 369371852384523791483441

theorem tailTrace_6474142 : CollatzResearch.WordTrace tailWord_6474142 prefixEnd_6474142 369371852384523791483441 := by
  unfold tailWord_6474142
  simp only [CollatzResearch.WordTrace]
  refine ⟨29516419713912088033725085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157420905140864469513200453 29516419713912088033725085)
  ·
    refine ⟨11068657392717033012646907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29516419713912088033725085 11068657392717033012646907)
    ·
      refine ⟨16602986089075549518970361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11068657392717033012646907 16602986089075549518970361)
      ·
        refine ⟨12452239566806662139227771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16602986089075549518970361 12452239566806662139227771)
        ·
          refine ⟨18678359350209993208841657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12452239566806662139227771 18678359350209993208841657)
          ·
            refine ⟨14008769512657494906631243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18678359350209993208841657 14008769512657494906631243)
            ·
              refine ⟨21013154268986242359946865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14008769512657494906631243 21013154268986242359946865)
              ·
                refine ⟨15759865701739681769960149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21013154268986242359946865 15759865701739681769960149)
                ·
                  refine ⟨369371852384523791483441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15759865701739681769960149 369371852384523791483441)
                  ·
                    rfl

theorem cell23_6474142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_6474142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474142 prefixEnd_6474142 := by exact prefixLift 6474142
  have htrace : WordTrace (prefixWord ++ tailWord_6474142) baseStart_6474142 baseEnd_6474142 := by
    simpa [prefixWord, tailWord_6474142, baseEnd_6474142] using wordTrace_append hprefix tailTrace_6474142
  have hstable : (prefixWord ++ tailWord_6474142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474142).length < 2 ^ (prefixWord ++ tailWord_6474142).sum := by decide
  have hdescent : baseEnd_6474142 < baseStart_6474142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474148 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_6474148 : Nat := 118140960795 + 6474148 * 2 ^ 59
def prefixEnd_6474148 : Nat := 4983230072969 + 3 ^ 40 * 6474148 * 2
def baseEnd_6474148 : Nat := 3324349752344641099875941

theorem tailTrace_6474148 : CollatzResearch.WordTrace tailWord_6474148 prefixEnd_6474148 3324349752344641099875941 := by
  unfold tailWord_6474148
  simp only [CollatzResearch.WordTrace]
  refine ⟨118065788274637483647259549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157421051032849978196346065 118065788274637483647259549)
  ·
    refine ⟨44274670602989056367722331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118065788274637483647259549 44274670602989056367722331)
    ·
      refine ⟨66412005904483584551583497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44274670602989056367722331 66412005904483584551583497)
      ·
        refine ⟨49809004428362688413687623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66412005904483584551583497 49809004428362688413687623)
        ·
          refine ⟨74713506642544032620531435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49809004428362688413687623 74713506642544032620531435)
          ·
            refine ⟨112070259963816048930797153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74713506642544032620531435 112070259963816048930797153)
            ·
              refine ⟨84052694972862036698097865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112070259963816048930797153 84052694972862036698097865)
              ·
                refine ⟨63039521229646527523573399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84052694972862036698097865 63039521229646527523573399)
                ·
                  refine ⟨94559281844469791285360099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63039521229646527523573399 94559281844469791285360099)
                  ·
                    refine ⟨141838922766704686928040149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94559281844469791285360099 141838922766704686928040149)
                    ·
                      refine ⟨3324349752344641099875941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141838922766704686928040149 3324349752344641099875941)
                      ·
                        rfl

theorem cell23_6474148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_6474148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474148 prefixEnd_6474148 := by exact prefixLift 6474148
  have htrace : WordTrace (prefixWord ++ tailWord_6474148) baseStart_6474148 baseEnd_6474148 := by
    simpa [prefixWord, tailWord_6474148, baseEnd_6474148] using wordTrace_append hprefix tailTrace_6474148
  have hstable : (prefixWord ++ tailWord_6474148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474148).length < 2 ^ (prefixWord ++ tailWord_6474148).sum := by decide
  have hdescent : baseEnd_6474148 < baseStart_6474148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474185 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 3, 4]
def baseStart_6474185 : Nat := 118140960795 + 6474185 * 2 ^ 59
def prefixEnd_6474185 : Nat := 4983230072969 + 3 ^ 40 * 6474185 * 2
def baseEnd_6474185 : Nat := 1108122917042952485037757

theorem tailTrace_6474185 : CollatzResearch.WordTrace tailWord_6474185 prefixEnd_6474185 1108122917042952485037757 := by
  unfold tailWord_6474185
  simp only [CollatzResearch.WordTrace]
  refine ⟨236132926050140922613616009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157421950700093948409077339 236132926050140922613616009)
  ·
    refine ⟨177099694537605691960212007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236132926050140922613616009 177099694537605691960212007)
    ·
      refine ⟨265649541806408537940318011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177099694537605691960212007 265649541806408537940318011)
      ·
        refine ⟨398474312709612806910477017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265649541806408537940318011 398474312709612806910477017)
        ·
          refine ⟨298855734532209605182857763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398474312709612806910477017 298855734532209605182857763)
          ·
            refine ⟨448283601798314407774286645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298855734532209605182857763 448283601798314407774286645)
            ·
              refine ⟨42026587668591975728839373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 448283601798314407774286645 42026587668591975728839373)
              ·
                refine ⟨15759970375721990898314765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42026587668591975728839373 15759970375721990898314765)
                ·
                  refine ⟨5909988890895746586868037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15759970375721990898314765 5909988890895746586868037)
                  ·
                    refine ⟨1108122917042952485037757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5909988890895746586868037 1108122917042952485037757)
                    ·
                      rfl

theorem cell23_6474185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 4].length) (baseStart_6474185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474185 prefixEnd_6474185 := by exact prefixLift 6474185
  have htrace : WordTrace (prefixWord ++ tailWord_6474185) baseStart_6474185 baseEnd_6474185 := by
    simpa [prefixWord, tailWord_6474185, baseEnd_6474185] using wordTrace_append hprefix tailTrace_6474185
  have hstable : (prefixWord ++ tailWord_6474185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474185).length < 2 ^ (prefixWord ++ tailWord_6474185).sum := by decide
  have hdescent : baseEnd_6474185 < baseStart_6474185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474205 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6474205 : Nat := 118140960795 + 6474205 * 2 ^ 59
def prefixEnd_6474205 : Nat := 4983230072969 + 3 ^ 40 * 6474205 * 2
def baseEnd_6474205 : Nat := 3324379020741947376863179

theorem tailTrace_6474205 : CollatzResearch.WordTrace tailWord_6474205 prefixEnd_6474205 3324379020741947376863179 := by
  unfold tailWord_6474205
  simp only [CollatzResearch.WordTrace]
  refine ⟨236133655510068466029344069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157422437006712310686229379 236133655510068466029344069)
  ·
    refine ⟨44275060408137837380502013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236133655510068466029344069 44275060408137837380502013)
    ·
      refine ⟨16603147653051689017688255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44275060408137837380502013 16603147653051689017688255)
      ·
        refine ⟨24904721479577533526532383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16603147653051689017688255 24904721479577533526532383)
        ·
          refine ⟨37357082219366300289798575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24904721479577533526532383 37357082219366300289798575)
          ·
            refine ⟨56035623329049450434697863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37357082219366300289798575 56035623329049450434697863)
            ·
              refine ⟨84053434993574175652046795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56035623329049450434697863 84053434993574175652046795)
              ·
                refine ⟨126080152490361263478070193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84053434993574175652046795 126080152490361263478070193)
                ·
                  refine ⟨94560114367770947608552645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126080152490361263478070193 94560114367770947608552645)
                  ·
                    refine ⟨17730021443957052676603621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94560114367770947608552645 17730021443957052676603621)
                    ·
                      refine ⟨3324379020741947376863179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17730021443957052676603621 3324379020741947376863179)
                      ·
                        rfl

theorem cell23_6474205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6474205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474205 prefixEnd_6474205 := by exact prefixLift 6474205
  have htrace : WordTrace (prefixWord ++ tailWord_6474205) baseStart_6474205 baseEnd_6474205 := by
    simpa [prefixWord, tailWord_6474205, baseEnd_6474205] using wordTrace_append hprefix tailTrace_6474205
  have hstable : (prefixWord ++ tailWord_6474205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474205).length < 2 ^ (prefixWord ++ tailWord_6474205).sum := by decide
  have hdescent : baseEnd_6474205 < baseStart_6474205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474265 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_6474265 : Nat := 118140960795 + 6474265 * 2 ^ 59
def prefixEnd_6474265 : Nat := 4983230072969 + 3 ^ 40 * 6474265 * 2
def baseEnd_6474265 : Nat := 3324409829581217142112903

theorem tailTrace_6474265 : CollatzResearch.WordTrace tailWord_6474265 prefixEnd_6474265 3324409829581217142112903 := by
  unfold tailWord_6474265
  simp only [CollatzResearch.WordTrace]
  refine ⟨236135843889851096276528249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157423895926567397517685499 236135843889851096276528249)
  ·
    refine ⟨177101882917388322207396187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236135843889851096276528249 177101882917388322207396187)
    ·
      refine ⟨265652824376082483311094281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177101882917388322207396187 265652824376082483311094281)
      ·
        refine ⟨199239618282061862483320711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265652824376082483311094281 199239618282061862483320711)
        ·
          refine ⟨298859427423092793724981067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199239618282061862483320711 298859427423092793724981067)
          ·
            refine ⟨448289141134639190587471601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298859427423092793724981067 448289141134639190587471601)
            ·
              refine ⟨336216855850979392940603701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448289141134639190587471601 336216855850979392940603701)
              ·
                refine ⟨31520330236029318088181597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336216855850979392940603701 31520330236029318088181597)
                ·
                  refine ⟨11820123838510994283068099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31520330236029318088181597 11820123838510994283068099)
                  ·
                    refine ⟨17730185757766491424602149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11820123838510994283068099 17730185757766491424602149)
                    ·
                      refine ⟨3324409829581217142112903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17730185757766491424602149 3324409829581217142112903)
                      ·
                        rfl

theorem cell23_6474265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_6474265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474265 prefixEnd_6474265 := by exact prefixLift 6474265
  have htrace : WordTrace (prefixWord ++ tailWord_6474265) baseStart_6474265 baseEnd_6474265 := by
    simpa [prefixWord, tailWord_6474265, baseEnd_6474265] using wordTrace_append hprefix tailTrace_6474265
  have hstable : (prefixWord ++ tailWord_6474265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474265).length < 2 ^ (prefixWord ++ tailWord_6474265).sum := by decide
  have hdescent : baseEnd_6474265 < baseStart_6474265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474269 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_6474269 : Nat := 118140960795 + 6474269 * 2 ^ 59
def prefixEnd_6474269 : Nat := 4983230072969 + 3 ^ 40 * 6474269 * 2
def baseEnd_6474269 : Nat := 3324411883503835126462885

theorem tailTrace_6474269 : CollatzResearch.WordTrace tailWord_6474269 prefixEnd_6474269 3324411883503835126462885 := by
  unfold tailWord_6474269
  simp only [CollatzResearch.WordTrace]
  refine ⟨236135989781836604959673861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157423993187891069973115907 236135989781836604959673861)
  ·
    refine ⟨44275498084094363429938849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236135989781836604959673861 44275498084094363429938849)
    ·
      refine ⟨33206623563070772572454137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44275498084094363429938849 33206623563070772572454137)
      ·
        refine ⟨24904967672303079429340603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33206623563070772572454137 24904967672303079429340603)
        ·
          refine ⟨37357451508454619144010905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24904967672303079429340603 37357451508454619144010905)
          ·
            refine ⟨28018088631340964358008179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37357451508454619144010905 28018088631340964358008179)
            ·
              refine ⟨42027132947011446537012269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28018088631340964358008179 42027132947011446537012269)
              ·
                refine ⟨15760174855129292451379601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42027132947011446537012269 15760174855129292451379601)
                ·
                  refine ⟨11820131141346969338534701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15760174855129292451379601 11820131141346969338534701)
                  ·
                    refine ⟨4432549178005113501950513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11820131141346969338534701 4432549178005113501950513)
                    ·
                      refine ⟨3324411883503835126462885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432549178005113501950513 3324411883503835126462885)
                      ·
                        rfl

theorem cell23_6474269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_6474269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474269 prefixEnd_6474269 := by exact prefixLift 6474269
  have htrace : WordTrace (prefixWord ++ tailWord_6474269) baseStart_6474269 baseEnd_6474269 := by
    simpa [prefixWord, tailWord_6474269, baseEnd_6474269] using wordTrace_append hprefix tailTrace_6474269
  have hstable : (prefixWord ++ tailWord_6474269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474269).length < 2 ^ (prefixWord ++ tailWord_6474269).sum := by decide
  have hdescent : baseEnd_6474269 < baseStart_6474269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474275 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 3, 6]
def baseStart_6474275 : Nat := 118140960795 + 6474275 * 2 ^ 59
def prefixEnd_6474275 : Nat := 4983230072969 + 3 ^ 40 * 6474275 * 2
def baseEnd_6474275 : Nat := 1108138321462587367662619

theorem tailTrace_6474275 : CollatzResearch.WordTrace tailWord_6474275 prefixEnd_6474275 1108138321462587367662619 := by
  unfold tailWord_6474275
  simp only [CollatzResearch.WordTrace]
  refine ⟨236136208619814867984392279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157424139079876578656261519 236136208619814867984392279)
  ·
    refine ⟨354204312929722301976588419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236136208619814867984392279 354204312929722301976588419)
    ·
      refine ⟨531306469394583452964882629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354204312929722301976588419 531306469394583452964882629)
      ·
        refine ⟨99619963011484397430915493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 531306469394583452964882629 99619963011484397430915493)
        ·
          refine ⟨18678743064653324518296655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99619963011484397430915493 18678743064653324518296655)
          ·
            refine ⟨28018114596979986777444983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18678743064653324518296655 28018114596979986777444983)
            ·
              refine ⟨42027171895469980166167475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28018114596979986777444983 42027171895469980166167475)
              ·
                refine ⟨63040757843204970249251213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42027171895469980166167475 63040757843204970249251213)
                ·
                  refine ⟨23640284191201863843469205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63040757843204970249251213 23640284191201863843469205)
                  ·
                    refine ⟨1108138321462587367662619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23640284191201863843469205 1108138321462587367662619)
                    ·
                      rfl

theorem cell23_6474275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 6].length) (baseStart_6474275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474275 prefixEnd_6474275 := by exact prefixLift 6474275
  have htrace : WordTrace (prefixWord ++ tailWord_6474275) baseStart_6474275 baseEnd_6474275 := by
    simpa [prefixWord, tailWord_6474275, baseEnd_6474275] using wordTrace_append hprefix tailTrace_6474275
  have hstable : (prefixWord ++ tailWord_6474275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474275).length < 2 ^ (prefixWord ++ tailWord_6474275).sum := by decide
  have hdescent : baseEnd_6474275 < baseStart_6474275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474295 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_6474295 : Nat := 118140960795 + 6474295 * 2 ^ 59
def prefixEnd_6474295 : Nat := 4983230072969 + 3 ^ 40 * 6474295 * 2
def baseEnd_6474295 : Nat := 3324425234000852024737765

theorem tailTrace_6474295 : CollatzResearch.WordTrace tailWord_6474295 prefixEnd_6474295 3324425234000852024737765 := by
  unfold tailWord_6474295
  simp only [CollatzResearch.WordTrace]
  refine ⟨236136938079742411400120339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157424625386494940933413559 236136938079742411400120339)
  ·
    refine ⟨354205407119613617100180509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236136938079742411400120339 354205407119613617100180509)
    ·
      refine ⟨132827027669855106412567691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354205407119613617100180509 132827027669855106412567691)
      ·
        refine ⟨199240541504782659618851537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132827027669855106412567691 199240541504782659618851537)
        ·
          refine ⟨149430406128586994714138653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199240541504782659618851537 149430406128586994714138653)
          ·
            refine ⟨56036402298220123017801995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149430406128586994714138653 56036402298220123017801995)
            ·
              refine ⟨84054603447330184526702993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56036402298220123017801995 84054603447330184526702993)
              ·
                refine ⟨63040952585497638395027245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84054603447330184526702993 63040952585497638395027245)
                ·
                  refine ⟨23640357219561614398135217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63040952585497638395027245 23640357219561614398135217)
                  ·
                    refine ⟨17730267914671210798601413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23640357219561614398135217 17730267914671210798601413)
                    ·
                      refine ⟨3324425234000852024737765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17730267914671210798601413 3324425234000852024737765)
                      ·
                        rfl

theorem cell23_6474295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_6474295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474295 prefixEnd_6474295 := by exact prefixLift 6474295
  have htrace : WordTrace (prefixWord ++ tailWord_6474295) baseStart_6474295 baseEnd_6474295 := by
    simpa [prefixWord, tailWord_6474295, baseEnd_6474295] using wordTrace_append hprefix tailTrace_6474295
  have hstable : (prefixWord ++ tailWord_6474295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474295).length < 2 ^ (prefixWord ++ tailWord_6474295).sum := by decide
  have hdescent : baseEnd_6474295 < baseStart_6474295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474322 : List Nat := [3, 2, 2, 1, 2, 1, 5, 7]
def baseStart_6474322 : Nat := 118140960795 + 6474322 * 2 ^ 59
def prefixEnd_6474322 : Nat := 4983230072969 + 3 ^ 40 * 6474322 * 2
def baseEnd_6474322 : Nat := 123127373999204571077783

theorem tailTrace_6474322 : CollatzResearch.WordTrace tailWord_6474322 prefixEnd_6474322 123127373999204571077783 := by
  unfold tailWord_6474322
  simp only [CollatzResearch.WordTrace]
  refine ⟨59034480712661148752838305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157425281900429730007568813 59034480712661148752838305)
  ·
    refine ⟨44275860534495861564628729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59034480712661148752838305 44275860534495861564628729)
    ·
      refine ⟨33206895400871896173471547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44275860534495861564628729 33206895400871896173471547)
      ·
        refine ⟨49810343101307844260207321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33206895400871896173471547 49810343101307844260207321)
        ·
          refine ⟨37357757325980883195155491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49810343101307844260207321 37357757325980883195155491)
          ·
            refine ⟨56036635988971324792733237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37357757325980883195155491 56036635988971324792733237)
            ·
              refine ⟨5253434623966061699318741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56036635988971324792733237 5253434623966061699318741)
              ·
                refine ⟨123127373999204571077783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5253434623966061699318741 123127373999204571077783)
                ·
                  rfl

theorem cell23_6474322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 7].length) (baseStart_6474322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474322 prefixEnd_6474322 := by exact prefixLift 6474322
  have htrace : WordTrace (prefixWord ++ tailWord_6474322) baseStart_6474322 baseEnd_6474322 := by
    simpa [prefixWord, tailWord_6474322, baseEnd_6474322] using wordTrace_append hprefix tailTrace_6474322
  have hstable : (prefixWord ++ tailWord_6474322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474322).length < 2 ^ (prefixWord ++ tailWord_6474322).sum := by decide
  have hdescent : baseEnd_6474322 < baseStart_6474322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474355 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 4]
def baseStart_6474355 : Nat := 118140960795 + 6474355 * 2 ^ 59
def prefixEnd_6474355 : Nat := 4983230072969 + 3 ^ 40 * 6474355 * 2
def baseEnd_6474355 : Nat := 3324456042840121789987489

theorem tailTrace_6474355 : CollatzResearch.WordTrace tailWord_6474355 prefixEnd_6474355 3324456042840121789987489 := by
  unfold tailWord_6474355
  simp only [CollatzResearch.WordTrace]
  refine ⟨236139126459525041647304519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157426084306350027764869679 236139126459525041647304519)
  ·
    refine ⟨354208689689287562470956779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236139126459525041647304519 354208689689287562470956779)
    ·
      refine ⟨531313034533931343706435169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354208689689287562470956779 531313034533931343706435169)
      ·
        refine ⟨398484775900448507779826377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531313034533931343706435169 398484775900448507779826377)
        ·
          refine ⟨298863581925336380834869783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398484775900448507779826377 298863581925336380834869783)
          ·
            refine ⟨448295372888004571252304675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298863581925336380834869783 448295372888004571252304675)
            ·
              refine ⟨672443059332006856878457013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448295372888004571252304675 672443059332006856878457013)
              ·
                refine ⟨63041536812375642832355345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 672443059332006856878457013 63041536812375642832355345)
                ·
                  refine ⟨47281152609281732124266509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63041536812375642832355345 47281152609281732124266509)
                  ·
                    refine ⟨17730432228480649546599941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47281152609281732124266509 17730432228480649546599941)
                    ·
                      refine ⟨3324456042840121789987489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17730432228480649546599941 3324456042840121789987489)
                      ·
                        rfl

theorem cell23_6474355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_6474355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474355 prefixEnd_6474355 := by exact prefixLift 6474355
  have htrace : WordTrace (prefixWord ++ tailWord_6474355) baseStart_6474355 baseEnd_6474355 := by
    simpa [prefixWord, tailWord_6474355, baseEnd_6474355] using wordTrace_append hprefix tailTrace_6474355
  have hstable : (prefixWord ++ tailWord_6474355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474355).length < 2 ^ (prefixWord ++ tailWord_6474355).sum := by decide
  have hdescent : baseEnd_6474355 < baseStart_6474355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474392 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6474392 : Nat := 118140960795 + 6474392 * 2 ^ 59
def prefixEnd_6474392 : Nat := 4983230072969 + 3 ^ 40 * 6474392 * 2
def baseEnd_6474392 : Nat := 3324475041624338145224819

theorem tailTrace_6474392 : CollatzResearch.WordTrace tailWord_6474392 prefixEnd_6474392 3324475041624338145224819 := by
  unfold tailWord_6474392
  simp only [CollatzResearch.WordTrace]
  refine ⟨118070237980195498483200715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157426983973593997977600953 118070237980195498483200715)
  ·
    refine ⟨177105356970293247724801073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118070237980195498483200715 177105356970293247724801073)
    ·
      refine ⟨132829017727719935793600805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177105356970293247724801073 132829017727719935793600805)
      ·
        refine ⟨24905440823947487961300151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132829017727719935793600805 24905440823947487961300151)
        ·
          refine ⟨37358161235921231941950227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24905440823947487961300151 37358161235921231941950227)
          ·
            refine ⟨56037241853881847912925341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37358161235921231941950227 56037241853881847912925341)
            ·
              refine ⟨21013965695205692967347003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56037241853881847912925341 21013965695205692967347003)
              ·
                refine ⟨31520948542808539451020505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21013965695205692967347003 31520948542808539451020505)
                ·
                  refine ⟨23640711407106404588265379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31520948542808539451020505 23640711407106404588265379)
                  ·
                    refine ⟨35461067110659606882398069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23640711407106404588265379 35461067110659606882398069)
                    ·
                      refine ⟨3324475041624338145224819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35461067110659606882398069 3324475041624338145224819)
                      ·
                        rfl

theorem cell23_6474392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6474392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474392 prefixEnd_6474392 := by exact prefixLift 6474392
  have htrace : WordTrace (prefixWord ++ tailWord_6474392) baseStart_6474392 baseEnd_6474392 := by
    simpa [prefixWord, tailWord_6474392, baseEnd_6474392] using wordTrace_append hprefix tailTrace_6474392
  have hstable : (prefixWord ++ tailWord_6474392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474392).length < 2 ^ (prefixWord ++ tailWord_6474392).sum := by decide
  have hdescent : baseEnd_6474392 < baseStart_6474392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474405 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_6474405 : Nat := 118140960795 + 6474405 * 2 ^ 59
def prefixEnd_6474405 : Nat := 4983230072969 + 3 ^ 40 * 6474405 * 2
def baseEnd_6474405 : Nat := 3324481716872846594362259

theorem tailTrace_6474405 : CollatzResearch.WordTrace tailWord_6474405 prefixEnd_6474405 3324481716872846594362259 := by
  unfold tailWord_6474405
  simp only [CollatzResearch.WordTrace]
  refine ⟨236140950109343900186624669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157427300072895933457749779 236140950109343900186624669)
  ·
    refine ⟨88552856291003962569984251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236140950109343900186624669 88552856291003962569984251)
    ·
      refine ⟨132829284436505943854976377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88552856291003962569984251 132829284436505943854976377)
      ·
        refine ⟨99621963327379457891232283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132829284436505943854976377 99621963327379457891232283)
        ·
          refine ⟨149432944991069186836848425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99621963327379457891232283 149432944991069186836848425)
          ·
            refine ⟨112074708743301890127636319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149432944991069186836848425 112074708743301890127636319)
            ·
              refine ⟨168112063114952835191454479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112074708743301890127636319 168112063114952835191454479)
              ·
                refine ⟨252168094672429252787181719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168112063114952835191454479 252168094672429252787181719)
                ·
                  refine ⟨378252142008643879180772579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252168094672429252787181719 378252142008643879180772579)
                  ·
                    refine ⟨567378213012965818771158869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 378252142008643879180772579 567378213012965818771158869)
                    ·
                      refine ⟨3324481716872846594362259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 567378213012965818771158869 3324481716872846594362259)
                      ·
                        rfl

theorem cell23_6474405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_6474405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474405 prefixEnd_6474405 := by exact prefixLift 6474405
  have htrace : WordTrace (prefixWord ++ tailWord_6474405) baseStart_6474405 baseEnd_6474405 := by
    simpa [prefixWord, tailWord_6474405, baseEnd_6474405] using wordTrace_append hprefix tailTrace_6474405
  have hstable : (prefixWord ++ tailWord_6474405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474405).length < 2 ^ (prefixWord ++ tailWord_6474405).sum := by decide
  have hdescent : baseEnd_6474405 < baseStart_6474405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474417 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6474417 : Nat := 118140960795 + 6474417 * 2 ^ 59
def prefixEnd_6474417 : Nat := 4983230072969 + 3 ^ 40 * 6474417 * 2
def baseEnd_6474417 : Nat := 3324487878640700547412205

theorem tailTrace_6474417 : CollatzResearch.WordTrace tailWord_6474417 prefixEnd_6474417 3324487878640700547412205 := by
  unfold tailWord_6474417
  simp only [CollatzResearch.WordTrace]
  refine ⟨236141387785300426236061505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157427591856866950824041003 236141387785300426236061505)
  ·
    refine ⟨177106040838975319677046129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236141387785300426236061505 177106040838975319677046129)
    ·
      refine ⟨132829530629231489757784597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177106040838975319677046129 132829530629231489757784597)
      ·
        refine ⟨6226384248245226082396153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132829530629231489757784597 6226384248245226082396153)
        ·
          refine ⟨4669788186183919561797115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6226384248245226082396153 4669788186183919561797115)
          ·
            refine ⟨7004682279275879342695673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669788186183919561797115 7004682279275879342695673)
            ·
              refine ⟨5253511709456909507021755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7004682279275879342695673 5253511709456909507021755)
              ·
                refine ⟨7880267564185364260532633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253511709456909507021755 7880267564185364260532633)
                ·
                  refine ⟨5910200673139023195399475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7880267564185364260532633 5910200673139023195399475)
                  ·
                    refine ⟨8865301009708534793099213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910200673139023195399475 8865301009708534793099213)
                    ·
                      refine ⟨3324487878640700547412205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8865301009708534793099213 3324487878640700547412205)
                      ·
                        rfl

theorem cell23_6474417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6474417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474417 prefixEnd_6474417 := by exact prefixLift 6474417
  have htrace : WordTrace (prefixWord ++ tailWord_6474417) baseStart_6474417 baseEnd_6474417 := by
    simpa [prefixWord, tailWord_6474417, baseEnd_6474417] using wordTrace_append hprefix tailTrace_6474417
  have hstable : (prefixWord ++ tailWord_6474417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474417).length < 2 ^ (prefixWord ++ tailWord_6474417).sum := by decide
  have hdescent : baseEnd_6474417 < baseStart_6474417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474423 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 2, 2, 2]
def baseStart_6474423 : Nat := 118140960795 + 6474423 * 2 ^ 59
def prefixEnd_6474423 : Nat := 4983230072969 + 3 ^ 40 * 6474423 * 2
def baseEnd_6474423 : Nat := 3324490959524627523937177

theorem tailTrace_6474423 : CollatzResearch.WordTrace tailWord_6474423 prefixEnd_6474423 3324490959524627523937177 := by
  unfold tailWord_6474423
  simp only [CollatzResearch.WordTrace]
  refine ⟨236141606623278689260779923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157427737748852459507186615 236141606623278689260779923)
  ·
    refine ⟨354212409934918033891169885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236141606623278689260779923 354212409934918033891169885)
    ·
      refine ⟨132829653725594262709188707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354212409934918033891169885 132829653725594262709188707)
      ·
        refine ⟨199244480588391394063783061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132829653725594262709188707 199244480588391394063783061)
        ·
          refine ⟨9339585027580846596739831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199244480588391394063783061 9339585027580846596739831)
          ·
            refine ⟨14009377541371269895109747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9339585027580846596739831 14009377541371269895109747)
            ·
              refine ⟨21014066312056904842664621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14009377541371269895109747 21014066312056904842664621)
              ·
                refine ⟨7880274867021339315999233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21014066312056904842664621 7880274867021339315999233)
                ·
                  refine ⟨5910206150266004486999425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7880274867021339315999233 5910206150266004486999425)
                  ·
                    refine ⟨4432654612699503365249569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5910206150266004486999425 4432654612699503365249569)
                    ·
                      refine ⟨3324490959524627523937177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432654612699503365249569 3324490959524627523937177)
                      ·
                        rfl

theorem cell23_6474423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_6474423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474423 prefixEnd_6474423 := by exact prefixLift 6474423
  have htrace : WordTrace (prefixWord ++ tailWord_6474423) baseStart_6474423 baseEnd_6474423 := by
    simpa [prefixWord, tailWord_6474423, baseEnd_6474423] using wordTrace_append hprefix tailTrace_6474423
  have hstable : (prefixWord ++ tailWord_6474423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474423).length < 2 ^ (prefixWord ++ tailWord_6474423).sum := by decide
  have hdescent : baseEnd_6474423 < baseStart_6474423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474479 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 1, 6, 2]
def baseStart_6474479 : Nat := 118140960795 + 6474479 * 2 ^ 59
def prefixEnd_6474479 : Nat := 4983230072969 + 3 ^ 40 * 6474479 * 2
def baseEnd_6474479 : Nat := 3324519714441279304836919

theorem tailTrace_6474479 : CollatzResearch.WordTrace tailWord_6474479 prefixEnd_6474479 3324519714441279304836919 := by
  unfold tailWord_6474479
  simp only [CollatzResearch.WordTrace]
  refine ⟨236143649111075810824818491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157429099407383873883212327 236143649111075810824818491)
  ·
    refine ⟨354215473666613716237227737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236143649111075810824818491 354215473666613716237227737)
    ·
      refine ⟨265661605249960287177920803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354215473666613716237227737 265661605249960287177920803)
      ·
        refine ⟨398492407874940430766881205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265661605249960287177920803 398492407874940430766881205)
        ·
          refine ⟨37358663238275665384395113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 398492407874940430766881205 37358663238275665384395113)
          ·
            refine ⟨28018997428706749038296335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37358663238275665384395113 28018997428706749038296335)
            ·
              refine ⟨42028496143060123557444503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28018997428706749038296335 42028496143060123557444503)
              ·
                refine ⟨63042744214590185336166755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42028496143060123557444503 63042744214590185336166755)
                ·
                  refine ⟨94564116321885278004250133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63042744214590185336166755 94564116321885278004250133)
                  ·
                    refine ⟨4432692952588372406449225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94564116321885278004250133 4432692952588372406449225)
                    ·
                      refine ⟨3324519714441279304836919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432692952588372406449225 3324519714441279304836919)
                      ·
                        rfl

theorem cell23_6474479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 6, 2].length) (baseStart_6474479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474479 prefixEnd_6474479 := by exact prefixLift 6474479
  have htrace : WordTrace (prefixWord ++ tailWord_6474479) baseStart_6474479 baseEnd_6474479 := by
    simpa [prefixWord, tailWord_6474479, baseEnd_6474479] using wordTrace_append hprefix tailTrace_6474479
  have hstable : (prefixWord ++ tailWord_6474479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474479).length < 2 ^ (prefixWord ++ tailWord_6474479).sum := by decide
  have hdescent : baseEnd_6474479 < baseStart_6474479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474519 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 8]
def baseStart_6474519 : Nat := 118140960795 + 6474519 * 2 ^ 59
def prefixEnd_6474519 : Nat := 4983230072969 + 3 ^ 40 * 6474519 * 2
def baseEnd_6474519 : Nat := 369393361518606572037415

theorem tailTrace_6474519 : CollatzResearch.WordTrace tailWord_6474519 prefixEnd_6474519 369393361518606572037415 := by
  unfold tailWord_6474519
  simp only [CollatzResearch.WordTrace]
  refine ⟨236145108030930897656274611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157430072020620598437516407 236145108030930897656274611)
  ·
    refine ⟨354217662046396346484411917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236145108030930897656274611 354217662046396346484411917)
    ·
      refine ⟨132831623267398629931654469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354217662046396346484411917 132831623267398629931654469)
      ·
        refine ⟨24905929362637243112185213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132831623267398629931654469 24905929362637243112185213)
        ·
          refine ⟨9339723510988966167069455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24905929362637243112185213 9339723510988966167069455)
          ·
            refine ⟨14009585266483449250604183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9339723510988966167069455 14009585266483449250604183)
            ·
              refine ⟨21014377899725173875906275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14009585266483449250604183 21014377899725173875906275)
              ·
                refine ⟨31521566849587760813859413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21014377899725173875906275 31521566849587760813859413)
                ·
                  refine ⟨369393361518606572037415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31521566849587760813859413 369393361518606572037415)
                  ·
                    rfl

theorem cell23_6474519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 8].length) (baseStart_6474519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474519 prefixEnd_6474519 := by exact prefixLift 6474519
  have htrace : WordTrace (prefixWord ++ tailWord_6474519) baseStart_6474519 baseEnd_6474519 := by
    simpa [prefixWord, tailWord_6474519, baseEnd_6474519] using wordTrace_append hprefix tailTrace_6474519
  have hstable : (prefixWord ++ tailWord_6474519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474519).length < 2 ^ (prefixWord ++ tailWord_6474519).sum := by decide
  have hdescent : baseEnd_6474519 < baseStart_6474519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474522 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_6474522 : Nat := 118140960795 + 6474522 * 2 ^ 59
def prefixEnd_6474522 : Nat := 4983230072969 + 3 ^ 40 * 6474522 * 2
def baseEnd_6474522 : Nat := 3324541794109422636599221

theorem tailTrace_6474522 : CollatzResearch.WordTrace tailWord_6474522 prefixEnd_6474522 3324541794109422636599221 := by
  unfold tailWord_6474522
  simp only [CollatzResearch.WordTrace]
  refine ⟨59036304362480007292158455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157430144966613352779089213 59036304362480007292158455)
  ·
    refine ⟨88554456543720010938237683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59036304362480007292158455 88554456543720010938237683)
    ·
      refine ⟨132831684815580016407356525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88554456543720010938237683 132831684815580016407356525)
      ·
        refine ⟨49811881805842506152758697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132831684815580016407356525 49811881805842506152758697)
        ·
          refine ⟨37358911354381879614569023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49811881805842506152758697 37358911354381879614569023)
          ·
            refine ⟨56038367031572819421853535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37358911354381879614569023 56038367031572819421853535)
            ·
              refine ⟨84057550547359229132780303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56038367031572819421853535 84057550547359229132780303)
              ·
                refine ⟨126086325821038843699170455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84057550547359229132780303 126086325821038843699170455)
                ·
                  refine ⟨189129488731558265548755683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126086325821038843699170455 189129488731558265548755683)
                  ·
                    refine ⟨283694233097337398323133525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189129488731558265548755683 283694233097337398323133525)
                    ·
                      refine ⟨3324541794109422636599221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 283694233097337398323133525 3324541794109422636599221)
                      ·
                        rfl

theorem cell23_6474522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_6474522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474522 prefixEnd_6474522 := by exact prefixLift 6474522
  have htrace : WordTrace (prefixWord ++ tailWord_6474522) baseStart_6474522 baseEnd_6474522 := by
    simpa [prefixWord, tailWord_6474522, baseEnd_6474522] using wordTrace_append hprefix tailTrace_6474522
  have hstable : (prefixWord ++ tailWord_6474522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474522).length < 2 ^ (prefixWord ++ tailWord_6474522).sum := by decide
  have hdescent : baseEnd_6474522 < baseStart_6474522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474536 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 6]
def baseStart_6474536 : Nat := 118140960795 + 6474536 * 2 ^ 59
def prefixEnd_6474536 : Nat := 4983230072969 + 3 ^ 40 * 6474536 * 2
def baseEnd_6474536 : Nat := 369394331426509509091573

theorem tailTrace_6474536 : CollatzResearch.WordTrace tailWord_6474536 prefixEnd_6474536 369394331426509509091573 := by
  unfold tailWord_6474536
  simp only [CollatzResearch.WordTrace]
  refine ⟨118072864035934654779821731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157430485381246206373095641 118072864035934654779821731)
  ·
    refine ⟨177109296053901982169732597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118072864035934654779821731 177109296053901982169732597)
    ·
      refine ⟨16603996505053310828412431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177109296053901982169732597 16603996505053310828412431)
      ·
        refine ⟨24905994757579966242618647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16603996505053310828412431 24905994757579966242618647)
        ·
          refine ⟨37358992136369949363927971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24905994757579966242618647 37358992136369949363927971)
          ·
            refine ⟨56038488204554924045891957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37358992136369949363927971 56038488204554924045891957)
            ·
              refine ⟨5253608269177024129302371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56038488204554924045891957 5253608269177024129302371)
              ·
                refine ⟨7880412403765536193953557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253608269177024129302371 7880412403765536193953557)
                ·
                  refine ⟨369394331426509509091573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7880412403765536193953557 369394331426509509091573)
                  ·
                    rfl

theorem cell23_6474536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 6].length) (baseStart_6474536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474536 prefixEnd_6474536 := by exact prefixLift 6474536
  have htrace : WordTrace (prefixWord ++ tailWord_6474536) baseStart_6474536 baseEnd_6474536 := by
    simpa [prefixWord, tailWord_6474536, baseEnd_6474536] using wordTrace_append hprefix tailTrace_6474536
  have hstable : (prefixWord ++ tailWord_6474536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474536).length < 2 ^ (prefixWord ++ tailWord_6474536).sum := by decide
  have hdescent : baseEnd_6474536 < baseStart_6474536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474539 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 1, 5, 2]
def baseStart_6474539 : Nat := 118140960795 + 6474539 * 2 ^ 59
def prefixEnd_6474539 : Nat := 4983230072969 + 3 ^ 40 * 6474539 * 2
def baseEnd_6474539 : Nat := 3324550523280549070086643

theorem tailTrace_6474539 : CollatzResearch.WordTrace tailWord_6474539 prefixEnd_6474539 3324550523280549070086643 := by
  unfold tailWord_6474539
  simp only [CollatzResearch.WordTrace]
  refine ⟨236145837490858441072002671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157430558327238960714668447 236145837490858441072002671)
  ·
    refine ⟨354218756236287661608004007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236145837490858441072002671 354218756236287661608004007)
    ·
      refine ⟨531328134354431492412006011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354218756236287661608004007 531328134354431492412006011)
      ·
        refine ⟨796992201531647238618009017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531328134354431492412006011 796992201531647238618009017)
        ·
          refine ⟨597744151148735428963506763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796992201531647238618009017 597744151148735428963506763)
          ·
            refine ⟨896616226723103143445260145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597744151148735428963506763 896616226723103143445260145)
            ·
              refine ⟨672462170042327357583945109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896616226723103143445260145 672462170042327357583945109)
              ·
                refine ⟨31521664220734094886747427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 672462170042327357583945109 31521664220734094886747427)
                ·
                  refine ⟨47282496331101142330121141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31521664220734094886747427 47282496331101142330121141)
                  ·
                    refine ⟨4432734031040732093448857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47282496331101142330121141 4432734031040732093448857)
                    ·
                      refine ⟨3324550523280549070086643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432734031040732093448857 3324550523280549070086643)
                      ·
                        rfl

theorem cell23_6474539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 5, 2].length) (baseStart_6474539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474539 prefixEnd_6474539 := by exact prefixLift 6474539
  have htrace : WordTrace (prefixWord ++ tailWord_6474539) baseStart_6474539 baseEnd_6474539 := by
    simpa [prefixWord, tailWord_6474539, baseEnd_6474539] using wordTrace_append hprefix tailTrace_6474539
  have hstable : (prefixWord ++ tailWord_6474539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474539).length < 2 ^ (prefixWord ++ tailWord_6474539).sum := by decide
  have hdescent : baseEnd_6474539 < baseStart_6474539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474546 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_6474546 : Nat := 118140960795 + 6474546 * 2 ^ 59
def prefixEnd_6474546 : Nat := 4983230072969 + 3 ^ 40 * 6474546 * 2
def baseEnd_6474546 : Nat := 3324554117645130542699111

theorem tailTrace_6474546 : CollatzResearch.WordTrace tailWord_6474546 prefixEnd_6474546 3324554117645130542699111 := by
  unfold tailWord_6474546
  simp only [CollatzResearch.WordTrace]
  refine ⟨59036523200458270316876873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157430728534555387511671661 59036523200458270316876873)
  ·
    refine ⟨44277392400343702737657655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59036523200458270316876873 44277392400343702737657655)
    ·
      refine ⟨66416088600515554106486483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44277392400343702737657655 66416088600515554106486483)
      ·
        refine ⟨99624132900773331159729725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66416088600515554106486483 99624132900773331159729725)
        ·
          refine ⟨37359049837789999184898647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99624132900773331159729725 37359049837789999184898647)
          ·
            refine ⟨56038574756684998777347971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37359049837789999184898647 56038574756684998777347971)
            ·
              refine ⟨84057862135027498166021957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56038574756684998777347971 84057862135027498166021957)
              ·
                refine ⟨15760849150317655906129117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84057862135027498166021957 15760849150317655906129117)
                ·
                  refine ⟨5910318431369120964798419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15760849150317655906129117 5910318431369120964798419)
                  ·
                    refine ⟨8865477647053681447197629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910318431369120964798419 8865477647053681447197629)
                    ·
                      refine ⟨3324554117645130542699111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8865477647053681447197629 3324554117645130542699111)
                      ·
                        rfl

theorem cell23_6474546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_6474546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474546 prefixEnd_6474546 := by exact prefixLift 6474546
  have htrace : WordTrace (prefixWord ++ tailWord_6474546) baseStart_6474546 baseEnd_6474546 := by
    simpa [prefixWord, tailWord_6474546, baseEnd_6474546] using wordTrace_append hprefix tailTrace_6474546
  have hstable : (prefixWord ++ tailWord_6474546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474546).length < 2 ^ (prefixWord ++ tailWord_6474546).sum := by decide
  have hdescent : baseEnd_6474546 < baseStart_6474546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474556 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_6474556 : Nat := 118140960795 + 6474556 * 2 ^ 59
def prefixEnd_6474556 : Nat := 4983230072969 + 3 ^ 40 * 6474556 * 2
def baseEnd_6474556 : Nat := 3324559252451675503574065

theorem tailTrace_6474556 : CollatzResearch.WordTrace tailWord_6474556 prefixEnd_6474556 3324559252451675503574065 := by
  unfold tailWord_6474556
  simp only [CollatzResearch.WordTrace]
  refine ⟨118073228765898426487685761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157430971687864568650247681 118073228765898426487685761)
  ·
    refine ⟨88554921574423819865764321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118073228765898426487685761 88554921574423819865764321)
    ·
      refine ⟨66416191180817864899323241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88554921574423819865764321 66416191180817864899323241)
      ·
        refine ⟨49812143385613398674492431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66416191180817864899323241 49812143385613398674492431)
        ·
          refine ⟨74718215078420098011738647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49812143385613398674492431 74718215078420098011738647)
          ·
            refine ⟨112077322617630147017607971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74718215078420098011738647 112077322617630147017607971)
            ·
              refine ⟨168115983926445220526411957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112077322617630147017607971 168115983926445220526411957)
              ·
                refine ⟨15760873493104239424351121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168115983926445220526411957 15760873493104239424351121)
                ·
                  refine ⟨11820655119828179568263341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15760873493104239424351121 11820655119828179568263341)
                  ·
                    refine ⟨4432745669935567338098753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11820655119828179568263341 4432745669935567338098753)
                    ·
                      refine ⟨3324559252451675503574065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432745669935567338098753 3324559252451675503574065)
                      ·
                        rfl

theorem cell23_6474556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_6474556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474556 prefixEnd_6474556 := by exact prefixLift 6474556
  have htrace : WordTrace (prefixWord ++ tailWord_6474556) baseStart_6474556 baseEnd_6474556 := by
    simpa [prefixWord, tailWord_6474556, baseEnd_6474556] using wordTrace_append hprefix tailTrace_6474556
  have hstable : (prefixWord ++ tailWord_6474556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474556).length < 2 ^ (prefixWord ++ tailWord_6474556).sum := by decide
  have hdescent : baseEnd_6474556 < baseStart_6474556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474557 : List Nat := [1, 4, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_6474557 : Nat := 118140960795 + 6474557 * 2 ^ 59
def prefixEnd_6474557 : Nat := 4983230072969 + 3 ^ 40 * 6474557 * 2
def baseEnd_6474557 : Nat := 1108186588644109999887187

theorem tailTrace_6474557 : CollatzResearch.WordTrace tailWord_6474557 prefixEnd_6474557 1108186588644109999887187 := by
  unfold tailWord_6474557
  simp only [CollatzResearch.WordTrace]
  refine ⟨236146494004793230146157925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157430996003195486764105283 236146494004793230146157925)
  ·
    refine ⟨44277467625898730652404611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236146494004793230146157925 44277467625898730652404611)
    ·
      refine ⟨66416201438848095978606917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44277467625898730652404611 66416201438848095978606917)
      ·
        refine ⟨12453037769784017995988797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66416201438848095978606917 12453037769784017995988797)
        ·
          refine ⟨4669889163669006748495799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12453037769784017995988797 4669889163669006748495799)
          ·
            refine ⟨7004833745503510122743699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669889163669006748495799 7004833745503510122743699)
            ·
              refine ⟨10507250618255265184115549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004833745503510122743699 10507250618255265184115549)
              ·
                refine ⟨3940218981845724444043331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10507250618255265184115549 3940218981845724444043331)
                ·
                  refine ⟨5910328472768586666064997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940218981845724444043331 5910328472768586666064997)
                  ·
                    refine ⟨1108186588644109999887187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5910328472768586666064997 1108186588644109999887187)
                    ·
                      rfl

theorem cell23_6474557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_6474557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474557 prefixEnd_6474557 := by exact prefixLift 6474557
  have htrace : WordTrace (prefixWord ++ tailWord_6474557) baseStart_6474557 baseEnd_6474557 := by
    simpa [prefixWord, tailWord_6474557, baseEnd_6474557] using wordTrace_append hprefix tailTrace_6474557
  have hstable : (prefixWord ++ tailWord_6474557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474557).length < 2 ^ (prefixWord ++ tailWord_6474557).sum := by decide
  have hdescent : baseEnd_6474557 < baseStart_6474557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474580 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_6474580 : Nat := 118140960795 + 6474580 * 2 ^ 59
def prefixEnd_6474580 : Nat := 4983230072969 + 3 ^ 40 * 6474580 * 2
def baseEnd_6474580 : Nat := 3324571575987383409673955

theorem tailTrace_6474580 : CollatzResearch.WordTrace tailWord_6474580 prefixEnd_6474580 3324571575987383409673955 := by
  unfold tailWord_6474580
  simp only [CollatzResearch.WordTrace]
  refine ⟨118073666441854952537122597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157431555255806603382830129 118073666441854952537122597)
  ·
    refine ⟨22138812457847803600710487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118073666441854952537122597 22138812457847803600710487)
    ·
      refine ⟨33208218686771705401065731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22138812457847803600710487 33208218686771705401065731)
      ·
        refine ⟨49812328030157558101598597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33208218686771705401065731 49812328030157558101598597)
        ·
          refine ⟨9339811505654542144049737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49812328030157558101598597 9339811505654542144049737)
          ·
            refine ⟨7004858629240906608037303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9339811505654542144049737 7004858629240906608037303)
            ·
              refine ⟨10507287943861359912055955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004858629240906608037303 10507287943861359912055955)
              ·
                refine ⟨15760931915792039868083933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10507287943861359912055955 15760931915792039868083933)
                ·
                  refine ⟨5910349468422014950531475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15760931915792039868083933 5910349468422014950531475)
                  ·
                    refine ⟨8865524202633022425797213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910349468422014950531475 8865524202633022425797213)
                    ·
                      refine ⟨3324571575987383409673955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8865524202633022425797213 3324571575987383409673955)
                      ·
                        rfl

theorem cell23_6474580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_6474580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474580 prefixEnd_6474580 := by exact prefixLift 6474580
  have htrace : WordTrace (prefixWord ++ tailWord_6474580) baseStart_6474580 baseEnd_6474580 := by
    simpa [prefixWord, tailWord_6474580, baseEnd_6474580] using wordTrace_append hprefix tailTrace_6474580
  have hstable : (prefixWord ++ tailWord_6474580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474580).length < 2 ^ (prefixWord ++ tailWord_6474580).sum := by decide
  have hdescent : baseEnd_6474580 < baseStart_6474580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474599 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_6474599 : Nat := 118140960795 + 6474599 * 2 ^ 59
def prefixEnd_6474599 : Nat := 4983230072969 + 3 ^ 40 * 6474599 * 2
def baseEnd_6474599 : Nat := 3324581332119818835336367

theorem tailTrace_6474599 : CollatzResearch.WordTrace tailWord_6474599 prefixEnd_6474599 3324581332119818835336367 := by
  unfold tailWord_6474599
  simp only [CollatzResearch.WordTrace]
  refine ⟨236148025870641071319186851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157432017247094047546124567 236148025870641071319186851)
  ·
    refine ⟨354222038805961606978780277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236148025870641071319186851 354222038805961606978780277)
    ·
      refine ⟨33208316138058900654260651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 354222038805961606978780277 33208316138058900654260651)
      ·
        refine ⟨49812474207088350981390977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33208316138058900654260651 49812474207088350981390977)
        ·
          refine ⟨37359355655316263236043233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49812474207088350981390977 37359355655316263236043233)
          ·
            refine ⟨28019516741487197427032425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37359355655316263236043233 28019516741487197427032425)
            ·
              refine ⟨21014637556115398070274319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28019516741487197427032425 21014637556115398070274319)
              ·
                refine ⟨31521956334173097105411479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21014637556115398070274319 31521956334173097105411479)
                ·
                  refine ⟨47282934501259645658117219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31521956334173097105411479 47282934501259645658117219)
                  ·
                    refine ⟨70924401751889468487175829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47282934501259645658117219 70924401751889468487175829)
                    ·
                      refine ⟨3324581332119818835336367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70924401751889468487175829 3324581332119818835336367)
                      ·
                        rfl

theorem cell23_6474599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_6474599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474599 prefixEnd_6474599 := by exact prefixLift 6474599
  have htrace : WordTrace (prefixWord ++ tailWord_6474599) baseStart_6474599 baseEnd_6474599 := by
    simpa [prefixWord, tailWord_6474599, baseEnd_6474599] using wordTrace_append hprefix tailTrace_6474599
  have hstable : (prefixWord ++ tailWord_6474599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474599).length < 2 ^ (prefixWord ++ tailWord_6474599).sum := by decide
  have hdescent : baseEnd_6474599 < baseStart_6474599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474619 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 3]
def baseStart_6474619 : Nat := 118140960795 + 6474619 * 2 ^ 59
def prefixEnd_6474619 : Nat := 4983230072969 + 3 ^ 40 * 6474619 * 2
def baseEnd_6474619 : Nat := 3324591601732908757086275

theorem tailTrace_6474619 : CollatzResearch.WordTrace tailWord_6474619 prefixEnd_6474619 3324591601732908757086275 := by
  unfold tailWord_6474619
  simp only [CollatzResearch.WordTrace]
  refine ⟨236148755330568614734914911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157432503553712409823276607 236148755330568614734914911)
  ·
    refine ⟨354223132995852922102372367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236148755330568614734914911 354223132995852922102372367)
    ·
      refine ⟨531334699493779383153558551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354223132995852922102372367 531334699493779383153558551)
      ·
        refine ⟨797002049240669074730337827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531334699493779383153558551 797002049240669074730337827)
        ·
          refine ⟨1195503073861003612095506741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797002049240669074730337827 1195503073861003612095506741)
          ·
            refine ⟨112078413174469088633953757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1195503073861003612095506741 112078413174469088633953757)
            ·
              refine ⟨42029404940425908237732659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112078413174469088633953757 42029404940425908237732659)
              ·
                refine ⟨63044107410638862356598989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42029404940425908237732659 63044107410638862356598989)
                ·
                  refine ⟨23641540278989573383724621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63044107410638862356598989 23641540278989573383724621)
                  ·
                    refine ⟨8865577604621090018896733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23641540278989573383724621 8865577604621090018896733)
                    ·
                      refine ⟨3324591601732908757086275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8865577604621090018896733 3324591601732908757086275)
                      ·
                        rfl

theorem cell23_6474619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 3].length) (baseStart_6474619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474619 prefixEnd_6474619 := by exact prefixLift 6474619
  have htrace : WordTrace (prefixWord ++ tailWord_6474619) baseStart_6474619 baseEnd_6474619 := by
    simpa [prefixWord, tailWord_6474619, baseEnd_6474619] using wordTrace_append hprefix tailTrace_6474619
  have hstable : (prefixWord ++ tailWord_6474619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474619).length < 2 ^ (prefixWord ++ tailWord_6474619).sum := by decide
  have hdescent : baseEnd_6474619 < baseStart_6474619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474626 : List Nat := [3, 4, 2, 2, 12]
def baseStart_6474626 : Nat := 118140960795 + 6474626 * 2 ^ 59
def prefixEnd_6474626 : Nat := 4983230072969 + 3 ^ 40 * 6474626 * 2
def baseEnd_6474626 : Nat := 4560487237445116913167

theorem tailTrace_6474626 : CollatzResearch.WordTrace tailWord_6474626 prefixEnd_6474626 4560487237445116913167 := by
  unfold tailWord_6474626
  simp only [CollatzResearch.WordTrace]
  refine ⟨59037252660385813732604933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157432673761028836620279821 59037252660385813732604933)
  ·
    refine ⟨11069484873822340074863425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59037252660385813732604933 11069484873822340074863425)
    ·
      refine ⟨8302113655366755056147569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11069484873822340074863425 8302113655366755056147569)
      ·
        refine ⟨6226585241525066292110677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8302113655366755056147569 6226585241525066292110677)
        ·
          refine ⟨4560487237445116913167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6226585241525066292110677 4560487237445116913167)
          ·
            rfl

theorem cell23_6474626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 12].length) (baseStart_6474626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474626 prefixEnd_6474626 := by exact prefixLift 6474626
  have htrace : WordTrace (prefixWord ++ tailWord_6474626) baseStart_6474626 baseEnd_6474626 := by
    simpa [prefixWord, tailWord_6474626, baseEnd_6474626] using wordTrace_append hprefix tailTrace_6474626
  have hstable : (prefixWord ++ tailWord_6474626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474626).length < 2 ^ (prefixWord ++ tailWord_6474626).sum := by decide
  have hdescent : baseEnd_6474626 < baseStart_6474626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474636 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_6474636 : Nat := 118140960795 + 6474636 * 2 ^ 59
def prefixEnd_6474636 : Nat := 4983230072969 + 3 ^ 40 * 6474636 * 2
def baseEnd_6474636 : Nat := 3324600330904035190573697

theorem tailTrace_6474636 : CollatzResearch.WordTrace tailWord_6474636 prefixEnd_6474636 3324600330904035190573697 := by
  unfold tailWord_6474636
  simp only [CollatzResearch.WordTrace]
  refine ⟨118074687685753513319141881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157432916914338017758855841 118074687685753513319141881)
  ·
    refine ⟨88556015764315134989356411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118074687685753513319141881 88556015764315134989356411)
    ·
      refine ⟨132834023646472702484034617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88556015764315134989356411 132834023646472702484034617)
      ·
        refine ⟨99625517734854526863025963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132834023646472702484034617 99625517734854526863025963)
        ·
          refine ⟨149438276602281790294538945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99625517734854526863025963 149438276602281790294538945)
          ·
            refine ⟨112078707451711342720904209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149438276602281790294538945 112078707451711342720904209)
            ·
              refine ⟨84059030588783507040678157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112078707451711342720904209 84059030588783507040678157)
              ·
                refine ⟨31522136470793815140254309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84059030588783507040678157 31522136470793815140254309)
                ·
                  refine ⟨5910400588273840338797683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31522136470793815140254309 5910400588273840338797683)
                  ·
                    refine ⟨8865600882410760508196525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910400588273840338797683 8865600882410760508196525)
                    ·
                      refine ⟨3324600330904035190573697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8865600882410760508196525 3324600330904035190573697)
                      ·
                        rfl

theorem cell23_6474636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_6474636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474636 prefixEnd_6474636 := by exact prefixLift 6474636
  have htrace : WordTrace (prefixWord ++ tailWord_6474636) baseStart_6474636 baseEnd_6474636 := by
    simpa [prefixWord, tailWord_6474636, baseEnd_6474636] using wordTrace_append hprefix tailTrace_6474636
  have hstable : (prefixWord ++ tailWord_6474636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474636).length < 2 ^ (prefixWord ++ tailWord_6474636).sum := by decide
  have hdescent : baseEnd_6474636 < baseStart_6474636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474653 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_6474653 : Nat := 118140960795 + 6474653 * 2 ^ 59
def prefixEnd_6474653 : Nat := 4983230072969 + 3 ^ 40 * 6474653 * 2
def baseEnd_6474653 : Nat := 3324609060075161624061119

theorem tailTrace_6474653 : CollatzResearch.WordTrace tailWord_6474653 prefixEnd_6474653 3324609060075161624061119 := by
  unfold tailWord_6474653
  simp only [CollatzResearch.WordTrace]
  refine ⟨236149995412445438541652613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157433330274963625694435075 236149995412445438541652613)
  ·
    refine ⟨44278124139833519726559865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236149995412445438541652613 44278124139833519726559865)
    ·
      refine ⟨33208593104875139794919899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44278124139833519726559865 33208593104875139794919899)
      ·
        refine ⟨49812889657312709692379849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33208593104875139794919899 49812889657312709692379849)
        ·
          refine ⟨37359667242984532269284887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49812889657312709692379849 37359667242984532269284887)
          ·
            refine ⟨56039500864476798403927331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37359667242984532269284887 56039500864476798403927331)
            ·
              refine ⟨84059251296715197605890997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56039500864476798403927331 84059251296715197605890997)
              ·
                refine ⟨7880554809067049775552281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84059251296715197605890997 7880554809067049775552281)
                ·
                  refine ⟨5910416106800287331664211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7880554809067049775552281 5910416106800287331664211)
                  ·
                    refine ⟨8865624160200430997496317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910416106800287331664211 8865624160200430997496317)
                    ·
                      refine ⟨3324609060075161624061119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8865624160200430997496317 3324609060075161624061119)
                      ·
                        rfl

theorem cell23_6474653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_6474653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474653 prefixEnd_6474653 := by exact prefixLift 6474653
  have htrace : WordTrace (prefixWord ++ tailWord_6474653) baseStart_6474653 baseEnd_6474653 := by
    simpa [prefixWord, tailWord_6474653, baseEnd_6474653] using wordTrace_append hprefix tailTrace_6474653
  have hstable : (prefixWord ++ tailWord_6474653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474653).length < 2 ^ (prefixWord ++ tailWord_6474653).sum := by decide
  have hdescent : baseEnd_6474653 < baseStart_6474653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474679 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_6474679 : Nat := 118140960795 + 6474679 * 2 ^ 59
def prefixEnd_6474679 : Nat := 4983230072969 + 3 ^ 40 * 6474679 * 2
def baseEnd_6474679 : Nat := 3324622410572178522335999

theorem tailTrace_6474679 : CollatzResearch.WordTrace tailWord_6474679 prefixEnd_6474679 3324622410572178522335999 := by
  unfold tailWord_6474679
  simp only [CollatzResearch.WordTrace]
  refine ⟨236150943710351244982099091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157433962473567496654732727 236150943710351244982099091)
  ·
    refine ⟨354226415565526867473148637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236150943710351244982099091 354226415565526867473148637)
    ·
      refine ⟨132834905837072575302430739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354226415565526867473148637 132834905837072575302430739)
      ·
        refine ⟨199252358755608862953646109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132834905837072575302430739 199252358755608862953646109)
        ·
          refine ⟨74719634533353323607617291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199252358755608862953646109 74719634533353323607617291)
          ·
            refine ⟨112079451800029985411425937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74719634533353323607617291 112079451800029985411425937)
            ·
              refine ⟨84059588850022489058569453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112079451800029985411425937 84059588850022489058569453)
              ·
                refine ⟨31522345818758433396963545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84059588850022489058569453 31522345818758433396963545)
                ·
                  refine ⟨23641759364068825047722659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31522345818758433396963545 23641759364068825047722659)
                  ·
                    refine ⟨35462639046103237571583989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23641759364068825047722659 35462639046103237571583989)
                    ·
                      refine ⟨3324622410572178522335999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35462639046103237571583989 3324622410572178522335999)
                      ·
                        rfl

theorem cell23_6474679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_6474679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474679 prefixEnd_6474679 := by exact prefixLift 6474679
  have htrace : WordTrace (prefixWord ++ tailWord_6474679) baseStart_6474679 baseEnd_6474679 := by
    simpa [prefixWord, tailWord_6474679, baseEnd_6474679] using wordTrace_append hprefix tailTrace_6474679
  have hstable : (prefixWord ++ tailWord_6474679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474679).length < 2 ^ (prefixWord ++ tailWord_6474679).sum := by decide
  have hdescent : baseEnd_6474679 < baseStart_6474679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474680 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 1, 3, 2]
def baseStart_6474680 : Nat := 118140960795 + 6474680 * 2 ^ 59
def prefixEnd_6474680 : Nat := 4983230072969 + 3 ^ 40 * 6474680 * 2
def baseEnd_6474680 : Nat := 3324622924052833018423495

theorem tailTrace_6474680 : CollatzResearch.WordTrace tailWord_6474680 prefixEnd_6474680 3324622924052833018423495 := by
  unfold tailWord_6474680
  simp only [CollatzResearch.WordTrace]
  refine ⟨118075490091673811076442747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157433986788898414768590329 118075490091673811076442747)
  ·
    refine ⟨177113235137510716614664121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118075490091673811076442747 177113235137510716614664121)
    ·
      refine ⟨132834926353133037460998091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177113235137510716614664121 132834926353133037460998091)
      ·
        refine ⟨199252389529699556191497137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132834926353133037460998091 199252389529699556191497137)
        ·
          refine ⟨149439292147274667143622853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199252389529699556191497137 149439292147274667143622853)
          ·
            refine ⟨28019867277614000089429285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149439292147274667143622853 28019867277614000089429285)
            ·
              refine ⟨5253725114552625016767991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28019867277614000089429285 5253725114552625016767991)
              ·
                refine ⟨7880587671828937525151987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253725114552625016767991 7880587671828937525151987)
                ·
                  refine ⟨11820881507743406287727981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7880587671828937525151987 11820881507743406287727981)
                  ·
                    refine ⟨4432830565403777357897993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11820881507743406287727981 4432830565403777357897993)
                    ·
                      refine ⟨3324622924052833018423495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432830565403777357897993 3324622924052833018423495)
                      ·
                        rfl

theorem cell23_6474680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_6474680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474680 prefixEnd_6474680 := by exact prefixLift 6474680
  have htrace : WordTrace (prefixWord ++ tailWord_6474680) baseStart_6474680 baseEnd_6474680 := by
    simpa [prefixWord, tailWord_6474680, baseEnd_6474680] using wordTrace_append hprefix tailTrace_6474680
  have hstable : (prefixWord ++ tailWord_6474680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474680).length < 2 ^ (prefixWord ++ tailWord_6474680).sum := by decide
  have hdescent : baseEnd_6474680 < baseStart_6474680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474699 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 7]
def baseStart_6474699 : Nat := 118140960795 + 6474699 * 2 ^ 59
def prefixEnd_6474699 : Nat := 4983230072969 + 3 ^ 40 * 6474699 * 2
def baseEnd_6474699 : Nat := 369403631131696493787323

theorem tailTrace_6474699 : CollatzResearch.WordTrace tailWord_6474699 prefixEnd_6474699 369403631131696493787323 := by
  unfold tailWord_6474699
  simp only [CollatzResearch.WordTrace]
  refine ⟨236151673170278788397827151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157434448780185858931884767 236151673170278788397827151)
  ·
    refine ⟨354227509755418182596740727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236151673170278788397827151 354227509755418182596740727)
    ·
      refine ⟨531341264633127273895111091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354227509755418182596740727 531341264633127273895111091)
      ·
        refine ⟨797011896949690910842666637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531341264633127273895111091 797011896949690910842666637)
        ·
          refine ⟨298879461356134091565999989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 797011896949690910842666637 298879461356134091565999989)
          ·
            refine ⟨28019949502137571084312499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298879461356134091565999989 28019949502137571084312499)
            ·
              refine ⟨42029924253206356626468749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28019949502137571084312499 42029924253206356626468749)
              ·
                refine ⟨15761221594952383734925781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42029924253206356626468749 15761221594952383734925781)
                ·
                  refine ⟨369403631131696493787323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15761221594952383734925781 369403631131696493787323)
                  ·
                    rfl

theorem cell23_6474699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 7].length) (baseStart_6474699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474699 prefixEnd_6474699 := by exact prefixLift 6474699
  have htrace : WordTrace (prefixWord ++ tailWord_6474699) baseStart_6474699 baseEnd_6474699 := by
    simpa [prefixWord, tailWord_6474699, baseEnd_6474699] using wordTrace_append hprefix tailTrace_6474699
  have hstable : (prefixWord ++ tailWord_6474699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474699).length < 2 ^ (prefixWord ++ tailWord_6474699).sum := by decide
  have hdescent : baseEnd_6474699 < baseStart_6474699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474729 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 8, 5]
def baseStart_6474729 : Nat := 118140960795 + 6474729 * 2 ^ 59
def prefixEnd_6474729 : Nat := 4983230072969 + 3 ^ 40 * 6474729 * 2
def baseEnd_6474729 : Nat := 1108216028201634442236923

theorem tailTrace_6474729 : CollatzResearch.WordTrace tailWord_6474729 prefixEnd_6474729 1108216028201634442236923 := by
  unfold tailWord_6474729
  simp only [CollatzResearch.WordTrace]
  refine ⟨236152767360170103521419241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157435178240113402347612827 236152767360170103521419241)
  ·
    refine ⟨177114575520127577641064431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236152767360170103521419241 177114575520127577641064431)
    ·
      refine ⟨265671863280191366461596647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177114575520127577641064431 265671863280191366461596647)
      ·
        refine ⟨398507794920287049692394971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265671863280191366461596647 398507794920287049692394971)
        ·
          refine ⟨597761692380430574538592457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398507794920287049692394971 597761692380430574538592457)
          ·
            refine ⟨448321269285322930903944343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597761692380430574538592457 448321269285322930903944343)
            ·
              refine ⟨672481903927984396355916515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448321269285322930903944343 672481903927984396355916515)
              ·
                refine ⟨1008722855891976594533874773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672481903927984396355916515 1008722855891976594533874773)
                ·
                  refine ⟨11820970967484100717193845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1008722855891976594533874773 11820970967484100717193845)
                  ·
                    refine ⟨1108216028201634442236923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11820970967484100717193845 1108216028201634442236923)
                    ·
                      rfl

theorem cell23_6474729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_6474729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474729 prefixEnd_6474729 := by exact prefixLift 6474729
  have htrace : WordTrace (prefixWord ++ tailWord_6474729) baseStart_6474729 baseEnd_6474729 := by
    simpa [prefixWord, tailWord_6474729, baseEnd_6474729] using wordTrace_append hprefix tailTrace_6474729
  have hstable : (prefixWord ++ tailWord_6474729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474729).length < 2 ^ (prefixWord ++ tailWord_6474729).sum := by decide
  have hdescent : baseEnd_6474729 < baseStart_6474729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474736 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 1, 7, 2]
def baseStart_6474736 : Nat := 118140960795 + 6474736 * 2 ^ 59
def prefixEnd_6474736 : Nat := 4983230072969 + 3 ^ 40 * 6474736 * 2
def baseEnd_6474736 : Nat := 3324651678969484799323237

theorem tailTrace_6474736 : CollatzResearch.WordTrace tailWord_6474736 prefixEnd_6474736 3324651678969484799323237 := by
  unfold tailWord_6474736
  simp only [CollatzResearch.WordTrace]
  refine ⟨118076511335572371858462031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157435348447429829144616041 118076511335572371858462031)
  ·
    refine ⟨177114767003358557787693047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118076511335572371858462031 177114767003358557787693047)
    ·
      refine ⟨265672150505037836681539571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177114767003358557787693047 265672150505037836681539571)
      ·
        refine ⟨398508225757556755022309357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265672150505037836681539571 398508225757556755022309357)
        ·
          refine ⟨149440584659083783133366009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398508225757556755022309357 149440584659083783133366009)
          ·
            refine ⟨112080438494312837350024507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149440584659083783133366009 112080438494312837350024507)
            ·
              refine ⟨168120657741469256025036761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112080438494312837350024507 168120657741469256025036761)
              ·
                refine ⟨126090493306101942018777571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168120657741469256025036761 126090493306101942018777571)
                ·
                  refine ⟨189135739959152913028166357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126090493306101942018777571 189135739959152913028166357)
                  ·
                    refine ⟨4432868905292646399097649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 189135739959152913028166357 4432868905292646399097649)
                    ·
                      refine ⟨3324651678969484799323237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4432868905292646399097649 3324651678969484799323237)
                      ·
                        rfl

theorem cell23_6474736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 7, 2].length) (baseStart_6474736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474736 prefixEnd_6474736 := by exact prefixLift 6474736
  have htrace : WordTrace (prefixWord ++ tailWord_6474736) baseStart_6474736 baseEnd_6474736 := by
    simpa [prefixWord, tailWord_6474736, baseEnd_6474736] using wordTrace_append hprefix tailTrace_6474736
  have hstable : (prefixWord ++ tailWord_6474736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474736).length < 2 ^ (prefixWord ++ tailWord_6474736).sum := by decide
  have hdescent : baseEnd_6474736 < baseStart_6474736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474750 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_6474750 : Nat := 118140960795 + 6474750 * 2 ^ 59
def prefixEnd_6474750 : Nat := 4983230072969 + 3 ^ 40 * 6474750 * 2
def baseEnd_6474750 : Nat := 369406540855405304949797

theorem tailTrace_6474750 : CollatzResearch.WordTrace tailWord_6474750 prefixEnd_6474750 369406540855405304949797 := by
  unfold tailWord_6474750
  simp only [CollatzResearch.WordTrace]
  refine ⟨29519191661636753013491713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157435688862062682738622469 29519191661636753013491713)
  ·
    refine ⟨22139393746227564760118785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29519191661636753013491713 22139393746227564760118785)
    ·
      refine ⟨16604545309670673570089089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22139393746227564760118785 16604545309670673570089089)
      ·
        refine ⟨12453408982253005177566817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16604545309670673570089089 12453408982253005177566817)
        ·
          refine ⟨9340056736689753883175113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12453408982253005177566817 9340056736689753883175113)
          ·
            refine ⟨7005042552517315412381335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9340056736689753883175113 7005042552517315412381335)
            ·
              refine ⟨10507563828775973118572003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005042552517315412381335 10507563828775973118572003)
              ·
                refine ⟨15761345743163959677858005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10507563828775973118572003 15761345743163959677858005)
                ·
                  refine ⟨369406540855405304949797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15761345743163959677858005 369406540855405304949797)
                  ·
                    rfl

theorem cell23_6474750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_6474750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474750 prefixEnd_6474750 := by exact prefixLift 6474750
  have htrace : WordTrace (prefixWord ++ tailWord_6474750) baseStart_6474750 baseEnd_6474750 := by
    simpa [prefixWord, tailWord_6474750, baseEnd_6474750] using wordTrace_append hprefix tailTrace_6474750
  have hstable : (prefixWord ++ tailWord_6474750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474750).length < 2 ^ (prefixWord ++ tailWord_6474750).sum := by decide
  have hdescent : baseEnd_6474750 < baseStart_6474750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474769 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_6474769 : Nat := 118140960795 + 6474769 * 2 ^ 59
def prefixEnd_6474769 : Nat := 4983230072969 + 3 ^ 40 * 6474769 * 2
def baseEnd_6474769 : Nat := 3324668623831083170210585

theorem tailTrace_6474769 : CollatzResearch.WordTrace tailWord_6474769 prefixEnd_6474769 3324668623831083170210585 := by
  unfold tailWord_6474769
  simp only [CollatzResearch.WordTrace]
  refine ⟨236154226280025190352875361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157436150853350126901916907 236154226280025190352875361)
  ·
    refine ⟨177115669710018892764656521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236154226280025190352875361 177115669710018892764656521)
    ·
      refine ⟨132836752282514169573492391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177115669710018892764656521 132836752282514169573492391)
      ·
        refine ⟨199255128423771254360238587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132836752282514169573492391 199255128423771254360238587)
        ·
          refine ⟨298882692635656881540357881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199255128423771254360238587 298882692635656881540357881)
          ·
            refine ⟨224162019476742661155268411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298882692635656881540357881 224162019476742661155268411)
            ·
              refine ⟨336243029215113991732902617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224162019476742661155268411 336243029215113991732902617)
              ·
                refine ⟨252182271911335493799676963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336243029215113991732902617 252182271911335493799676963)
                ·
                  refine ⟨378273407867003240699515445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252182271911335493799676963 378273407867003240699515445)
                  ·
                    refine ⟨35463131987531553815579573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 378273407867003240699515445 35463131987531553815579573)
                    ·
                      refine ⟨3324668623831083170210585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35463131987531553815579573 3324668623831083170210585)
                      ·
                        rfl

theorem cell23_6474769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_6474769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474769 prefixEnd_6474769 := by exact prefixLift 6474769
  have htrace : WordTrace (prefixWord ++ tailWord_6474769) baseStart_6474769 baseEnd_6474769 := by
    simpa [prefixWord, tailWord_6474769, baseEnd_6474769] using wordTrace_append hprefix tailTrace_6474769
  have hstable : (prefixWord ++ tailWord_6474769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474769).length < 2 ^ (prefixWord ++ tailWord_6474769).sum := by decide
  have hdescent : baseEnd_6474769 < baseStart_6474769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474783 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 4]
def baseStart_6474783 : Nat := 118140960795 + 6474783 * 2 ^ 59
def prefixEnd_6474783 : Nat := 4983230072969 + 3 ^ 40 * 6474783 * 2
def baseEnd_6474783 : Nat := 3324675812560246115435521

theorem tailTrace_6474783 : CollatzResearch.WordTrace tailWord_6474783 prefixEnd_6474783 3324675812560246115435521 := by
  unfold tailWord_6474783
  simp only [CollatzResearch.WordTrace]
  refine ⟨236154736901974470743885003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157436491267982980495923335 236154736901974470743885003)
  ·
    refine ⟨354232105352961706115827505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236154736901974470743885003 354232105352961706115827505)
    ·
      refine ⟨265674079014721279586870629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354232105352961706115827505 265674079014721279586870629)
      ·
        refine ⟨49813889815260239922538243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265674079014721279586870629 49813889815260239922538243)
        ·
          refine ⟨74720834722890359883807365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49813889815260239922538243 74720834722890359883807365)
          ·
            refine ⟨14010156510541942478213881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74720834722890359883807365 14010156510541942478213881)
            ·
              refine ⟨10507617382906456858660411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14010156510541942478213881 10507617382906456858660411)
              ·
                refine ⟨15761426074359685287990617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10507617382906456858660411 15761426074359685287990617)
                ·
                  refine ⟨11821069555769763965992963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15761426074359685287990617 11821069555769763965992963)
                  ·
                    refine ⟨17731604333654645948989445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11821069555769763965992963 17731604333654645948989445)
                    ·
                      refine ⟨3324675812560246115435521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17731604333654645948989445 3324675812560246115435521)
                      ·
                        rfl

theorem cell23_6474783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_6474783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474783 prefixEnd_6474783 := by exact prefixLift 6474783
  have htrace : WordTrace (prefixWord ++ tailWord_6474783) baseStart_6474783 baseEnd_6474783 := by
    simpa [prefixWord, tailWord_6474783, baseEnd_6474783] using wordTrace_append hprefix tailTrace_6474783
  have hstable : (prefixWord ++ tailWord_6474783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474783).length < 2 ^ (prefixWord ++ tailWord_6474783).sum := by decide
  have hdescent : baseEnd_6474783 < baseStart_6474783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474833 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_6474833 : Nat := 118140960795 + 6474833 * 2 ^ 59
def prefixEnd_6474833 : Nat := 4983230072969 + 3 ^ 40 * 6474833 * 2
def baseEnd_6474833 : Nat := 3324701486592970919810291

theorem tailTrace_6474833 : CollatzResearch.WordTrace tailWord_6474833 prefixEnd_6474833 3324701486592970919810291 := by
  unfold tailWord_6474833
  simp only [CollatzResearch.WordTrace]
  refine ⟨236156560551793329283205153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157437707034528886188803435 236156560551793329283205153)
  ·
    refine ⟨177117420413844996962403865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236156560551793329283205153 177117420413844996962403865)
    ·
      refine ⟨132838065310383747721802899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177117420413844996962403865 132838065310383747721802899)
      ·
        refine ⟨199257097965575621582704349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132838065310383747721802899 199257097965575621582704349)
        ·
          refine ⟨74721411737090858093514131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199257097965575621582704349 74721411737090858093514131)
          ·
            refine ⟨112082117605636287140271197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74721411737090858093514131 112082117605636287140271197)
            ·
              refine ⟨42030794102113607677601699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112082117605636287140271197 42030794102113607677601699)
              ·
                refine ⟨63046191153170411516402549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42030794102113607677601699 63046191153170411516402549)
                ·
                  refine ⟨5910580420609726079662739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63046191153170411516402549 5910580420609726079662739)
                  ·
                    refine ⟨8865870630914589119494109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910580420609726079662739 8865870630914589119494109)
                    ·
                      refine ⟨3324701486592970919810291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8865870630914589119494109 3324701486592970919810291)
                      ·
                        rfl

theorem cell23_6474833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_6474833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474833 prefixEnd_6474833 := by exact prefixLift 6474833
  have htrace : WordTrace (prefixWord ++ tailWord_6474833) baseStart_6474833 baseEnd_6474833 := by
    simpa [prefixWord, tailWord_6474833, baseEnd_6474833] using wordTrace_append hprefix tailTrace_6474833
  have hstable : (prefixWord ++ tailWord_6474833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474833).length < 2 ^ (prefixWord ++ tailWord_6474833).sum := by decide
  have hdescent : baseEnd_6474833 < baseStart_6474833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474853 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_6474853 : Nat := 118140960795 + 6474853 * 2 ^ 59
def prefixEnd_6474853 : Nat := 4983230072969 + 3 ^ 40 * 6474853 * 2
def baseEnd_6474853 : Nat := 1108237252068686947186733

theorem tailTrace_6474853 : CollatzResearch.WordTrace tailWord_6474853 prefixEnd_6474853 1108237252068686947186733 := by
  unfold tailWord_6474853
  simp only [CollatzResearch.WordTrace]
  refine ⟨236157290011720872698933213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157438193341147248465955475 236157290011720872698933213)
  ·
    refine ⟨88558983754395327262099955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236157290011720872698933213 88558983754395327262099955)
    ·
      refine ⟨132838475631592990893149933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88558983754395327262099955 132838475631592990893149933)
      ·
        refine ⟨49814428361847371584931225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132838475631592990893149933 49814428361847371584931225)
        ·
          refine ⟨37360821271385528688698419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49814428361847371584931225 37360821271385528688698419)
          ·
            refine ⟨56041231907078293033047629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37360821271385528688698419 56041231907078293033047629)
            ·
              refine ⟨21015461965154359887392861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56041231907078293033047629 21015461965154359887392861)
              ·
                refine ⟨7880798236932884957772323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21015461965154359887392861 7880798236932884957772323)
                ·
                  refine ⟨11821197355399327436658485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7880798236932884957772323 11821197355399327436658485)
                  ·
                    refine ⟨1108237252068686947186733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11821197355399327436658485 1108237252068686947186733)
                    ·
                      rfl

theorem cell23_6474853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_6474853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474853 prefixEnd_6474853 := by exact prefixLift 6474853
  have htrace : WordTrace (prefixWord ++ tailWord_6474853) baseStart_6474853 baseEnd_6474853 := by
    simpa [prefixWord, tailWord_6474853, baseEnd_6474853] using wordTrace_append hprefix tailTrace_6474853
  have hstable : (prefixWord ++ tailWord_6474853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474853).length < 2 ^ (prefixWord ++ tailWord_6474853).sum := by decide
  have hdescent : baseEnd_6474853 < baseStart_6474853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474890 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_6474890 : Nat := 118140960795 + 6474890 * 2 ^ 59
def prefixEnd_6474890 : Nat := 4983230072969 + 3 ^ 40 * 6474890 * 2
def baseEnd_6474890 : Nat := 3324730754990277196797529

theorem tailTrace_6474890 : CollatzResearch.WordTrace tailWord_6474890 prefixEnd_6474890 3324730754990277196797529 := by
  unfold tailWord_6474890
  simp only [CollatzResearch.WordTrace]
  refine ⟨59039659878146707004507531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157439093008391218678686749 59039659878146707004507531)
  ·
    refine ⟨88559489817220060506761297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59039659878146707004507531 88559489817220060506761297)
    ·
      refine ⟨66419617362915045380070973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88559489817220060506761297 66419617362915045380070973)
      ·
        refine ⟨24907356511093142017526615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66419617362915045380070973 24907356511093142017526615)
        ·
          refine ⟨37361034766639713026289923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24907356511093142017526615 37361034766639713026289923)
          ·
            refine ⟨56041552149959569539434885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37361034766639713026289923 56041552149959569539434885)
            ·
              refine ⟨10507791028117419288644041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56041552149959569539434885 10507791028117419288644041)
              ·
                refine ⟨7880843271088064466483031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10507791028117419288644041 7880843271088064466483031)
                ·
                  refine ⟨11821264906632096699724547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7880843271088064466483031 11821264906632096699724547)
                  ·
                    refine ⟨17731897359948145049586821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11821264906632096699724547 17731897359948145049586821)
                    ·
                      refine ⟨3324730754990277196797529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17731897359948145049586821 3324730754990277196797529)
                      ·
                        rfl

theorem cell23_6474890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_6474890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474890 prefixEnd_6474890 := by exact prefixLift 6474890
  have htrace : WordTrace (prefixWord ++ tailWord_6474890) baseStart_6474890 baseEnd_6474890 := by
    simpa [prefixWord, tailWord_6474890, baseEnd_6474890] using wordTrace_append hprefix tailTrace_6474890
  have hstable : (prefixWord ++ tailWord_6474890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474890).length < 2 ^ (prefixWord ++ tailWord_6474890).sum := by decide
  have hdescent : baseEnd_6474890 < baseStart_6474890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474910 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6474910 : Nat := 118140960795 + 6474910 * 2 ^ 59
def prefixEnd_6474910 : Nat := 4983230072969 + 3 ^ 40 * 6474910 * 2
def baseEnd_6474910 : Nat := 3324741024603367118547437

theorem tailTrace_6474910 : CollatzResearch.WordTrace tailWord_6474910 prefixEnd_6474910 3324741024603367118547437 := by
  unfold tailWord_6474910
  simp only [CollatzResearch.WordTrace]
  refine ⟨29519921121564296429219773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157439579315009580955838789 29519921121564296429219773)
  ·
    refine ⟨11069970420586611160957415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29519921121564296429219773 11069970420586611160957415)
    ·
      refine ⟨16604955630879916741436123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11069970420586611160957415 16604955630879916741436123)
      ·
        refine ⟨24907433446319875112154185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16604955630879916741436123 24907433446319875112154185)
        ·
          refine ⟨18680575084739906334115639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24907433446319875112154185 18680575084739906334115639)
          ·
            refine ⟨28020862627109859501173459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18680575084739906334115639 28020862627109859501173459)
            ·
              refine ⟨42031293940664789251760189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28020862627109859501173459 42031293940664789251760189)
              ·
                refine ⟨15761735227749295969410071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42031293940664789251760189 15761735227749295969410071)
                ·
                  refine ⟨23642602841623943954115107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15761735227749295969410071 23642602841623943954115107)
                  ·
                    refine ⟨35463904262435915931172661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23642602841623943954115107 35463904262435915931172661)
                    ·
                      refine ⟨3324741024603367118547437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35463904262435915931172661 3324741024603367118547437)
                      ·
                        rfl

theorem cell23_6474910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6474910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474910 prefixEnd_6474910 := by exact prefixLift 6474910
  have htrace : WordTrace (prefixWord ++ tailWord_6474910) baseStart_6474910 baseEnd_6474910 := by
    simpa [prefixWord, tailWord_6474910, baseEnd_6474910] using wordTrace_append hprefix tailTrace_6474910
  have hstable : (prefixWord ++ tailWord_6474910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474910).length < 2 ^ (prefixWord ++ tailWord_6474910).sum := by decide
  have hdescent : baseEnd_6474910 < baseStart_6474910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474936 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_6474936 : Nat := 118140960795 + 6474936 * 2 ^ 59
def prefixEnd_6474936 : Nat := 4983230072969 + 3 ^ 40 * 6474936 * 2
def baseEnd_6474936 : Nat := 3324754375100384016822317

theorem tailTrace_6474936 : CollatzResearch.WordTrace tailWord_6474936 prefixEnd_6474936 3324754375100384016822317 := by
  unfold tailWord_6474936
  simp only [CollatzResearch.WordTrace]
  refine ⟨118080158635210088937102331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157440211513613451916136441 118080158635210088937102331)
  ·
    refine ⟨177120237952815133405653497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118080158635210088937102331 177120237952815133405653497)
    ·
      refine ⟨132840178464611350054240123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177120237952815133405653497 132840178464611350054240123)
      ·
        refine ⟨199260267696917025081360185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132840178464611350054240123 199260267696917025081360185)
        ·
          refine ⟨149445200772687768811020139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199260267696917025081360185 149445200772687768811020139)
          ·
            refine ⟨224167801159031653216530209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149445200772687768811020139 224167801159031653216530209)
            ·
              refine ⟨168125850869273739912397657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224167801159031653216530209 168125850869273739912397657)
              ·
                refine ⟨126094388151955304934298243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168125850869273739912397657 126094388151955304934298243)
                ·
                  refine ⟨189141582227932957401447365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126094388151955304934298243 189141582227932957401447365)
                  ·
                    refine ⟨35464046667737429512771381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189141582227932957401447365 35464046667737429512771381)
                    ·
                      refine ⟨3324754375100384016822317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35464046667737429512771381 3324754375100384016822317)
                      ·
                        rfl

theorem cell23_6474936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_6474936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474936 prefixEnd_6474936 := by exact prefixLift 6474936
  have htrace : WordTrace (prefixWord ++ tailWord_6474936) baseStart_6474936 baseEnd_6474936 := by
    simpa [prefixWord, tailWord_6474936, baseEnd_6474936] using wordTrace_append hprefix tailTrace_6474936
  have hstable : (prefixWord ++ tailWord_6474936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474936).length < 2 ^ (prefixWord ++ tailWord_6474936).sum := by decide
  have hdescent : baseEnd_6474936 < baseStart_6474936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6474944 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 1, 2, 3]
def baseStart_6474944 : Nat := 118140960795 + 6474944 * 2 ^ 59
def prefixEnd_6474944 : Nat := 4983230072969 + 3 ^ 40 * 6474944 * 2
def baseEnd_6474944 : Nat := 3324758482945619985522281

theorem tailTrace_6474944 : CollatzResearch.WordTrace tailWord_6474944 prefixEnd_6474944 3324758482945619985522281 := by
  unfold tailWord_6474944
  simp only [CollatzResearch.WordTrace]
  refine ⟨118080304527195597620247943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157440406036260796826997257 118080304527195597620247943)
  ·
    refine ⟨177120456790793396430371915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118080304527195597620247943 177120456790793396430371915)
    ·
      refine ⟨265680685186190094645557873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177120456790793396430371915 265680685186190094645557873)
      ·
        refine ⟨199260513889642570984168405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265680685186190094645557873 199260513889642570984168405)
        ·
          refine ⟨4670168294288497757441447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 199260513889642570984168405 4670168294288497757441447)
          ·
            refine ⟨7005252441432746636162171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670168294288497757441447 7005252441432746636162171)
            ·
              refine ⟨10507878662149119954243257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005252441432746636162171 10507878662149119954243257)
              ·
                refine ⟨7880908996611839965682443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10507878662149119954243257 7880908996611839965682443)
                ·
                  refine ⟨11821363494917759948523665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7880908996611839965682443 11821363494917759948523665)
                  ·
                    refine ⟨8866022621188319961392749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11821363494917759948523665 8866022621188319961392749)
                    ·
                      refine ⟨3324758482945619985522281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8866022621188319961392749 3324758482945619985522281)
                      ·
                        rfl

theorem cell23_6474944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_6474944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6474944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6474944 prefixEnd_6474944 := by exact prefixLift 6474944
  have htrace : WordTrace (prefixWord ++ tailWord_6474944) baseStart_6474944 baseEnd_6474944 := by
    simpa [prefixWord, tailWord_6474944, baseEnd_6474944] using wordTrace_append hprefix tailTrace_6474944
  have hstable : (prefixWord ++ tailWord_6474944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6474944).length < 2 ^ (prefixWord ++ tailWord_6474944).sum := by decide
  have hdescent : baseEnd_6474944 < baseStart_6474944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6474944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475013 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_6475013 : Nat := 118140960795 + 6475013 * 2 ^ 59
def prefixEnd_6475013 : Nat := 4983230072969 + 3 ^ 40 * 6475013 * 2
def baseEnd_6475013 : Nat := 3324793913110780215559463

theorem tailTrace_6475013 : CollatzResearch.WordTrace tailWord_6475013 prefixEnd_6475013 3324793913110780215559463 := by
  unfold tailWord_6475013
  simp only [CollatzResearch.WordTrace]
  refine ⟨236163125691141220024757693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157442083794094146683171795 236163125691141220024757693)
  ·
    refine ⟨88561172134177957509284135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236163125691141220024757693 88561172134177957509284135)
    ·
      refine ⟨132841758201266936263926203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88561172134177957509284135 132841758201266936263926203)
      ·
        refine ⟨199262637301900404395889305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132841758201266936263926203 199262637301900404395889305)
        ·
          refine ⟨149446977976425303296916979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199262637301900404395889305 149446977976425303296916979)
          ·
            refine ⟨224170466964637954945375469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149446977976425303296916979 224170466964637954945375469)
            ·
              refine ⟨84063925111739233104515801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224170466964637954945375469 84063925111739233104515801)
              ·
                refine ⟨63047943833804424828386851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84063925111739233104515801 63047943833804424828386851)
                ·
                  refine ⟨94571915750706637242580277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63047943833804424828386851 94571915750706637242580277)
                  ·
                    refine ⟨8866117101628747241491901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94571915750706637242580277 8866117101628747241491901)
                    ·
                      refine ⟨3324793913110780215559463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8866117101628747241491901 3324793913110780215559463)
                      ·
                        rfl

theorem cell23_6475013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_6475013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475013 prefixEnd_6475013 := by exact prefixLift 6475013
  have htrace : WordTrace (prefixWord ++ tailWord_6475013) baseStart_6475013 baseEnd_6475013 := by
    simpa [prefixWord, tailWord_6475013, baseEnd_6475013] using wordTrace_append hprefix tailTrace_6475013
  have hstable : (prefixWord ++ tailWord_6475013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475013).length < 2 ^ (prefixWord ++ tailWord_6475013).sum := by decide
  have hdescent : baseEnd_6475013 < baseStart_6475013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475020 : List Nat := [2, 2, 1, 2, 2, 3, 1, 5, 5]
def baseStart_6475020 : Nat := 118140960795 + 6475020 * 2 ^ 59
def prefixEnd_6475020 : Nat := 4983230072969 + 3 ^ 40 * 6475020 * 2
def baseEnd_6475020 : Nat := 369421945275040187574659

theorem tailTrace_6475020 : CollatzResearch.WordTrace tailWord_6475020 prefixEnd_6475020 369421945275040187574659 := by
  unfold tailWord_6475020
  simp only [CollatzResearch.WordTrace]
  refine ⟨118081690501057930110131257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157442254001410573480175009 118081690501057930110131257)
  ·
    refine ⟨88561267875793447582598443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118081690501057930110131257 88561267875793447582598443)
    ·
      refine ⟨132841901813690171373897665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88561267875793447582598443 132841901813690171373897665)
      ·
        refine ⟨99631426360267628530423249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132841901813690171373897665 99631426360267628530423249)
        ·
          refine ⟨74723569770200721397817437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99631426360267628530423249 74723569770200721397817437)
          ·
            refine ⟨28021338663825270524181539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74723569770200721397817437 28021338663825270524181539)
            ·
              refine ⟨42032007995737905786272309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28021338663825270524181539 42032007995737905786272309)
              ·
                refine ⟨3940500749600428667463029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42032007995737905786272309 3940500749600428667463029)
                ·
                  refine ⟨369421945275040187574659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3940500749600428667463029 369421945275040187574659)
                  ·
                    rfl

theorem cell23_6475020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_6475020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475020 prefixEnd_6475020 := by exact prefixLift 6475020
  have htrace : WordTrace (prefixWord ++ tailWord_6475020) baseStart_6475020 baseEnd_6475020 := by
    simpa [prefixWord, tailWord_6475020, baseEnd_6475020] using wordTrace_append hprefix tailTrace_6475020
  have hstable : (prefixWord ++ tailWord_6475020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475020).length < 2 ^ (prefixWord ++ tailWord_6475020).sum := by decide
  have hdescent : baseEnd_6475020 < baseStart_6475020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475037 : List Nat := [1, 4, 2, 3, 1, 1, 2, 4, 5]
def baseStart_6475037 : Nat := 118140960795 + 6475037 * 2 ^ 59
def prefixEnd_6475037 : Nat := 4983230072969 + 3 ^ 40 * 6475037 * 2
def baseEnd_6475037 : Nat := 369422915182943124628817

theorem tailTrace_6475037 : CollatzResearch.WordTrace tailWord_6475037 prefixEnd_6475037 369422915182943124628817 := by
  unfold tailWord_6475037
  simp only [CollatzResearch.WordTrace]
  refine ⟨236164001043054272123631365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157442667362036181415754243 236164001043054272123631365)
  ·
    refine ⟨44280750195572676023180881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236164001043054272123631365 44280750195572676023180881)
    ·
      refine ⟨33210562646679507017385661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44280750195572676023180881 33210562646679507017385661)
      ·
        refine ⟨12453960992504815131519623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33210562646679507017385661 12453960992504815131519623)
        ·
          refine ⟨18680941488757222697279435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12453960992504815131519623 18680941488757222697279435)
          ·
            refine ⟨28021412233135834045919153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18680941488757222697279435 28021412233135834045919153)
            ·
              refine ⟨21016059174851875534439365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28021412233135834045919153 21016059174851875534439365)
              ·
                refine ⟨3940511095284726662707381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21016059174851875534439365 3940511095284726662707381)
                ·
                  refine ⟨369422915182943124628817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3940511095284726662707381 369422915182943124628817)
                  ·
                    rfl

theorem cell23_6475037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_6475037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475037 prefixEnd_6475037 := by exact prefixLift 6475037
  have htrace : WordTrace (prefixWord ++ tailWord_6475037) baseStart_6475037 baseEnd_6475037 := by
    simpa [prefixWord, tailWord_6475037, baseEnd_6475037] using wordTrace_append hprefix tailTrace_6475037
  have hstable : (prefixWord ++ tailWord_6475037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475037).length < 2 ^ (prefixWord ++ tailWord_6475037).sum := by decide
  have hdescent : baseEnd_6475037 < baseStart_6475037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475050 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_6475050 : Nat := 118140960795 + 6475050 * 2 ^ 59
def prefixEnd_6475050 : Nat := 4983230072969 + 3 ^ 40 * 6475050 * 2
def baseEnd_6475050 : Nat := 1108270970631665523598931

theorem tailTrace_6475050 : CollatzResearch.WordTrace tailWord_6475050 prefixEnd_6475050 1108270970631665523598931 := by
  unfold tailWord_6475050
  simp only [CollatzResearch.WordTrace]
  refine ⟨59041118798001793835963651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157442983461338116895903069 59041118798001793835963651)
  ·
    refine ⟨88561678197002690753945477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59041118798001793835963651 88561678197002690753945477)
    ·
      refine ⟨16605314661938004516364777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88561678197002690753945477 16605314661938004516364777)
      ·
        refine ⟨12453985996453503387273583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16605314661938004516364777 12453985996453503387273583)
        ·
          refine ⟨18680978994680255080910375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12453985996453503387273583 18680978994680255080910375)
          ·
            refine ⟨28021468492020382621365563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18680978994680255080910375 28021468492020382621365563)
            ·
              refine ⟨42032202738030573932048345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28021468492020382621365563 42032202738030573932048345)
              ·
                refine ⟨31524152053522930449036259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42032202738030573932048345 31524152053522930449036259)
                ·
                  refine ⟨47286228080284395673554389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31524152053522930449036259 47286228080284395673554389)
                  ·
                    refine ⟨1108270970631665523598931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47286228080284395673554389 1108270970631665523598931)
                    ·
                      rfl

theorem cell23_6475050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_6475050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475050 prefixEnd_6475050 := by exact prefixLift 6475050
  have htrace : WordTrace (prefixWord ++ tailWord_6475050) baseStart_6475050 baseEnd_6475050 := by
    simpa [prefixWord, tailWord_6475050, baseEnd_6475050] using wordTrace_append hprefix tailTrace_6475050
  have hstable : (prefixWord ++ tailWord_6475050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475050).length < 2 ^ (prefixWord ++ tailWord_6475050).sum := by decide
  have hdescent : baseEnd_6475050 < baseStart_6475050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475070 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_6475070 : Nat := 118140960795 + 6475070 * 2 ^ 59
def prefixEnd_6475070 : Nat := 4983230072969 + 3 ^ 40 * 6475070 * 2
def baseEnd_6475070 : Nat := 3324823181508086492546701

theorem tailTrace_6475070 : CollatzResearch.WordTrace tailWord_6475070 prefixEnd_6475070 3324823181508086492546701 := by
  unfold tailWord_6475070
  simp only [CollatzResearch.WordTrace]
  refine ⟨29520650581491839844947833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157443469767956479173055109 29520650581491839844947833)
  ·
    refine ⟨22140487936118879883710875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29520650581491839844947833 22140487936118879883710875)
    ·
      refine ⟨33210731904178319825566313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22140487936118879883710875 33210731904178319825566313)
      ·
        refine ⟨24908048928133739869174735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33210731904178319825566313 24908048928133739869174735)
        ·
          refine ⟨37362073392200609803762103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24908048928133739869174735 37362073392200609803762103)
          ·
            refine ⟨56043110088300914705643155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37362073392200609803762103 56043110088300914705643155)
            ·
              refine ⟨84064665132451372058464733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56043110088300914705643155 84064665132451372058464733)
              ·
                refine ⟨31524249424669264521924275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84064665132451372058464733 31524249424669264521924275)
                ·
                  refine ⟨47286374137003896782886413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31524249424669264521924275 47286374137003896782886413)
                  ·
                    refine ⟨17732390301376461293582405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47286374137003896782886413 17732390301376461293582405)
                    ·
                      refine ⟨3324823181508086492546701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17732390301376461293582405 3324823181508086492546701)
                      ·
                        rfl

theorem cell23_6475070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_6475070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475070 prefixEnd_6475070 := by exact prefixLift 6475070
  have htrace : WordTrace (prefixWord ++ tailWord_6475070) baseStart_6475070 baseEnd_6475070 := by
    simpa [prefixWord, tailWord_6475070, baseEnd_6475070] using wordTrace_append hprefix tailTrace_6475070
  have hstable : (prefixWord ++ tailWord_6475070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475070).length < 2 ^ (prefixWord ++ tailWord_6475070).sum := by decide
  have hdescent : baseEnd_6475070 < baseStart_6475070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475097 : List Nat := [1, 2, 1, 2, 2, 2, 2, 6, 1, 4]
def baseStart_6475097 : Nat := 118140960795 + 6475097 * 2 ^ 59
def prefixEnd_6475097 : Nat := 4983230072969 + 3 ^ 40 * 6475097 * 2
def baseEnd_6475097 : Nat := 1108279015161919295636359

theorem tailTrace_6475097 : CollatzResearch.WordTrace tailWord_6475097 prefixEnd_6475097 1108279015161919295636359 := by
  unfold tailWord_6475097
  simp only [CollatzResearch.WordTrace]
  refine ⟨236166189422836902370815545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157444126281891268247210363 236166189422836902370815545)
  ·
    refine ⟨177124642067127676778111659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236166189422836902370815545 177124642067127676778111659)
    ·
      refine ⟨265686963100691515167167489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177124642067127676778111659 265686963100691515167167489)
      ·
        refine ⟨199265222325518636375375617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265686963100691515167167489 199265222325518636375375617)
        ·
          refine ⟨149448916744138977281531713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199265222325518636375375617 149448916744138977281531713)
          ·
            refine ⟨112086687558104232961148785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149448916744138977281531713 112086687558104232961148785)
            ·
              refine ⟨84065015668578174720861589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112086687558104232961148785 84065015668578174720861589)
              ·
                refine ⟨3940547609464601940040387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84065015668578174720861589 3940547609464601940040387)
                ·
                  refine ⟨5910821414196902910060581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940547609464601940040387 5910821414196902910060581)
                  ·
                    refine ⟨1108279015161919295636359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5910821414196902910060581 1108279015161919295636359)
                    ·
                      rfl

theorem cell23_6475097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 1, 4].length) (baseStart_6475097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475097 prefixEnd_6475097 := by exact prefixLift 6475097
  have htrace : WordTrace (prefixWord ++ tailWord_6475097) baseStart_6475097 baseEnd_6475097 := by
    simpa [prefixWord, tailWord_6475097, baseEnd_6475097] using wordTrace_append hprefix tailTrace_6475097
  have hstable : (prefixWord ++ tailWord_6475097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475097).length < 2 ^ (prefixWord ++ tailWord_6475097).sum := by decide
  have hdescent : baseEnd_6475097 < baseStart_6475097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475147 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 2, 3, 2]
def baseStart_6475147 : Nat := 118140960795 + 6475147 * 2 ^ 59
def prefixEnd_6475147 : Nat := 4983230072969 + 3 ^ 40 * 6475147 * 2
def baseEnd_6475147 : Nat := 3324862719518482691283847

theorem tailTrace_6475147 : CollatzResearch.WordTrace tailWord_6475147 prefixEnd_6475147 3324862719518482691283847 := by
  unfold tailWord_6475147
  simp only [CollatzResearch.WordTrace]
  refine ⟨236168013072655760910135695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157445342048437173940090463 236168013072655760910135695)
  ·
    refine ⟨354252019608983641365203543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236168013072655760910135695 354252019608983641365203543)
    ·
      refine ⟨531378029413475462047805315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354252019608983641365203543 531378029413475462047805315)
      ·
        refine ⟨797067044120213193071707973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531378029413475462047805315 797067044120213193071707973)
        ·
          refine ⟨149450070772539973700945245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 797067044120213193071707973 149450070772539973700945245)
          ·
            refine ⟨56043776539702490137854467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149450070772539973700945245 56043776539702490137854467)
            ·
              refine ⟨84065664809553735206781701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56043776539702490137854467 84065664809553735206781701)
              ·
                refine ⟨15762312151791325351271569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84065664809553735206781701 15762312151791325351271569)
                ·
                  refine ⟨11821734113843494013453677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15762312151791325351271569 11821734113843494013453677)
                  ·
                    refine ⟨4433150292691310255045129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11821734113843494013453677 4433150292691310255045129)
                    ·
                      refine ⟨3324862719518482691283847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433150292691310255045129 3324862719518482691283847)
                      ·
                        rfl

theorem cell23_6475147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 3, 2].length) (baseStart_6475147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475147 prefixEnd_6475147 := by exact prefixLift 6475147
  have htrace : WordTrace (prefixWord ++ tailWord_6475147) baseStart_6475147 baseEnd_6475147 := by
    simpa [prefixWord, tailWord_6475147, baseEnd_6475147] using wordTrace_append hprefix tailTrace_6475147
  have hstable : (prefixWord ++ tailWord_6475147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475147).length < 2 ^ (prefixWord ++ tailWord_6475147).sum := by decide
  have hdescent : baseEnd_6475147 < baseStart_6475147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475163 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 5]
def baseStart_6475163 : Nat := 118140960795 + 6475163 * 2 ^ 59
def prefixEnd_6475163 : Nat := 4983230072969 + 3 ^ 40 * 6475163 * 2
def baseEnd_6475163 : Nat := 3324870935208954628683773

theorem tailTrace_6475163 : CollatzResearch.WordTrace tailWord_6475163 prefixEnd_6475163 3324870935208954628683773 := by
  unfold tailWord_6475163
  simp only [CollatzResearch.WordTrace]
  refine ⟨236168596640597795642718143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157445731093731863761812095 236168596640597795642718143)
  ·
    refine ⟨354252894960896693464077215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236168596640597795642718143 354252894960896693464077215)
    ·
      refine ⟨531379342441345040196115823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354252894960896693464077215 531379342441345040196115823)
      ·
        refine ⟨797069013662017560294173735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531379342441345040196115823 797069013662017560294173735)
        ·
          refine ⟨1195603520493026340441260603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797069013662017560294173735 1195603520493026340441260603)
          ·
            refine ⟨1793405280739539510661890905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195603520493026340441260603 1793405280739539510661890905)
            ·
              refine ⟨1345053960554654632996418179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793405280739539510661890905 1345053960554654632996418179)
              ·
                refine ⟨2017580940831981949494627269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345053960554654632996418179 2017580940831981949494627269)
                ·
                  refine ⟨378296426405996615530242613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017580940831981949494627269 378296426405996615530242613)
                  ·
                    refine ⟨35465289975562182705960245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 378296426405996615530242613 35465289975562182705960245)
                    ·
                      refine ⟨3324870935208954628683773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35465289975562182705960245 3324870935208954628683773)
                      ·
                        rfl

theorem cell23_6475163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_6475163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475163 prefixEnd_6475163 := by exact prefixLift 6475163
  have htrace : WordTrace (prefixWord ++ tailWord_6475163) baseStart_6475163 baseEnd_6475163 := by
    simpa [prefixWord, tailWord_6475163, baseEnd_6475163] using wordTrace_append hprefix tailTrace_6475163
  have hstable : (prefixWord ++ tailWord_6475163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475163).length < 2 ^ (prefixWord ++ tailWord_6475163).sum := by decide
  have hdescent : baseEnd_6475163 < baseStart_6475163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475181 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6475181 : Nat := 118140960795 + 6475181 * 2 ^ 59
def prefixEnd_6475181 : Nat := 4983230072969 + 3 ^ 40 * 6475181 * 2
def baseEnd_6475181 : Nat := 3324880177860735558258691

theorem tailTrace_6475181 : CollatzResearch.WordTrace tailWord_6475181 prefixEnd_6475181 3324880177860735558258691 := by
  unfold tailWord_6475181
  simp only [CollatzResearch.WordTrace]
  refine ⟨236169253154532584716873397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157446168769688389811248931 236169253154532584716873397)
  ·
    refine ⟨22140867483237429817206881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236169253154532584716873397 22140867483237429817206881)
    ·
      refine ⟨16605650612428072362905161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22140867483237429817206881 16605650612428072362905161)
      ·
        refine ⟨12454237959321054272178871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16605650612428072362905161 12454237959321054272178871)
        ·
          refine ⟨18681356938981581408268307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12454237959321054272178871 18681356938981581408268307)
          ·
            refine ⟨28022035408472372112402461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18681356938981581408268307 28022035408472372112402461)
            ·
              refine ⟨10508263278177139542150923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28022035408472372112402461 10508263278177139542150923)
              ·
                refine ⟨15762394917265709313226385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10508263278177139542150923 15762394917265709313226385)
                ·
                  refine ⟨11821796187949281984919789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15762394917265709313226385 11821796187949281984919789)
                  ·
                    refine ⟨4433173570480980744344921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11821796187949281984919789 4433173570480980744344921)
                    ·
                      refine ⟨3324880177860735558258691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433173570480980744344921 3324880177860735558258691)
                      ·
                        rfl

theorem cell23_6475181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6475181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475181 prefixEnd_6475181 := by exact prefixLift 6475181
  have htrace : WordTrace (prefixWord ++ tailWord_6475181) baseStart_6475181 baseEnd_6475181 := by
    simpa [prefixWord, tailWord_6475181, baseEnd_6475181] using wordTrace_append hprefix tailTrace_6475181
  have hstable : (prefixWord ++ tailWord_6475181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475181).length < 2 ^ (prefixWord ++ tailWord_6475181).sum := by decide
  have hdescent : baseEnd_6475181 < baseStart_6475181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475183 : List Nat := [1, 1, 2, 1, 2, 2, 1, 13]
def baseStart_6475183 : Nat := 118140960795 + 6475183 * 2 ^ 59
def prefixEnd_6475183 : Nat := 4983230072969 + 3 ^ 40 * 6475183 * 2
def baseEnd_6475183 : Nat := 123143748326742390756803

theorem tailTrace_6475183 : CollatzResearch.WordTrace tailWord_6475183 prefixEnd_6475183 123143748326742390756803 := by
  unfold tailWord_6475183
  simp only [CollatzResearch.WordTrace]
  refine ⟨236169326100525339058446203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157446217400350226038964135 236169326100525339058446203)
  ·
    refine ⟨354253989150788008587669305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236169326100525339058446203 354253989150788008587669305)
    ·
      refine ⟨265690491863091006440751979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354253989150788008587669305 265690491863091006440751979)
      ·
        refine ⟨398535737794636509661127969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265690491863091006440751979 398535737794636509661127969)
        ·
          refine ⟨298901803345977382245845977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398535737794636509661127969 298901803345977382245845977)
          ·
            refine ⟨224176352509483036684384483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298901803345977382245845977 224176352509483036684384483)
            ·
              refine ⟨336264528764224555026576725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224176352509483036684384483 336264528764224555026576725)
              ·
                refine ⟨123143748326742390756803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 336264528764224555026576725 123143748326742390756803)
                ·
                  rfl

theorem cell23_6475183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 13].length) (baseStart_6475183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475183 prefixEnd_6475183 := by exact prefixLift 6475183
  have htrace : WordTrace (prefixWord ++ tailWord_6475183) baseStart_6475183 baseEnd_6475183 := by
    simpa [prefixWord, tailWord_6475183, baseEnd_6475183] using wordTrace_append hprefix tailTrace_6475183
  have hstable : (prefixWord ++ tailWord_6475183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475183).length < 2 ^ (prefixWord ++ tailWord_6475183).sum := by decide
  have hdescent : baseEnd_6475183 < baseStart_6475183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475204 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_6475204 : Nat := 118140960795 + 6475204 * 2 ^ 59
def prefixEnd_6475204 : Nat := 4983230072969 + 3 ^ 40 * 6475204 * 2
def baseEnd_6475204 : Nat := 1108297329305262989423695

theorem tailTrace_6475204 : CollatzResearch.WordTrace tailWord_6475204 prefixEnd_6475204 1108297329305262989423695 := by
  unfold tailWord_6475204
  simp only [CollatzResearch.WordTrace]
  refine ⟨118085046016724629822480333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157446728022299506429973777 118085046016724629822480333)
  ·
    refine ⟨44281892256271736183430125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118085046016724629822480333 44281892256271736183430125)
    ·
      refine ⟨16605709596101901068786297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44281892256271736183430125 16605709596101901068786297)
      ·
        refine ⟨12454282197076425801589723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16605709596101901068786297 12454282197076425801589723)
        ·
          refine ⟨18681423295614638702384585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12454282197076425801589723 18681423295614638702384585)
          ·
            refine ⟨14011067471710979026788439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18681423295614638702384585 14011067471710979026788439)
            ·
              refine ⟨21016601207566468540182659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14011067471710979026788439 21016601207566468540182659)
              ·
                refine ⟨31524901811349702810273989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21016601207566468540182659 31524901811349702810273989)
                ·
                  refine ⟨5910919089628069276926373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31524901811349702810273989 5910919089628069276926373)
                  ·
                    refine ⟨1108297329305262989423695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5910919089628069276926373 1108297329305262989423695)
                    ·
                      rfl

theorem cell23_6475204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_6475204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475204 prefixEnd_6475204 := by exact prefixLift 6475204
  have htrace : WordTrace (prefixWord ++ tailWord_6475204) baseStart_6475204 baseEnd_6475204 := by
    simpa [prefixWord, tailWord_6475204, baseEnd_6475204] using wordTrace_append hprefix tailTrace_6475204
  have hstable : (prefixWord ++ tailWord_6475204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475204).length < 2 ^ (prefixWord ++ tailWord_6475204).sum := by decide
  have hdescent : baseEnd_6475204 < baseStart_6475204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475211 : List Nat := [1, 1, 1, 1, 3, 3, 4, 4, 1, 2, 2]
def baseStart_6475211 : Nat := 118140960795 + 6475211 * 2 ^ 59
def prefixEnd_6475211 : Nat := 4983230072969 + 3 ^ 40 * 6475211 * 2
def baseEnd_6475211 : Nat := 3324895582280370440883553

theorem tailTrace_6475211 : CollatzResearch.WordTrace tailWord_6475211 prefixEnd_6475211 3324895582280370440883553 := by
  unfold tailWord_6475211
  simp only [CollatzResearch.WordTrace]
  refine ⟨236170347344423899840465487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157446898229615933226976991 236170347344423899840465487)
  ·
    refine ⟨354255521016635849760698231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236170347344423899840465487 354255521016635849760698231)
    ·
      refine ⟨531383281524953774641047347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354255521016635849760698231 531383281524953774641047347)
      ·
        refine ⟨797074922287430661961571021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531383281524953774641047347 797074922287430661961571021)
        ·
          refine ⟨298903095857786498235589133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 797074922287430661961571021 298903095857786498235589133)
          ·
            refine ⟨112088660946669936838345925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298903095857786498235589133 112088660946669936838345925)
            ·
              refine ⟨21016623927500613157189861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112088660946669936838345925 21016623927500613157189861)
              ·
                refine ⟨3940616986406364966973099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21016623927500613157189861 3940616986406364966973099)
                ·
                  refine ⟨5910925479609547450459649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940616986406364966973099 5910925479609547450459649)
                  ·
                    refine ⟨4433194109707160587844737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5910925479609547450459649 4433194109707160587844737)
                    ·
                      refine ⟨3324895582280370440883553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433194109707160587844737 3324895582280370440883553)
                      ·
                        rfl

theorem cell23_6475211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 2, 2].length) (baseStart_6475211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475211 prefixEnd_6475211 := by exact prefixLift 6475211
  have htrace : WordTrace (prefixWord ++ tailWord_6475211) baseStart_6475211 baseEnd_6475211 := by
    simpa [prefixWord, tailWord_6475211, baseEnd_6475211] using wordTrace_append hprefix tailTrace_6475211
  have hstable : (prefixWord ++ tailWord_6475211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475211).length < 2 ^ (prefixWord ++ tailWord_6475211).sum := by decide
  have hdescent : baseEnd_6475211 < baseStart_6475211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475240 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6475240 : Nat := 118140960795 + 6475240 * 2 ^ 59
def prefixEnd_6475240 : Nat := 4983230072969 + 3 ^ 40 * 6475240 * 2
def baseEnd_6475240 : Nat := 3324910473219350827420919

theorem tailTrace_6475240 : CollatzResearch.WordTrace tailWord_6475240 prefixEnd_6475240 3324910473219350827420919 := by
  unfold tailWord_6475240
  simp only [CollatzResearch.WordTrace]
  refine ⟨118085702530659418896635587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157447603374212558528847449 118085702530659418896635587)
  ·
    refine ⟨177128553795989128344953381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118085702530659418896635587 177128553795989128344953381)
    ·
      refine ⟨33211603836747961564678759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177128553795989128344953381 33211603836747961564678759)
      ·
        refine ⟨49817405755121942347018139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33211603836747961564678759 49817405755121942347018139)
        ·
          refine ⟨74726108632682913520527209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49817405755121942347018139 74726108632682913520527209)
          ·
            refine ⟨56044581474512185140395407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74726108632682913520527209 56044581474512185140395407)
            ·
              refine ⟨84066872211768277710593111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56044581474512185140395407 84066872211768277710593111)
              ·
                refine ⟨126100308317652416565889667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84066872211768277710593111 126100308317652416565889667)
                ·
                  refine ⟨189150462476478624848834501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126100308317652416565889667 189150462476478624848834501)
                  ·
                    refine ⟨35465711714339742159156469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189150462476478624848834501 35465711714339742159156469)
                    ·
                      refine ⟨3324910473219350827420919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35465711714339742159156469 3324910473219350827420919)
                      ·
                        rfl

theorem cell23_6475240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6475240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475240 prefixEnd_6475240 := by exact prefixLift 6475240
  have htrace : WordTrace (prefixWord ++ tailWord_6475240) baseStart_6475240 baseEnd_6475240 := by
    simpa [prefixWord, tailWord_6475240, baseEnd_6475240] using wordTrace_append hprefix tailTrace_6475240
  have hstable : (prefixWord ++ tailWord_6475240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475240).length < 2 ^ (prefixWord ++ tailWord_6475240).sum := by decide
  have hdescent : baseEnd_6475240 < baseStart_6475240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475260 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_6475260 : Nat := 118140960795 + 6475260 * 2 ^ 59
def prefixEnd_6475260 : Nat := 4983230072969 + 3 ^ 40 * 6475260 * 2
def baseEnd_6475260 : Nat := 1108306914277480249723609

theorem tailTrace_6475260 : CollatzResearch.WordTrace tailWord_6475260 prefixEnd_6475260 1108306914277480249723609 := by
  unfold tailWord_6475260
  simp only [CollatzResearch.WordTrace]
  refine ⟨118086067260623190604499617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157448089680830920805999489 118086067260623190604499617)
  ·
    refine ⟨88564550445467392953374713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118086067260623190604499617 88564550445467392953374713)
    ·
      refine ⟨66423412834100544715031035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88564550445467392953374713 66423412834100544715031035)
      ·
        refine ⟨99635119251150817072546553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66423412834100544715031035 99635119251150817072546553)
        ·
          refine ⟨74726339438363112804409915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99635119251150817072546553 74726339438363112804409915)
          ·
            refine ⟨112089509157544669206614873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74726339438363112804409915 112089509157544669206614873)
            ·
              refine ⟨84067131868158501904961155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112089509157544669206614873 84067131868158501904961155)
              ·
                refine ⟨126100697802237752857441733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84067131868158501904961155 126100697802237752857441733)
                ·
                  refine ⟨23643880837919578660770325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126100697802237752857441733 23643880837919578660770325)
                  ·
                    refine ⟨1108306914277480249723609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23643880837919578660770325 1108306914277480249723609)
                    ·
                      rfl

theorem cell23_6475260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_6475260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475260 prefixEnd_6475260 := by exact prefixLift 6475260
  have htrace : WordTrace (prefixWord ++ tailWord_6475260) baseStart_6475260 baseEnd_6475260 := by
    simpa [prefixWord, tailWord_6475260, baseEnd_6475260] using wordTrace_append hprefix tailTrace_6475260
  have hstable : (prefixWord ++ tailWord_6475260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475260).length < 2 ^ (prefixWord ++ tailWord_6475260).sum := by decide
  have hdescent : baseEnd_6475260 < baseStart_6475260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475262 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6475262 : Nat := 118140960795 + 6475262 * 2 ^ 59
def prefixEnd_6475262 : Nat := 4983230072969 + 3 ^ 40 * 6475262 * 2
def baseEnd_6475262 : Nat := 3324921769793749741345819

theorem tailTrace_6475262 : CollatzResearch.WordTrace tailWord_6475262 prefixEnd_6475262 3324921769793749741345819 := by
  unfold tailWord_6475262
  simp only [CollatzResearch.WordTrace]
  refine ⟨29521525933404891943821505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157448138311492757033714693 29521525933404891943821505)
  ·
    refine ⟨22141144450053668957866129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29521525933404891943821505 22141144450053668957866129)
    ·
      refine ⟨16605858337540251718399597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22141144450053668957866129 16605858337540251718399597)
      ·
        refine ⟨6227196876577594394399849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16605858337540251718399597 6227196876577594394399849)
        ·
          refine ⟨4670397657433195795799887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6227196876577594394399849 4670397657433195795799887)
          ·
            refine ⟨7005596486149793693699831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670397657433195795799887 7005596486149793693699831)
            ·
              refine ⟨10508394729224690540549747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005596486149793693699831 10508394729224690540549747)
              ·
                refine ⟨15762592093837035810824621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10508394729224690540549747 15762592093837035810824621)
                ·
                  refine ⟨5910972035188888429059233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15762592093837035810824621 5910972035188888429059233)
                  ·
                    refine ⟨4433229026391666321794425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5910972035188888429059233 4433229026391666321794425)
                    ·
                      refine ⟨3324921769793749741345819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433229026391666321794425 3324921769793749741345819)
                      ·
                        rfl

theorem cell23_6475262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6475262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475262 prefixEnd_6475262 := by exact prefixLift 6475262
  have htrace : WordTrace (prefixWord ++ tailWord_6475262) baseStart_6475262 baseEnd_6475262 := by
    simpa [prefixWord, tailWord_6475262, baseEnd_6475262] using wordTrace_append hprefix tailTrace_6475262
  have hstable : (prefixWord ++ tailWord_6475262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475262).length < 2 ^ (prefixWord ++ tailWord_6475262).sum := by decide
  have hdescent : baseEnd_6475262 < baseStart_6475262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475267 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 5, 4, 2]
def baseStart_6475267 : Nat := 118140960795 + 6475267 * 2 ^ 59
def prefixEnd_6475267 : Nat := 4983230072969 + 3 ^ 40 * 6475267 * 2
def baseEnd_6475267 : Nat := 3324924337197022221783295

theorem tailTrace_6475267 : CollatzResearch.WordTrace tailWord_6475267 prefixEnd_6475267 3324924337197022221783295 := by
  unfold tailWord_6475267
  simp only [CollatzResearch.WordTrace]
  refine ⟨236172389832221021404504055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157448259888147347603002703 236172389832221021404504055)
  ·
    refine ⟨354258584748331532106756083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236172389832221021404504055 354258584748331532106756083)
    ·
      refine ⟨531387877122497298160134125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354258584748331532106756083 531387877122497298160134125)
      ·
        refine ⟨199270453920936486810050297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531387877122497298160134125 199270453920936486810050297)
        ·
          refine ⟨149452840440702365107537723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199270453920936486810050297 149452840440702365107537723)
          ·
            refine ⟨224179260661053547661306585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149452840440702365107537723 224179260661053547661306585)
            ·
              refine ⟨168134445495790160745979939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224179260661053547661306585 168134445495790160745979939)
              ·
                refine ⟨252201668243685241118969909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168134445495790160745979939 252201668243685241118969909)
                ·
                  refine ⟨23643906397845491354903429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252201668243685241118969909 23643906397845491354903429)
                  ·
                    refine ⟨4433232449596029629044393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23643906397845491354903429 4433232449596029629044393)
                    ·
                      refine ⟨3324924337197022221783295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433232449596029629044393 3324924337197022221783295)
                      ·
                        rfl

theorem cell23_6475267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_6475267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475267 prefixEnd_6475267 := by exact prefixLift 6475267
  have htrace : WordTrace (prefixWord ++ tailWord_6475267) baseStart_6475267 baseEnd_6475267 := by
    simpa [prefixWord, tailWord_6475267, baseEnd_6475267] using wordTrace_append hprefix tailTrace_6475267
  have hstable : (prefixWord ++ tailWord_6475267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475267).length < 2 ^ (prefixWord ++ tailWord_6475267).sum := by decide
  have hdescent : baseEnd_6475267 < baseStart_6475267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475288 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 1, 3, 2]
def baseStart_6475288 : Nat := 118140960795 + 6475288 * 2 ^ 59
def prefixEnd_6475288 : Nat := 4983230072969 + 3 ^ 40 * 6475288 * 2
def baseEnd_6475288 : Nat := 3324935120290766639620699

theorem tailTrace_6475288 : CollatzResearch.WordTrace tailWord_6475288 prefixEnd_6475288 3324935120290766639620699 := by
  unfold tailWord_6475288
  simp only [CollatzResearch.WordTrace]
  refine ⟨118086577882572470995509259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157448770510096627994012345 118086577882572470995509259)
  ·
    refine ⟨177129866823858706493263889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118086577882572470995509259 177129866823858706493263889)
    ·
      refine ⟨132847400117894029869947917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177129866823858706493263889 132847400117894029869947917)
      ·
        refine ⟨49817775044210261201230469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132847400117894029869947917 49817775044210261201230469)
        ·
          refine ⟨9340832820789423975230713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49817775044210261201230469 9340832820789423975230713)
          ·
            refine ⟨7005624615592067981423035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9340832820789423975230713 7005624615592067981423035)
            ·
              refine ⟨10508436923388101972134553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005624615592067981423035 10508436923388101972134553)
              ·
                refine ⟨7881327692541076479100915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10508436923388101972134553 7881327692541076479100915)
                ·
                  refine ⟨11821991538811614718651373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881327692541076479100915 11821991538811614718651373)
                  ·
                    refine ⟨4433246827054355519494265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11821991538811614718651373 4433246827054355519494265)
                    ·
                      refine ⟨3324935120290766639620699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433246827054355519494265 3324935120290766639620699)
                      ·
                        rfl

theorem cell23_6475288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_6475288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475288 prefixEnd_6475288 := by exact prefixLift 6475288
  have htrace : WordTrace (prefixWord ++ tailWord_6475288) baseStart_6475288 baseEnd_6475288 := by
    simpa [prefixWord, tailWord_6475288, baseEnd_6475288] using wordTrace_append hprefix tailTrace_6475288
  have hstable : (prefixWord ++ tailWord_6475288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475288).length < 2 ^ (prefixWord ++ tailWord_6475288).sum := by decide
  have hdescent : baseEnd_6475288 < baseStart_6475288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475290 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 9]
def baseStart_6475290 : Nat := 118140960795 + 6475290 * 2 ^ 59
def prefixEnd_6475290 : Nat := 4983230072969 + 3 ^ 40 * 6475290 * 2
def baseEnd_6475290 : Nat := 369437349694675070199521

theorem tailTrace_6475290 : CollatzResearch.WordTrace tailWord_6475290 prefixEnd_6475290 369437349694675070199521 := by
  unfold tailWord_6475290
  simp only [CollatzResearch.WordTrace]
  refine ⟨59043307177784424083147831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157448819140758464221727549 59043307177784424083147831)
  ·
    refine ⟨88564960766676636124721747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59043307177784424083147831 88564960766676636124721747)
    ·
      refine ⟨132847441150014954187082621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88564960766676636124721747 132847441150014954187082621)
      ·
        refine ⟨49817790431255607820155983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132847441150014954187082621 49817790431255607820155983)
        ·
          refine ⟨74726685646883411730233975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49817790431255607820155983 74726685646883411730233975)
          ·
            refine ⟨112090028470325117595350963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74726685646883411730233975 112090028470325117595350963)
            ·
              refine ⟨168135042705487676393026445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112090028470325117595350963 168135042705487676393026445)
              ·
                refine ⟨63050641014557878647384917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168135042705487676393026445 63050641014557878647384917)
                ·
                  refine ⟨369437349694675070199521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63050641014557878647384917 369437349694675070199521)
                  ·
                    rfl

theorem cell23_6475290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_6475290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475290 prefixEnd_6475290 := by exact prefixLift 6475290
  have htrace : WordTrace (prefixWord ++ tailWord_6475290) baseStart_6475290 baseEnd_6475290 := by
    simpa [prefixWord, tailWord_6475290, baseEnd_6475290] using wordTrace_append hprefix tailTrace_6475290
  have hstable : (prefixWord ++ tailWord_6475290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475290).length < 2 ^ (prefixWord ++ tailWord_6475290).sum := by decide
  have hdescent : baseEnd_6475290 < baseStart_6475290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475464 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_6475464 : Nat := 118140960795 + 6475464 * 2 ^ 59
def prefixEnd_6475464 : Nat := 4983230072969 + 3 ^ 40 * 6475464 * 2
def baseEnd_6475464 : Nat := 3325025492885957951019889

theorem tailTrace_6475464 : CollatzResearch.WordTrace tailWord_6475464 prefixEnd_6475464 3325025492885957951019889 := by
  unfold tailWord_6475464
  simp only [CollatzResearch.WordTrace]
  refine ⟨118089787506253662024712723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157453050008338216032950297 118089787506253662024712723)
  ·
    refine ⟨177134681259380493037069085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118089787506253662024712723 177134681259380493037069085)
    ·
      refine ⟨66425505472267684888900907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177134681259380493037069085 66425505472267684888900907)
      ·
        refine ⟨99638258208401527333351361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66425505472267684888900907 99638258208401527333351361)
        ·
          refine ⟨74728693656301145500013521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99638258208401527333351361 74728693656301145500013521)
          ·
            refine ⟨56046520242225859125010141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74728693656301145500013521 56046520242225859125010141)
            ·
              refine ⟨21017445090834697171878803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56046520242225859125010141 21017445090834697171878803)
              ·
                refine ⟨31526167636252045757818205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21017445090834697171878803 31526167636252045757818205)
                ·
                  refine ⟨11822312863594517159181827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31526167636252045757818205 11822312863594517159181827)
                  ·
                    refine ⟨17733469295391775738772741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11822312863594517159181827 17733469295391775738772741)
                    ·
                      refine ⟨3325025492885957951019889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17733469295391775738772741 3325025492885957951019889)
                      ·
                        rfl

theorem cell23_6475464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_6475464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475464 prefixEnd_6475464 := by exact prefixLift 6475464
  have htrace : WordTrace (prefixWord ++ tailWord_6475464) baseStart_6475464 baseEnd_6475464 := by
    simpa [prefixWord, tailWord_6475464, baseEnd_6475464] using wordTrace_append hprefix tailTrace_6475464
  have hstable : (prefixWord ++ tailWord_6475464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475464).length < 2 ^ (prefixWord ++ tailWord_6475464).sum := by decide
  have hdescent : baseEnd_6475464 < baseStart_6475464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475467 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 5]
def baseStart_6475467 : Nat := 118140960795 + 6475467 * 2 ^ 59
def prefixEnd_6475467 : Nat := 4983230072969 + 3 ^ 40 * 6475467 * 2
def baseEnd_6475467 : Nat := 3325027033327921439282375

theorem tailTrace_6475467 : CollatzResearch.WordTrace tailWord_6475467 prefixEnd_6475467 3325027033327921439282375 := by
  unfold tailWord_6475467
  simp only [CollatzResearch.WordTrace]
  refine ⟨236179684431496455561784655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157453122954330970374523103 236179684431496455561784655)
  ·
    refine ⟨354269526647244683342676983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236179684431496455561784655 354269526647244683342676983)
    ·
      refine ⟨531404289970867025014015475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354269526647244683342676983 531404289970867025014015475)
      ·
        refine ⟨797106434956300537521023213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531404289970867025014015475 797106434956300537521023213)
        ·
          refine ⟨298914913108612701570383705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 797106434956300537521023213 298914913108612701570383705)
          ·
            refine ⟨224186184831459526177787779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298914913108612701570383705 224186184831459526177787779)
            ·
              refine ⟨336279277247189289266681669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224186184831459526177787779 336279277247189289266681669)
              ·
                refine ⟨63052364483847991737502813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336279277247189289266681669 63052364483847991737502813)
                ·
                  refine ⟨23644636681442996901563555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63052364483847991737502813 23644636681442996901563555)
                  ·
                    refine ⟨35466955022164495352345333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23644636681442996901563555 35466955022164495352345333)
                    ·
                      refine ⟨3325027033327921439282375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35466955022164495352345333 3325027033327921439282375)
                      ·
                        rfl

theorem cell23_6475467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_6475467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475467 prefixEnd_6475467 := by exact prefixLift 6475467
  have htrace : WordTrace (prefixWord ++ tailWord_6475467) baseStart_6475467 baseEnd_6475467 := by
    simpa [prefixWord, tailWord_6475467, baseEnd_6475467] using wordTrace_append hprefix tailTrace_6475467
  have hstable : (prefixWord ++ tailWord_6475467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475467).length < 2 ^ (prefixWord ++ tailWord_6475467).sum := by decide
  have hdescent : baseEnd_6475467 < baseStart_6475467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475474 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_6475474 : Nat := 118140960795 + 6475474 * 2 ^ 59
def prefixEnd_6475474 : Nat := 4983230072969 + 3 ^ 40 * 6475474 * 2
def baseEnd_6475474 : Nat := 1108343542564167637298281

theorem tailTrace_6475474 : CollatzResearch.WordTrace tailWord_6475474 prefixEnd_6475474 1108343542564167637298281 := by
  unfold tailWord_6475474
  simp only [CollatzResearch.WordTrace]
  refine ⟨59044984935617773939322369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157453293161647397171526317 59044984935617773939322369)
  ·
    refine ⟨44283738701713330454491777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59044984935617773939322369 44283738701713330454491777)
    ·
      refine ⟨33212804026284997840868833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44283738701713330454491777 33212804026284997840868833)
      ·
        refine ⟨24909603019713748380651625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33212804026284997840868833 24909603019713748380651625)
        ·
          refine ⟨18682202264785311285488719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24909603019713748380651625 18682202264785311285488719)
          ·
            refine ⟨28023303397177966928233079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18682202264785311285488719 28023303397177966928233079)
            ·
              refine ⟨42034955095766950392349619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28023303397177966928233079 42034955095766950392349619)
              ·
                refine ⟨63052432643650425588524429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42034955095766950392349619 63052432643650425588524429)
                ·
                  refine ⟨23644662241368909595696661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63052432643650425588524429 23644662241368909595696661)
                  ·
                    refine ⟨1108343542564167637298281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23644662241368909595696661 1108343542564167637298281)
                    ·
                      rfl

theorem cell23_6475474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_6475474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475474 prefixEnd_6475474 := by exact prefixLift 6475474
  have htrace : WordTrace (prefixWord ++ tailWord_6475474) baseStart_6475474 baseEnd_6475474 := by
    simpa [prefixWord, tailWord_6475474, baseEnd_6475474] using wordTrace_append hprefix tailTrace_6475474
  have hstable : (prefixWord ++ tailWord_6475474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475474).length < 2 ^ (prefixWord ++ tailWord_6475474).sum := by decide
  have hdescent : baseEnd_6475474 < baseStart_6475474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475501 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_6475501 : Nat := 118140960795 + 6475501 * 2 ^ 59
def prefixEnd_6475501 : Nat := 4983230072969 + 3 ^ 40 * 6475501 * 2
def baseEnd_6475501 : Nat := 3325044491670174306257219

theorem tailTrace_6475501 : CollatzResearch.WordTrace tailWord_6475501 prefixEnd_6475501 3325044491670174306257219 := by
  unfold tailWord_6475501
  simp only [CollatzResearch.WordTrace]
  refine ⟨236180924513373279368522357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157453949675582186245681571 236180924513373279368522357)
  ·
    refine ⟨22141961673128744940798971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236180924513373279368522357 22141961673128744940798971)
    ·
      refine ⟨33212942509693117411198457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22141961673128744940798971 33212942509693117411198457)
      ·
        refine ⟨24909706882269838058398843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33212942509693117411198457 24909706882269838058398843)
        ·
          refine ⟨37364560323404757087598265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24909706882269838058398843 37364560323404757087598265)
          ·
            refine ⟨28023420242553567815698699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37364560323404757087598265 28023420242553567815698699)
            ·
              refine ⟨42035130363830351723548049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28023420242553567815698699 42035130363830351723548049)
              ·
                refine ⟨31526347772872763792661037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42035130363830351723548049 31526347772872763792661037)
                ·
                  refine ⟨11822380414827286422247889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31526347772872763792661037 11822380414827286422247889)
                  ·
                    refine ⟨8866785311120464816685917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11822380414827286422247889 8866785311120464816685917)
                    ·
                      refine ⟨3325044491670174306257219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8866785311120464816685917 3325044491670174306257219)
                      ·
                        rfl

theorem cell23_6475501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_6475501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475501 prefixEnd_6475501 := by exact prefixLift 6475501
  have htrace : WordTrace (prefixWord ++ tailWord_6475501) baseStart_6475501 baseEnd_6475501 := by
    simpa [prefixWord, tailWord_6475501, baseEnd_6475501] using wordTrace_append hprefix tailTrace_6475501
  have hstable : (prefixWord ++ tailWord_6475501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475501).length < 2 ^ (prefixWord ++ tailWord_6475501).sum := by decide
  have hdescent : baseEnd_6475501 < baseStart_6475501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475507 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 6]
def baseStart_6475507 : Nat := 118140960795 + 6475507 * 2 ^ 59
def prefixEnd_6475507 : Nat := 4983230072969 + 3 ^ 40 * 6475507 * 2
def baseEnd_6475507 : Nat := 3325047572554101282782191

theorem tailTrace_6475507 : CollatzResearch.WordTrace tailWord_6475507 prefixEnd_6475507 3325047572554101282782191 := by
  unfold tailWord_6475507
  simp only [CollatzResearch.WordTrace]
  refine ⟨236181143351351542393240775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157454095567567694928827183 236181143351351542393240775)
  ·
    refine ⟨354271715027027313589861163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236181143351351542393240775 354271715027027313589861163)
    ·
      refine ⟨531407572540540970384791745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354271715027027313589861163 531407572540540970384791745)
      ·
        refine ⟨398555679405405727788593809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531407572540540970384791745 398555679405405727788593809)
        ·
          refine ⟨298916759554054295841445357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398555679405405727788593809 298916759554054295841445357)
          ·
            refine ⟨112093784832770360940542009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298916759554054295841445357 112093784832770360940542009)
            ·
              refine ⟨84070338624577770705406507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112093784832770360940542009 84070338624577770705406507)
              ·
                refine ⟨126105507936866656058109761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84070338624577770705406507 126105507936866656058109761)
                ·
                  refine ⟨94579130952649992043582321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126105507936866656058109761 94579130952649992043582321)
                  ·
                    refine ⟨70934348214487494032686741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94579130952649992043582321 70934348214487494032686741)
                    ·
                      refine ⟨3325047572554101282782191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70934348214487494032686741 3325047572554101282782191)
                      ·
                        rfl

theorem cell23_6475507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_6475507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475507 prefixEnd_6475507 := by exact prefixLift 6475507
  have htrace : WordTrace (prefixWord ++ tailWord_6475507) baseStart_6475507 baseEnd_6475507 := by
    simpa [prefixWord, tailWord_6475507, baseEnd_6475507] using wordTrace_append hprefix tailTrace_6475507
  have hstable : (prefixWord ++ tailWord_6475507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475507).length < 2 ^ (prefixWord ++ tailWord_6475507).sum := by decide
  have hdescent : baseEnd_6475507 < baseStart_6475507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475508 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6475508 : Nat := 118140960795 + 6475508 * 2 ^ 59
def prefixEnd_6475508 : Nat := 4983230072969 + 3 ^ 40 * 6475508 * 2
def baseEnd_6475508 : Nat := 1108349362011585259623229

theorem tailTrace_6475508 : CollatzResearch.WordTrace tailWord_6475508 prefixEnd_6475508 1108349362011585259623229 := by
  unfold tailWord_6475508
  simp only [CollatzResearch.WordTrace]
  refine ⟨118090589912173959782013589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157454119882898613042684785 118090589912173959782013589)
  ·
    refine ⟨5535496402133154364781887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118090589912173959782013589 5535496402133154364781887)
    ·
      refine ⟨8303244603199731547172831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5535496402133154364781887 8303244603199731547172831)
      ·
        refine ⟨12454866904799597320759247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303244603199731547172831 12454866904799597320759247)
        ·
          refine ⟨18682300357199395981138871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12454866904799597320759247 18682300357199395981138871)
          ·
            refine ⟨28023450535799093971708307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18682300357199395981138871 28023450535799093971708307)
            ·
              refine ⟨42035175803698640957562461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28023450535799093971708307 42035175803698640957562461)
              ·
                refine ⟨15763190926386990359085923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42035175803698640957562461 15763190926386990359085923)
                ·
                  refine ⟨23644786389580485538628885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15763190926386990359085923 23644786389580485538628885)
                  ·
                    refine ⟨1108349362011585259623229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23644786389580485538628885 1108349362011585259623229)
                    ·
                      rfl

theorem cell23_6475508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6475508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475508 prefixEnd_6475508 := by exact prefixLift 6475508
  have htrace : WordTrace (prefixWord ++ tailWord_6475508) baseStart_6475508 baseEnd_6475508 := by
    simpa [prefixWord, tailWord_6475508, baseEnd_6475508] using wordTrace_append hprefix tailTrace_6475508
  have hstable : (prefixWord ++ tailWord_6475508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475508).length < 2 ^ (prefixWord ++ tailWord_6475508).sum := by decide
  have hdescent : baseEnd_6475508 < baseStart_6475508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475547 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 3, 8]
def baseStart_6475547 : Nat := 118140960795 + 6475547 * 2 ^ 59
def prefixEnd_6475547 : Nat := 4983230072969 + 3 ^ 40 * 6475547 * 2
def baseEnd_6475547 : Nat := 1108356037260093708760669

theorem tailTrace_6475547 : CollatzResearch.WordTrace tailWord_6475547 prefixEnd_6475547 1108356037260093708760669 := by
  unfold tailWord_6475547
  simp only [CollatzResearch.WordTrace]
  refine ⟨236182602271206629224696895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157455068180804419483131263 236182602271206629224696895)
  ·
    refine ⟨354273903406809943837045343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236182602271206629224696895 354273903406809943837045343)
    ·
      refine ⟨531410855110214915755568015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354273903406809943837045343 531410855110214915755568015)
      ·
        refine ⟨797116282665322373633352023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531410855110214915755568015 797116282665322373633352023)
        ·
          refine ⟨1195674423997983560450028035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797116282665322373633352023 1195674423997983560450028035)
          ·
            refine ⟨1793511635996975340675042053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195674423997983560450028035 1793511635996975340675042053)
            ·
              refine ⟨336283431749432876376570385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1793511635996975340675042053 336283431749432876376570385)
              ·
                refine ⟨252212573812074657282427789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336283431749432876376570385 252212573812074657282427789)
                ·
                  refine ⟨94579715179527996480910421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252212573812074657282427789 94579715179527996480910421)
                  ·
                    refine ⟨1108356037260093708760669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94579715179527996480910421 1108356037260093708760669)
                    ·
                      rfl

theorem cell23_6475547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 8].length) (baseStart_6475547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475547 prefixEnd_6475547 := by exact prefixLift 6475547
  have htrace : WordTrace (prefixWord ++ tailWord_6475547) baseStart_6475547 baseEnd_6475547 := by
    simpa [prefixWord, tailWord_6475547, baseEnd_6475547] using wordTrace_append hprefix tailTrace_6475547
  have hstable : (prefixWord ++ tailWord_6475547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475547).length < 2 ^ (prefixWord ++ tailWord_6475547).sum := by decide
  have hdescent : baseEnd_6475547 < baseStart_6475547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475564 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_6475564 : Nat := 118140960795 + 6475564 * 2 ^ 59
def prefixEnd_6475564 : Nat := 4983230072969 + 3 ^ 40 * 6475564 * 2
def baseEnd_6475564 : Nat := 1108358946983802519923143

theorem tailTrace_6475564 : CollatzResearch.WordTrace tailWord_6475564 prefixEnd_6475564 1108358946983802519923143 := by
  unfold tailWord_6475564
  simp only [CollatzResearch.WordTrace]
  refine ⟨118091611156072520564032873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157455481541430027418710497 118091611156072520564032873)
  ·
    refine ⟨88568708367054390423024655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118091611156072520564032873 88568708367054390423024655)
    ·
      refine ⟨132853062550581585634536983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88568708367054390423024655 132853062550581585634536983)
      ·
        refine ⟨199279593825872378451805475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132853062550581585634536983 199279593825872378451805475)
        ·
          refine ⟨298919390738808567677708213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199279593825872378451805475 298919390738808567677708213)
          ·
            refine ⟨28023692881763303219785145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298919390738808567677708213 28023692881763303219785145)
            ·
              refine ⟨21017769661322477414838859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28023692881763303219785145 21017769661322477414838859)
              ·
                refine ⟨31526654491983716122258289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21017769661322477414838859 31526654491983716122258289)
                ·
                  refine ⟨23644990868987787091693717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31526654491983716122258289 23644990868987787091693717)
                  ·
                    refine ⟨1108358946983802519923143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23644990868987787091693717 1108358946983802519923143)
                    ·
                      rfl

theorem cell23_6475564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_6475564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475564 prefixEnd_6475564 := by exact prefixLift 6475564
  have htrace : WordTrace (prefixWord ++ tailWord_6475564) baseStart_6475564 baseEnd_6475564 := by
    simpa [prefixWord, tailWord_6475564, baseEnd_6475564] using wordTrace_append hprefix tailTrace_6475564
  have hstable : (prefixWord ++ tailWord_6475564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475564).length < 2 ^ (prefixWord ++ tailWord_6475564).sum := by decide
  have hdescent : baseEnd_6475564 < baseStart_6475564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475634 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6475634 : Nat := 118140960795 + 6475634 * 2 ^ 59
def prefixEnd_6475634 : Nat := 4983230072969 + 3 ^ 40 * 6475634 * 2
def baseEnd_6475634 : Nat := 3325112784597222285894107

theorem tailTrace_6475634 : CollatzResearch.WordTrace tailWord_6475634 prefixEnd_6475634 3325112784597222285894107 := by
  unfold tailWord_6475634
  simp only [CollatzResearch.WordTrace]
  refine ⟨59046443855472860770778489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157457183614594295388742637 59046443855472860770778489)
  ·
    refine ⟨44284832891604645578083867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59046443855472860770778489 44284832891604645578083867)
    ·
      refine ⟨66427249337406968367125801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44284832891604645578083867 66427249337406968367125801)
      ·
        refine ⟨49820437003055226275344351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66427249337406968367125801 49820437003055226275344351)
        ·
          refine ⟨74730655504582839413016527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49820437003055226275344351 74730655504582839413016527)
          ·
            refine ⟨112095983256874259119524791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74730655504582839413016527 112095983256874259119524791)
            ·
              refine ⟨168143974885311388679287187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112095983256874259119524791 168143974885311388679287187)
              ·
                refine ⟨252215962327967083018930781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168143974885311388679287187 252215962327967083018930781)
                ·
                  refine ⟨94580985872987656132099043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252215962327967083018930781 94580985872987656132099043)
                  ·
                    refine ⟨141871478809481484198148565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94580985872987656132099043 141871478809481484198148565)
                    ·
                      refine ⟨3325112784597222285894107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141871478809481484198148565 3325112784597222285894107)
                      ·
                        rfl

theorem cell23_6475634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6475634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475634 prefixEnd_6475634 := by exact prefixLift 6475634
  have htrace : WordTrace (prefixWord ++ tailWord_6475634) baseStart_6475634 baseEnd_6475634 := by
    simpa [prefixWord, tailWord_6475634, baseEnd_6475634] using wordTrace_append hprefix tailTrace_6475634
  have hstable : (prefixWord ++ tailWord_6475634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475634).length < 2 ^ (prefixWord ++ tailWord_6475634).sum := by decide
  have hdescent : baseEnd_6475634 < baseStart_6475634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475641 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 2, 5]
def baseStart_6475641 : Nat := 118140960795 + 6475641 * 2 ^ 59
def prefixEnd_6475641 : Nat := 4983230072969 + 3 ^ 40 * 6475641 * 2
def baseEnd_6475641 : Nat := 1108372126320601252835525

theorem tailTrace_6475641 : CollatzResearch.WordTrace tailWord_6475641 prefixEnd_6475641 1108372126320601252835525 := by
  unfold tailWord_6475641
  simp only [CollatzResearch.WordTrace]
  refine ⟨236186030732866083278618777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157457353821910722185745851 236186030732866083278618777)
  ·
    refine ⟨177139523049649562458964083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236186030732866083278618777 177139523049649562458964083)
    ·
      refine ⟨265709284574474343688446125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177139523049649562458964083 265709284574474343688446125)
      ·
        refine ⟨99640981715427878883167297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265709284574474343688446125 99640981715427878883167297)
        ·
          refine ⟨74730736286570909162375473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99640981715427878883167297 74730736286570909162375473)
          ·
            refine ⟨56048052214928181871781605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74730736286570909162375473 56048052214928181871781605)
            ·
              refine ⟨10509009790299034100959051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56048052214928181871781605 10509009790299034100959051)
              ·
                refine ⟨15763514685448551151438577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10509009790299034100959051 15763514685448551151438577)
                ·
                  refine ⟨11822636014086413363578933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15763514685448551151438577 11822636014086413363578933)
                  ·
                    refine ⟨1108372126320601252835525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11822636014086413363578933 1108372126320601252835525)
                    ·
                      rfl

theorem cell23_6475641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_6475641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475641 prefixEnd_6475641 := by exact prefixLift 6475641
  have htrace : WordTrace (prefixWord ++ tailWord_6475641) baseStart_6475641 baseEnd_6475641 := by
    simpa [prefixWord, tailWord_6475641, baseEnd_6475641] using wordTrace_append hprefix tailTrace_6475641
  have hstable : (prefixWord ++ tailWord_6475641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475641).length < 2 ^ (prefixWord ++ tailWord_6475641).sum := by decide
  have hdescent : baseEnd_6475641 < baseStart_6475641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475705 : List Nat := [1, 2, 1, 4, 2, 1, 4, 3, 1, 4]
def baseStart_6475705 : Nat := 118140960795 + 6475705 * 2 ^ 59
def prefixEnd_6475705 : Nat := 4983230072969 + 3 ^ 40 * 6475705 * 2
def baseEnd_6475705 : Nat := 1108383080574563836035427

theorem tailTrace_6475705 : CollatzResearch.WordTrace tailWord_6475705 prefixEnd_6475705 1108383080574563836035427 := by
  unfold tailWord_6475705
  simp only [CollatzResearch.WordTrace]
  refine ⟨236188365004634222208948569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157458910003089481472632379 236188365004634222208948569)
  ·
    refine ⟨177141273753475666656711427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236188365004634222208948569 177141273753475666656711427)
    ·
      refine ⟨265711910630213499985067141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177141273753475666656711427 265711910630213499985067141)
      ·
        refine ⟨49820983243165031247200089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265711910630213499985067141 49820983243165031247200089)
        ·
          refine ⟨37365737432373773435400067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49820983243165031247200089 37365737432373773435400067)
          ·
            refine ⟨56048606148560660153100101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37365737432373773435400067 56048606148560660153100101)
            ·
              refine ⟨10509113652855123778706269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56048606148560660153100101 10509113652855123778706269)
              ·
                refine ⟨3940917619820671417014851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10509113652855123778706269 3940917619820671417014851)
                ·
                  refine ⟨5911376429731007125522277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940917619820671417014851 5911376429731007125522277)
                  ·
                    refine ⟨1108383080574563836035427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5911376429731007125522277 1108383080574563836035427)
                    ·
                      rfl

theorem cell23_6475705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 4].length) (baseStart_6475705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475705 prefixEnd_6475705 := by exact prefixLift 6475705
  have htrace : WordTrace (prefixWord ++ tailWord_6475705) baseStart_6475705 baseEnd_6475705 := by
    simpa [prefixWord, tailWord_6475705, baseEnd_6475705] using wordTrace_append hprefix tailTrace_6475705
  have hstable : (prefixWord ++ tailWord_6475705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475705).length < 2 ^ (prefixWord ++ tailWord_6475705).sum := by decide
  have hdescent : baseEnd_6475705 < baseStart_6475705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475728 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 3, 1, 3]
def baseStart_6475728 : Nat := 118140960795 + 6475728 * 2 ^ 59
def prefixEnd_6475728 : Nat := 4983230072969 + 3 ^ 40 * 6475728 * 2
def baseEnd_6475728 : Nat := 3325161051778744918118675

theorem tailTrace_6475728 : CollatzResearch.WordTrace tailWord_6475728 prefixEnd_6475728 3325161051778744918118675 := by
  unfold tailWord_6475728
  simp only [CollatzResearch.WordTrace]
  refine ⟨118094601941775448568517919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157459469255700598091357225 118094601941775448568517919)
  ·
    refine ⟨177141902912663172852776879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118094601941775448568517919 177141902912663172852776879)
    ·
      refine ⟨265712854368994759279165319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177141902912663172852776879 265712854368994759279165319)
      ·
        refine ⟨398569281553492138918747979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265712854368994759279165319 398569281553492138918747979)
        ·
          refine ⟨597853922330238208378121969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398569281553492138918747979 597853922330238208378121969)
          ·
            refine ⟨448390441747678656283591477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597853922330238208378121969 448390441747678656283591477)
            ·
              refine ⟨42036603913844874026586701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 448390441747678656283591477 42036603913844874026586701)
              ·
                refine ⟨15763726467691827759970013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42036603913844874026586701 15763726467691827759970013)
                ·
                  refine ⟨5911397425384435409988755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15763726467691827759970013 5911397425384435409988755)
                  ·
                    refine ⟨8867096138076653114983133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5911397425384435409988755 8867096138076653114983133)
                    ·
                      refine ⟨3325161051778744918118675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867096138076653114983133 3325161051778744918118675)
                      ·
                        rfl

theorem cell23_6475728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 1, 3].length) (baseStart_6475728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475728 prefixEnd_6475728 := by exact prefixLift 6475728
  have htrace : WordTrace (prefixWord ++ tailWord_6475728) baseStart_6475728 baseEnd_6475728 := by
    simpa [prefixWord, tailWord_6475728, baseEnd_6475728] using wordTrace_append hprefix tailTrace_6475728
  have hstable : (prefixWord ++ tailWord_6475728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475728).length < 2 ^ (prefixWord ++ tailWord_6475728).sum := by decide
  have hdescent : baseEnd_6475728 < baseStart_6475728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475748 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_6475748 : Nat := 118140960795 + 6475748 * 2 ^ 59
def prefixEnd_6475748 : Nat := 4983230072969 + 3 ^ 40 * 6475748 * 2
def baseEnd_6475748 : Nat := 1108390440463944946622861

theorem tailTrace_6475748 : CollatzResearch.WordTrace tailWord_6475748 prefixEnd_6475748 1108390440463944946622861 := by
  unfold tailWord_6475748
  simp only [CollatzResearch.WordTrace]
  refine ⟨118094966671739220276381949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157459955562318960368509265 118094966671739220276381949)
  ·
    refine ⟨44285612501902207603643231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118094966671739220276381949 44285612501902207603643231)
    ·
      refine ⟨66428418752853311405464847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44285612501902207603643231 66428418752853311405464847)
      ·
        refine ⟨99642628129279967108197271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66428418752853311405464847 99642628129279967108197271)
        ·
          refine ⟨149463942193919950662295907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99642628129279967108197271 149463942193919950662295907)
          ·
            refine ⟨224195913290879925993443861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149463942193919950662295907 224195913290879925993443861)
            ·
              refine ⟨10509183435509996530942681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224195913290879925993443861 10509183435509996530942681)
              ·
                refine ⟨7881887576632497398207011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10509183435509996530942681 7881887576632497398207011)
                ·
                  refine ⟨11822831364948746097310517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881887576632497398207011 11822831364948746097310517)
                  ·
                    refine ⟨1108390440463944946622861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11822831364948746097310517 1108390440463944946622861)
                    ·
                      rfl

theorem cell23_6475748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_6475748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475748 prefixEnd_6475748 := by exact prefixLift 6475748
  have htrace : WordTrace (prefixWord ++ tailWord_6475748) baseStart_6475748 baseEnd_6475748 := by
    simpa [prefixWord, tailWord_6475748, baseEnd_6475748] using wordTrace_append hprefix tailTrace_6475748
  have hstable : (prefixWord ++ tailWord_6475748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475748).length < 2 ^ (prefixWord ++ tailWord_6475748).sum := by decide
  have hdescent : baseEnd_6475748 < baseStart_6475748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475768 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_6475768 : Nat := 118140960795 + 6475768 * 2 ^ 59
def prefixEnd_6475768 : Nat := 4983230072969 + 3 ^ 40 * 6475768 * 2
def baseEnd_6475768 : Nat := 3325181591004924761618491

theorem tailTrace_6475768 : CollatzResearch.WordTrace tailWord_6475768 prefixEnd_6475768 3325181591004924761618491 := by
  unfold tailWord_6475768
  simp only [CollatzResearch.WordTrace]
  refine ⟨118095331401702991984245979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157460441868937322645661305 118095331401702991984245979)
  ·
    refine ⟨177142997102554487976368969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118095331401702991984245979 177142997102554487976368969)
    ·
      refine ⟨132857247826915865982276727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177142997102554487976368969 132857247826915865982276727)
      ·
        refine ⟨199285871740373798973415091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132857247826915865982276727 199285871740373798973415091)
        ·
          refine ⟨298928807610560698460122637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199285871740373798973415091 298928807610560698460122637)
          ·
            refine ⟨112098302853960261922545989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298928807610560698460122637 112098302853960261922545989)
            ·
              refine ⟨21018431785117549110477373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112098302853960261922545989 21018431785117549110477373)
              ·
                refine ⟨7881911919419080916429015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21018431785117549110477373 7881911919419080916429015)
                ·
                  refine ⟨11822867879128621374643523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881911919419080916429015 11822867879128621374643523)
                  ·
                    refine ⟨17734301818692932061965285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11822867879128621374643523 17734301818692932061965285)
                    ·
                      refine ⟨3325181591004924761618491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17734301818692932061965285 3325181591004924761618491)
                      ·
                        rfl

theorem cell23_6475768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_6475768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475768 prefixEnd_6475768 := by exact prefixLift 6475768
  have htrace : WordTrace (prefixWord ++ tailWord_6475768) baseStart_6475768 baseEnd_6475768 := by
    simpa [prefixWord, tailWord_6475768, baseEnd_6475768] using wordTrace_append hprefix tailTrace_6475768
  have hstable : (prefixWord ++ tailWord_6475768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475768).length < 2 ^ (prefixWord ++ tailWord_6475768).sum := by decide
  have hdescent : baseEnd_6475768 < baseStart_6475768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475771 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 5]
def baseStart_6475771 : Nat := 118140960795 + 6475771 * 2 ^ 59
def prefixEnd_6475771 : Nat := 4983230072969 + 3 ^ 40 * 6475771 * 2
def baseEnd_6475771 : Nat := 3325183131446888249880977

theorem tailTrace_6475771 : CollatzResearch.WordTrace tailWord_6475771 prefixEnd_6475771 3325183131446888249880977 := by
  unfold tailWord_6475771
  simp only [CollatzResearch.WordTrace]
  refine ⟨236190772222395115480851167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157460514814930076987234111 236190772222395115480851167)
  ·
    refine ⟨354286158333592673221276751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236190772222395115480851167 354286158333592673221276751)
    ·
      refine ⟨531429237500389009831915127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354286158333592673221276751 531429237500389009831915127)
      ·
        refine ⟨797143856250583514747872691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531429237500389009831915127 797143856250583514747872691)
        ·
          refine ⟨1195715784375875272121809037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797143856250583514747872691 1195715784375875272121809037)
          ·
            refine ⟨448393419140953227045678389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1195715784375875272121809037 448393419140953227045678389)
            ·
              refine ⟨42036883044464365035532349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 448393419140953227045678389 42036883044464365035532349)
              ·
                refine ⟨15763831141674136888324631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42036883044464365035532349 15763831141674136888324631)
                ·
                  refine ⟨23645746712511205332486947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15763831141674136888324631 23645746712511205332486947)
                  ·
                    refine ⟨35468620068766807998730421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23645746712511205332486947 35468620068766807998730421)
                    ·
                      refine ⟨3325183131446888249880977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35468620068766807998730421 3325183131446888249880977)
                      ·
                        rfl

theorem cell23_6475771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 5].length) (baseStart_6475771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475771 prefixEnd_6475771 := by exact prefixLift 6475771
  have htrace : WordTrace (prefixWord ++ tailWord_6475771) baseStart_6475771 baseEnd_6475771 := by
    simpa [prefixWord, tailWord_6475771, baseEnd_6475771] using wordTrace_append hprefix tailTrace_6475771
  have hstable : (prefixWord ++ tailWord_6475771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475771).length < 2 ^ (prefixWord ++ tailWord_6475771).sum := by decide
  have hdescent : baseEnd_6475771 < baseStart_6475771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475781 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_6475781 : Nat := 118140960795 + 6475781 * 2 ^ 59
def prefixEnd_6475781 : Nat := 4983230072969 + 3 ^ 40 * 6475781 * 2
def baseEnd_6475781 : Nat := 3325188266253433210755931

theorem tailTrace_6475781 : CollatzResearch.WordTrace tailWord_6475781 prefixEnd_6475781 3325188266253433210755931 := by
  unfold tailWord_6475781
  simp only [CollatzResearch.WordTrace]
  refine ⟨236191136952358887188715197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157460757968239258125810131 236191136952358887188715197)
  ·
    refine ⟨88571676357134582695768199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236191136952358887188715197 88571676357134582695768199)
    ·
      refine ⟨132857514535701874043652299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88571676357134582695768199 132857514535701874043652299)
      ·
        refine ⟨199286271803552811065478449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132857514535701874043652299 199286271803552811065478449)
        ·
          refine ⟨149464703852664608299108837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199286271803552811065478449 149464703852664608299108837)
          ·
            refine ⟨28024631972374614056082907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149464703852664608299108837 28024631972374614056082907)
            ·
              refine ⟨42036947958561921084124361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28024631972374614056082907 42036947958561921084124361)
              ·
                refine ⟨31527710968921440813093271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42036947958561921084124361 31527710968921440813093271)
                ·
                  refine ⟨47291566453382161219639907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31527710968921440813093271 47291566453382161219639907)
                  ·
                    refine ⟨70937349680073241829459861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47291566453382161219639907 70937349680073241829459861)
                    ·
                      refine ⟨3325188266253433210755931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70937349680073241829459861 3325188266253433210755931)
                      ·
                        rfl

theorem cell23_6475781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_6475781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475781 prefixEnd_6475781 := by exact prefixLift 6475781
  have htrace : WordTrace (prefixWord ++ tailWord_6475781) baseStart_6475781 baseEnd_6475781 := by
    simpa [prefixWord, tailWord_6475781, baseEnd_6475781] using wordTrace_append hprefix tailTrace_6475781
  have hstable : (prefixWord ++ tailWord_6475781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475781).length < 2 ^ (prefixWord ++ tailWord_6475781).sum := by decide
  have hdescent : baseEnd_6475781 < baseStart_6475781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475788 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_6475788 : Nat := 118140960795 + 6475788 * 2 ^ 59
def prefixEnd_6475788 : Nat := 4983230072969 + 3 ^ 40 * 6475788 * 2
def baseEnd_6475788 : Nat := 3325191860618014683368399

theorem tailTrace_6475788 : CollatzResearch.WordTrace tailWord_6475788 prefixEnd_6475788 3325191860618014683368399 := by
  unfold tailWord_6475788
  simp only [CollatzResearch.WordTrace]
  refine ⟨118095696131666763692110009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157460928175555684922813345 118095696131666763692110009)
  ·
    refine ⟨88571772098750072769082507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118095696131666763692110009 88571772098750072769082507)
    ·
      refine ⟨132857658148125109153623761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88571772098750072769082507 132857658148125109153623761)
      ·
        refine ⟨99643243611093831865217821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132857658148125109153623761 99643243611093831865217821)
        ·
          refine ⟨37366216354160186949456683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99643243611093831865217821 37366216354160186949456683)
          ·
            refine ⟨56049324531240280424185025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37366216354160186949456683 56049324531240280424185025)
            ·
              refine ⟨42036993398430210318138769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56049324531240280424185025 42036993398430210318138769)
              ·
                refine ⟨31527745048822657738604077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42036993398430210318138769 31527745048822657738604077)
                ·
                  refine ⟨11822904393308496651976529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31527745048822657738604077 11822904393308496651976529)
                  ·
                    refine ⟨8867178294981372488982397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11822904393308496651976529 8867178294981372488982397)
                    ·
                      refine ⟨3325191860618014683368399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867178294981372488982397 3325191860618014683368399)
                      ·
                        rfl

theorem cell23_6475788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_6475788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475788 prefixEnd_6475788 := by exact prefixLift 6475788
  have htrace : WordTrace (prefixWord ++ tailWord_6475788) baseStart_6475788 baseEnd_6475788 := by
    simpa [prefixWord, tailWord_6475788, baseEnd_6475788] using wordTrace_append hprefix tailTrace_6475788
  have hstable : (prefixWord ++ tailWord_6475788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475788).length < 2 ^ (prefixWord ++ tailWord_6475788).sum := by decide
  have hdescent : baseEnd_6475788 < baseStart_6475788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475795 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 2, 4]
def baseStart_6475795 : Nat := 118140960795 + 6475795 * 2 ^ 59
def prefixEnd_6475795 : Nat := 4983230072969 + 3 ^ 40 * 6475795 * 2
def baseEnd_6475795 : Nat := 1108398484994198718660289

theorem tailTrace_6475795 : CollatzResearch.WordTrace tailWord_6475795 prefixEnd_6475795 1108398484994198718660289 := by
  unfold tailWord_6475795
  simp only [CollatzResearch.WordTrace]
  refine ⟨236191647574308167579724839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157461098382872111719816559 236191647574308167579724839)
  ·
    refine ⟨354287471361462251369587259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236191647574308167579724839 354287471361462251369587259)
    ·
      refine ⟨531431207042193377054380889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354287471361462251369587259 531431207042193377054380889)
      ·
        refine ⟨398573405281645032790785667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531431207042193377054380889 398573405281645032790785667)
        ·
          refine ⟨597860107922467549186178501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398573405281645032790785667 597860107922467549186178501)
          ·
            refine ⟨112098770235462665472408469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 597860107922467549186178501 112098770235462665472408469)
            ·
              refine ⟨5254629854787312444019147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112098770235462665472408469 5254629854787312444019147)
              ·
                refine ⟨7881944782180968666028721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254629854787312444019147 7881944782180968666028721)
                ·
                  refine ⟨5911458586635726499521541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7881944782180968666028721 5911458586635726499521541)
                  ·
                    refine ⟨1108398484994198718660289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5911458586635726499521541 1108398484994198718660289)
                    ·
                      rfl

theorem cell23_6475795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 4].length) (baseStart_6475795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475795 prefixEnd_6475795 := by exact prefixLift 6475795
  have htrace : WordTrace (prefixWord ++ tailWord_6475795) baseStart_6475795 baseEnd_6475795 := by
    simpa [prefixWord, tailWord_6475795, baseEnd_6475795] using wordTrace_append hprefix tailTrace_6475795
  have hstable : (prefixWord ++ tailWord_6475795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475795).length < 2 ^ (prefixWord ++ tailWord_6475795).sum := by decide
  have hdescent : baseEnd_6475795 < baseStart_6475795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475805 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_6475805 : Nat := 118140960795 + 6475805 * 2 ^ 59
def prefixEnd_6475805 : Nat := 4983230072969 + 3 ^ 40 * 6475805 * 2
def baseEnd_6475805 : Nat := 3325200589789141116855821

theorem tailTrace_6475805 : CollatzResearch.WordTrace tailWord_6475805 prefixEnd_6475805 3325200589789141116855821 := by
  unfold tailWord_6475805
  simp only [CollatzResearch.WordTrace]
  refine ⟨236192012304271939287588869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157461341536181292858392579 236192012304271939287588869)
  ·
    refine ⟨44286002307050988616422913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236192012304271939287588869 44286002307050988616422913)
    ·
      refine ⟨33214501730288241462317185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44286002307050988616422913 33214501730288241462317185)
      ·
        refine ⟨24910876297716181096737889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33214501730288241462317185 24910876297716181096737889)
        ·
          refine ⟨18683157223287135822553417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24910876297716181096737889 18683157223287135822553417)
          ·
            refine ⟨14012367917465351866915063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18683157223287135822553417 14012367917465351866915063)
            ·
              refine ⟨21018551876198027800372595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14012367917465351866915063 21018551876198027800372595)
              ·
                refine ⟨31527827814297041700558893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21018551876198027800372595 31527827814297041700558893)
                ·
                  refine ⟨11822935430361390637709585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31527827814297041700558893 11822935430361390637709585)
                  ·
                    refine ⟨8867201572771042978282189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11822935430361390637709585 8867201572771042978282189)
                    ·
                      refine ⟨3325200589789141116855821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867201572771042978282189 3325200589789141116855821)
                      ·
                        rfl

theorem cell23_6475805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_6475805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475805 prefixEnd_6475805 := by exact prefixLift 6475805
  have htrace : WordTrace (prefixWord ++ tailWord_6475805) baseStart_6475805 baseEnd_6475805 := by
    simpa [prefixWord, tailWord_6475805, baseEnd_6475805] using wordTrace_append hprefix tailTrace_6475805
  have hstable : (prefixWord ++ tailWord_6475805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475805).length < 2 ^ (prefixWord ++ tailWord_6475805).sum := by decide
  have hdescent : baseEnd_6475805 < baseStart_6475805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475831 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_6475831 : Nat := 118140960795 + 6475831 * 2 ^ 59
def prefixEnd_6475831 : Nat := 4983230072969 + 3 ^ 40 * 6475831 * 2
def baseEnd_6475831 : Nat := 3325213940286158015130701

theorem tailTrace_6475831 : CollatzResearch.WordTrace tailWord_6475831 prefixEnd_6475831 3325213940286158015130701 := by
  unfold tailWord_6475831
  simp only [CollatzResearch.WordTrace]
  refine ⟨236192960602177745728035347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157461973734785163818690231 236192960602177745728035347)
  ·
    refine ⟨354289440903266618592053021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236192960602177745728035347 354289440903266618592053021)
    ·
      refine ⟨132858540338724981972019883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354289440903266618592053021 132858540338724981972019883)
      ·
        refine ⟨199287810508087472958029825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132858540338724981972019883 199287810508087472958029825)
        ·
          refine ⟨149465857881065604718522369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199287810508087472958029825 149465857881065604718522369)
          ·
            refine ⟨112099393410799203538891777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149465857881065604718522369 112099393410799203538891777)
            ·
              refine ⟨84074545058099402654168833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112099393410799203538891777 84074545058099402654168833)
              ·
                refine ⟨63055908793574551990626625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84074545058099402654168833 63055908793574551990626625)
                ·
                  refine ⟨47291931595180913992969969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63055908793574551990626625 47291931595180913992969969)
                  ·
                    refine ⟨35468948696385685494727477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47291931595180913992969969 35468948696385685494727477)
                    ·
                      refine ⟨3325213940286158015130701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35468948696385685494727477 3325213940286158015130701)
                      ·
                        rfl

theorem cell23_6475831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_6475831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475831 prefixEnd_6475831 := by exact prefixLift 6475831
  have htrace : WordTrace (prefixWord ++ tailWord_6475831) baseStart_6475831 baseEnd_6475831 := by
    simpa [prefixWord, tailWord_6475831, baseEnd_6475831] using wordTrace_append hprefix tailTrace_6475831
  have hstable : (prefixWord ++ tailWord_6475831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475831).length < 2 ^ (prefixWord ++ tailWord_6475831).sum := by decide
  have hdescent : baseEnd_6475831 < baseStart_6475831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475851 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 2, 6]
def baseStart_6475851 : Nat := 118140960795 + 6475851 * 2 ^ 59
def prefixEnd_6475851 : Nat := 4983230072969 + 3 ^ 40 * 6475851 * 2
def baseEnd_6475851 : Nat := 1108408069966415978960203

theorem tailTrace_6475851 : CollatzResearch.WordTrace tailWord_6475851 prefixEnd_6475851 1108408069966415978960203 := by
  unfold tailWord_6475851
  simp only [CollatzResearch.WordTrace]
  refine ⟨236193690062105289143763407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157462460041403526095842271 236193690062105289143763407)
  ·
    refine ⟨354290535093157933715645111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236193690062105289143763407 354290535093157933715645111)
    ·
      refine ⟨531435802639736900573467667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354290535093157933715645111 531435802639736900573467667)
      ·
        refine ⟨797153703959605350860201501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531435802639736900573467667 797153703959605350860201501)
        ·
          refine ⟨298932638984852006572575563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 797153703959605350860201501 298932638984852006572575563)
          ·
            refine ⟨448398958477278009858863345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298932638984852006572575563 448398958477278009858863345)
            ·
              refine ⟨336299218857958507394147509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448398958477278009858863345 336299218857958507394147509)
              ·
                refine ⟨31528051767933610068201329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336299218857958507394147509 31528051767933610068201329)
                ·
                  refine ⟨23646038825950207551150997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31528051767933610068201329 23646038825950207551150997)
                  ·
                    refine ⟨1108408069966415978960203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23646038825950207551150997 1108408069966415978960203)
                    ·
                      rfl

theorem cell23_6475851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 6].length) (baseStart_6475851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475851 prefixEnd_6475851 := by exact prefixLift 6475851
  have htrace : WordTrace (prefixWord ++ tailWord_6475851) baseStart_6475851 baseEnd_6475851 := by
    simpa [prefixWord, tailWord_6475851, baseEnd_6475851] using wordTrace_append hprefix tailTrace_6475851
  have hstable : (prefixWord ++ tailWord_6475851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475851).length < 2 ^ (prefixWord ++ tailWord_6475851).sum := by decide
  have hdescent : baseEnd_6475851 < baseStart_6475851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475870 : List Nat := [4, 4, 1, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_6475870 : Nat := 118140960795 + 6475870 * 2 ^ 59
def prefixEnd_6475870 : Nat := 4983230072969 + 3 ^ 40 * 6475870 * 2
def baseEnd_6475870 : Nat := 3325233966031683362543023

theorem tailTrace_6475870 : CollatzResearch.WordTrace tailWord_6475870 prefixEnd_6475870 3325233966031683362543023 := by
  unfold tailWord_6475870
  simp only [CollatzResearch.WordTrace]
  refine ⟨29524297881129556923588133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157462922032690970259136709 29524297881129556923588133)
  ·
    refine ⟨5535805852711791923172775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29524297881129556923588133 5535805852711791923172775)
    ·
      refine ⟨8303708779067687884759163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5535805852711791923172775 8303708779067687884759163)
      ·
        refine ⟨12455563168601531827138745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303708779067687884759163 12455563168601531827138745)
        ·
          refine ⟨9341672376451148870354059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12455563168601531827138745 9341672376451148870354059)
          ·
            refine ⟨14012508564676723305531089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9341672376451148870354059 14012508564676723305531089)
            ·
              refine ⟨10509381423507542479148317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14012508564676723305531089 10509381423507542479148317)
              ·
                refine ⟨3941018033815328429680619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10509381423507542479148317 3941018033815328429680619)
                ·
                  refine ⟨5911527050722992644520929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941018033815328429680619 5911527050722992644520929)
                  ·
                    refine ⟨4433645288042244483390697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5911527050722992644520929 4433645288042244483390697)
                    ·
                      refine ⟨3325233966031683362543023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433645288042244483390697 3325233966031683362543023)
                      ·
                        rfl

theorem cell23_6475870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_6475870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475870 prefixEnd_6475870 := by exact prefixLift 6475870
  have htrace : WordTrace (prefixWord ++ tailWord_6475870) baseStart_6475870 baseEnd_6475870 := by
    simpa [prefixWord, tailWord_6475870, baseEnd_6475870] using wordTrace_append hprefix tailTrace_6475870
  have hstable : (prefixWord ++ tailWord_6475870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475870).length < 2 ^ (prefixWord ++ tailWord_6475870).sum := by decide
  have hdescent : baseEnd_6475870 < baseStart_6475870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475875 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 1, 4, 2]
def baseStart_6475875 : Nat := 118140960795 + 6475875 * 2 ^ 59
def prefixEnd_6475875 : Nat := 4983230072969 + 3 ^ 40 * 6475875 * 2
def baseEnd_6475875 : Nat := 3325236533434955842980499

theorem tailTrace_6475875 : CollatzResearch.WordTrace tailWord_6475875 prefixEnd_6475875 3325236533434955842980499 := by
  unfold tailWord_6475875
  simp only [CollatzResearch.WordTrace]
  refine ⟨236194565414018341242637079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157463043609345560828424719 236194565414018341242637079)
  ·
    refine ⟨354291848121027511863955619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236194565414018341242637079 354291848121027511863955619)
    ·
      refine ⟨531437772181541267795933429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354291848121027511863955619 531437772181541267795933429)
      ·
        refine ⟨49822291142019493855868759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 531437772181541267795933429 49822291142019493855868759)
        ·
          refine ⟨74733436713029240783803139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49822291142019493855868759 74733436713029240783803139)
          ·
            refine ⟨112100155069543861175704709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74733436713029240783803139 112100155069543861175704709)
            ·
              refine ⟨21018779075539473970444633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112100155069543861175704709 21018779075539473970444633)
              ·
                refine ⟨15764084306654605477833475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21018779075539473970444633 15764084306654605477833475)
                ·
                  refine ⟨23646126459981908216750213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15764084306654605477833475 23646126459981908216750213)
                  ·
                    refine ⟨4433648711246607790640665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23646126459981908216750213 4433648711246607790640665)
                    ·
                      refine ⟨3325236533434955842980499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433648711246607790640665 3325236533434955842980499)
                      ·
                        rfl

theorem cell23_6475875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_6475875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475875 prefixEnd_6475875 := by exact prefixLift 6475875
  have htrace : WordTrace (prefixWord ++ tailWord_6475875) baseStart_6475875 baseEnd_6475875 := by
    simpa [prefixWord, tailWord_6475875, baseEnd_6475875] using wordTrace_append hprefix tailTrace_6475875
  have hstable : (prefixWord ++ tailWord_6475875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475875).length < 2 ^ (prefixWord ++ tailWord_6475875).sum := by decide
  have hdescent : baseEnd_6475875 < baseStart_6475875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475881 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 9]
def baseStart_6475881 : Nat := 118140960795 + 6475881 * 2 ^ 59
def prefixEnd_6475881 : Nat := 4983230072969 + 3 ^ 40 * 6475881 * 2
def baseEnd_6475881 : Nat := 369471068257653646611719

theorem tailTrace_6475881 : CollatzResearch.WordTrace tailWord_6475881 prefixEnd_6475881 369471068257653646611719 := by
  unfold tailWord_6475881
  simp only [CollatzResearch.WordTrace]
  refine ⟨236194784251996604267355497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157463189501331069511570331 236194784251996604267355497)
  ·
    refine ⟨177146088188997453200516623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236194784251996604267355497 177146088188997453200516623)
    ·
      refine ⟨265719132283496179800774935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177146088188997453200516623 265719132283496179800774935)
      ·
        refine ⟨398578698425244269701162403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265719132283496179800774935 398578698425244269701162403)
        ·
          refine ⟨597868047637866404551743605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398578698425244269701162403 597868047637866404551743605)
          ·
            refine ⟨56050129466049975426725963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 597868047637866404551743605 56050129466049975426725963)
            ·
              refine ⟨84075194199074963140088945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56050129466049975426725963 84075194199074963140088945)
              ·
                refine ⟨63056395649306222355066709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84075194199074963140088945 63056395649306222355066709)
                ·
                  refine ⟨369471068257653646611719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63056395649306222355066709 369471068257653646611719)
                  ·
                    rfl

theorem cell23_6475881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 9].length) (baseStart_6475881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475881 prefixEnd_6475881 := by exact prefixLift 6475881
  have htrace : WordTrace (prefixWord ++ tailWord_6475881) baseStart_6475881 baseEnd_6475881 := by
    simpa [prefixWord, tailWord_6475881, baseEnd_6475881] using wordTrace_append hprefix tailTrace_6475881
  have hstable : (prefixWord ++ tailWord_6475881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475881).length < 2 ^ (prefixWord ++ tailWord_6475881).sum := by decide
  have hdescent : baseEnd_6475881 < baseStart_6475881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475888 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_6475888 : Nat := 118140960795 + 6475888 * 2 ^ 59
def prefixEnd_6475888 : Nat := 4983230072969 + 3 ^ 40 * 6475888 * 2
def baseEnd_6475888 : Nat := 3325243208683464292117939

theorem tailTrace_6475888 : CollatzResearch.WordTrace tailWord_6475888 prefixEnd_6475888 3325243208683464292117939 := by
  unfold tailWord_6475888
  simp only [CollatzResearch.WordTrace]
  refine ⟨118097519781485622231430159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157463359708647496308573545 118097519781485622231430159)
  ·
    refine ⟨177146279672228433347145239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118097519781485622231430159 177146279672228433347145239)
    ·
      refine ⟨265719419508342650020717859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177146279672228433347145239 265719419508342650020717859)
      ·
        refine ⟨398579129262513975031076789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265719419508342650020717859 398579129262513975031076789)
        ·
          refine ⟨37366793368360685159163449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 398579129262513975031076789 37366793368360685159163449)
          ·
            refine ⟨28025095026270513869372587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37366793368360685159163449 28025095026270513869372587)
            ·
              refine ⟨42037642539405770804058881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28025095026270513869372587 42037642539405770804058881)
              ·
                refine ⟨31528231904554328103044161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42037642539405770804058881 31528231904554328103044161)
                ·
                  refine ⟨23646173928415746077283121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31528231904554328103044161 23646173928415746077283121)
                  ·
                    refine ⟨17734630446311809557962341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23646173928415746077283121 17734630446311809557962341)
                    ·
                      refine ⟨3325243208683464292117939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17734630446311809557962341 3325243208683464292117939)
                      ·
                        rfl

theorem cell23_6475888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_6475888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475888 prefixEnd_6475888 := by exact prefixLift 6475888
  have htrace : WordTrace (prefixWord ++ tailWord_6475888) baseStart_6475888 baseEnd_6475888 := by
    simpa [prefixWord, tailWord_6475888, baseEnd_6475888] using wordTrace_append hprefix tailTrace_6475888
  have hstable : (prefixWord ++ tailWord_6475888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475888).length < 2 ^ (prefixWord ++ tailWord_6475888).sum := by decide
  have hdescent : baseEnd_6475888 < baseStart_6475888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475949 : List Nat := [1, 5, 2, 1, 2, 2, 3, 2, 5]
def baseStart_6475949 : Nat := 118140960795 + 6475949 * 2 ^ 59
def prefixEnd_6475949 : Nat := 4983230072969 + 3 ^ 40 * 6475949 * 2
def baseEnd_6475949 : Nat := 369474947889265394828351

theorem tailTrace_6475949 : CollatzResearch.WordTrace tailWord_6475949 prefixEnd_6475949 369474947889265394828351 := by
  unfold tailWord_6475949
  simp only [CollatzResearch.WordTrace]
  refine ⟨236197264415750251880830901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157464842943833501253887267 236197264415750251880830901)
  ·
    refine ⟨22143493538976586113827897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236197264415750251880830901 22143493538976586113827897)
    ·
      refine ⟨16607620154232439585370923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22143493538976586113827897 16607620154232439585370923)
      ·
        refine ⟨24911430231348659378056385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16607620154232439585370923 24911430231348659378056385)
        ·
          refine ⟨18683572673511494533542289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24911430231348659378056385 18683572673511494533542289)
          ·
            refine ⟨14012679505133620900156717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18683572673511494533542289 14012679505133620900156717)
            ·
              refine ⟨5254754814425107837558769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14012679505133620900156717 5254754814425107837558769)
              ·
                refine ⟨3941066110818830878169077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5254754814425107837558769 3941066110818830878169077)
                ·
                  refine ⟨369474947889265394828351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3941066110818830878169077 369474947889265394828351)
                  ·
                    rfl

theorem cell23_6475949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_6475949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475949 prefixEnd_6475949 := by exact prefixLift 6475949
  have htrace : WordTrace (prefixWord ++ tailWord_6475949) baseStart_6475949 baseEnd_6475949 := by
    simpa [prefixWord, tailWord_6475949, baseEnd_6475949] using wordTrace_append hprefix tailTrace_6475949
  have hstable : (prefixWord ++ tailWord_6475949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475949).length < 2 ^ (prefixWord ++ tailWord_6475949).sum := by decide
  have hdescent : baseEnd_6475949 < baseStart_6475949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475965 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_6475965 : Nat := 118140960795 + 6475965 * 2 ^ 59
def prefixEnd_6475965 : Nat := 4983230072969 + 3 ^ 40 * 6475965 * 2
def baseEnd_6475965 : Nat := 3325282746693860490855085

theorem tailTrace_6475965 : CollatzResearch.WordTrace tailWord_6475965 prefixEnd_6475965 3325282746693860490855085 := by
  unfold tailWord_6475965
  simp only [CollatzResearch.WordTrace]
  refine ⟨236197847983692286613413349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157465231989128191075608899 236197847983692286613413349)
  ·
    refine ⟨44287096496942303740015003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236197847983692286613413349 44287096496942303740015003)
    ·
      refine ⟨66430644745413455610022505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44287096496942303740015003 66430644745413455610022505)
      ·
        refine ⟨49822983559060091707516879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66430644745413455610022505 49822983559060091707516879)
        ·
          refine ⟨74734475338590137561275319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49822983559060091707516879 74734475338590137561275319)
          ·
            refine ⟨112101713007885206341912979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74734475338590137561275319 112101713007885206341912979)
            ·
              refine ⟨168152569511827809512869469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112101713007885206341912979 168152569511827809512869469)
              ·
                refine ⟨63057213566935428567326051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168152569511827809512869469 63057213566935428567326051)
                ·
                  refine ⟨94585820350403142850989077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63057213566935428567326051 94585820350403142850989077)
                  ·
                    refine ⟨4433710328925147321140113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94585820350403142850989077 4433710328925147321140113)
                    ·
                      refine ⟨3325282746693860490855085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433710328925147321140113 3325282746693860490855085)
                      ·
                        rfl

theorem cell23_6475965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_6475965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475965 prefixEnd_6475965 := by exact prefixLift 6475965
  have htrace : WordTrace (prefixWord ++ tailWord_6475965) baseStart_6475965 baseEnd_6475965 := by
    simpa [prefixWord, tailWord_6475965, baseEnd_6475965] using wordTrace_append hprefix tailTrace_6475965
  have hstable : (prefixWord ++ tailWord_6475965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475965).length < 2 ^ (prefixWord ++ tailWord_6475965).sum := by decide
  have hdescent : baseEnd_6475965 < baseStart_6475965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475982 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_6475982 : Nat := 118140960795 + 6475982 * 2 ^ 59
def prefixEnd_6475982 : Nat := 4983230072969 + 3 ^ 40 * 6475982 * 2
def baseEnd_6475982 : Nat := 3325291475864986924342507

theorem tailTrace_6475982 : CollatzResearch.WordTrace tailWord_6475982 prefixEnd_6475982 3325291475864986924342507 := by
  unfold tailWord_6475982
  simp only [CollatzResearch.WordTrace]
  refine ⟨29524808503078837314597775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157465645349753799011188133 29524808503078837314597775)
  ·
    refine ⟨44287212754618255971896663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29524808503078837314597775 44287212754618255971896663)
    ·
      refine ⟨66430819131927383957844995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44287212754618255971896663 66430819131927383957844995)
      ·
        refine ⟨99646228697891075936767493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66430819131927383957844995 99646228697891075936767493)
        ·
          refine ⟨18683667880854576738143905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99646228697891075936767493 18683667880854576738143905)
          ·
            refine ⟨14012750910640932553607929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18683667880854576738143905 14012750910640932553607929)
            ·
              refine ⟨10509563182980699415205947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14012750910640932553607929 10509563182980699415205947)
              ·
                refine ⟨15764344774471049122808921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10509563182980699415205947 15764344774471049122808921)
                ·
                  refine ⟨11823258580853286842106691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15764344774471049122808921 11823258580853286842106691)
                  ·
                    refine ⟨17734887871279930263160037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11823258580853286842106691 17734887871279930263160037)
                    ·
                      refine ⟨3325291475864986924342507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17734887871279930263160037 3325291475864986924342507)
                      ·
                        rfl

theorem cell23_6475982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_6475982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475982 prefixEnd_6475982 := by exact prefixLift 6475982
  have htrace : WordTrace (prefixWord ++ tailWord_6475982) baseStart_6475982 baseEnd_6475982 := by
    simpa [prefixWord, tailWord_6475982, baseEnd_6475982] using wordTrace_append hprefix tailTrace_6475982
  have hstable : (prefixWord ++ tailWord_6475982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475982).length < 2 ^ (prefixWord ++ tailWord_6475982).sum := by decide
  have hdescent : baseEnd_6475982 < baseStart_6475982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6475985 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_6475985 : Nat := 118140960795 + 6475985 * 2 ^ 59
def prefixEnd_6475985 : Nat := 4983230072969 + 3 ^ 40 * 6475985 * 2
def baseEnd_6475985 : Nat := 3325293016306950412604993

theorem tailTrace_6475985 : CollatzResearch.WordTrace tailWord_6475985 prefixEnd_6475985 3325293016306950412604993 := by
  unfold tailWord_6475985
  simp only [CollatzResearch.WordTrace]
  refine ⟨236198577443619830029141409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157465718295746553352760939 236198577443619830029141409)
  ·
    refine ⟨177148933082714872521856057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236198577443619830029141409 177148933082714872521856057)
    ·
      refine ⟨132861699812036154391392043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177148933082714872521856057 132861699812036154391392043)
      ·
        refine ⟨199292549718054231587088065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132861699812036154391392043 199292549718054231587088065)
        ·
          refine ⟨149469412288540673690316049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199292549718054231587088065 149469412288540673690316049)
          ·
            refine ⟨112102059216405505267737037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149469412288540673690316049 112102059216405505267737037)
            ·
              refine ⟨42038272206152064475401389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112102059216405505267737037 42038272206152064475401389)
              ·
                refine ⟨15764352077307024178275521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42038272206152064475401389 15764352077307024178275521)
                ·
                  refine ⟨11823264057980268133706641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15764352077307024178275521 11823264057980268133706641)
                  ·
                    refine ⟨8867448043485201100279981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11823264057980268133706641 8867448043485201100279981)
                    ·
                      refine ⟨3325293016306950412604993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867448043485201100279981 3325293016306950412604993)
                      ·
                        rfl

theorem cell23_6475985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_6475985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6475985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6475985 prefixEnd_6475985 := by exact prefixLift 6475985
  have htrace : WordTrace (prefixWord ++ tailWord_6475985) baseStart_6475985 baseEnd_6475985 := by
    simpa [prefixWord, tailWord_6475985, baseEnd_6475985] using wordTrace_append hprefix tailTrace_6475985
  have hstable : (prefixWord ++ tailWord_6475985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6475985).length < 2 ^ (prefixWord ++ tailWord_6475985).sum := by decide
  have hdescent : baseEnd_6475985 < baseStart_6475985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6475985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476005 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 6]
def baseStart_6476005 : Nat := 118140960795 + 6476005 * 2 ^ 59
def prefixEnd_6476005 : Nat := 4983230072969 + 3 ^ 40 * 6476005 * 2
def baseEnd_6476005 : Nat := 369478142880004481594989

theorem tailTrace_6476005 : CollatzResearch.WordTrace tailWord_6476005 prefixEnd_6476005 369478142880004481594989 := by
  unfold tailWord_6476005
  simp only [CollatzResearch.WordTrace]
  refine ⟨236199306903547373444869469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157466204602364915629912979 236199306903547373444869469)
  ·
    refine ⟨88574740088830265041826051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236199306903547373444869469 88574740088830265041826051)
    ·
      refine ⟨132862110133245397562739077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88574740088830265041826051 132862110133245397562739077)
      ·
        refine ⟨24911645649983512043013577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132862110133245397562739077 24911645649983512043013577)
        ·
          refine ⟨18683734237487634032260183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24911645649983512043013577 18683734237487634032260183)
          ·
            refine ⟨28025601356231451048390275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18683734237487634032260183 28025601356231451048390275)
            ·
              refine ⟨42038402034347176572585413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28025601356231451048390275 42038402034347176572585413)
              ·
                refine ⟨7882200381440095607359765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42038402034347176572585413 7882200381440095607359765)
                ·
                  refine ⟨369478142880004481594989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7882200381440095607359765 369478142880004481594989)
                  ·
                    rfl

theorem cell23_6476005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_6476005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476005 prefixEnd_6476005 := by exact prefixLift 6476005
  have htrace : WordTrace (prefixWord ++ tailWord_6476005) baseStart_6476005 baseEnd_6476005 := by
    simpa [prefixWord, tailWord_6476005, baseEnd_6476005] using wordTrace_append hprefix tailTrace_6476005
  have hstable : (prefixWord ++ tailWord_6476005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476005).length < 2 ^ (prefixWord ++ tailWord_6476005).sum := by decide
  have hdescent : baseEnd_6476005 < baseStart_6476005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476035 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 1, 5]
def baseStart_6476035 : Nat := 118140960795 + 6476035 * 2 ^ 59
def prefixEnd_6476035 : Nat := 4983230072969 + 3 ^ 40 * 6476035 * 2
def baseEnd_6476035 : Nat := 1108439563446558405659921

theorem tailTrace_6476035 : CollatzResearch.WordTrace tailWord_6476035 prefixEnd_6476035 1108439563446558405659921 := by
  unfold tailWord_6476035
  simp only [CollatzResearch.WordTrace]
  refine ⟨236200401093438688568461559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157466934062292459045641039 236200401093438688568461559)
  ·
    refine ⟨354300601640158032852692339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236200401093438688568461559 354300601640158032852692339)
    ·
      refine ⟨531450902460237049279038509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354300601640158032852692339 531450902460237049279038509)
      ·
        refine ⟨199294088422588893479639441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531450902460237049279038509 199294088422588893479639441)
        ·
          refine ⟨149470566316941670109729581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199294088422588893479639441 149470566316941670109729581)
          ·
            refine ⟨56051462368853126291148593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149470566316941670109729581 56051462368853126291148593)
            ·
              refine ⟨42038596776639844718361445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56051462368853126291148593 42038596776639844718361445)
              ·
                refine ⟨7882236895619970884692771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42038596776639844718361445 7882236895619970884692771)
                ·
                  refine ⟨11823355343429956327039157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7882236895619970884692771 11823355343429956327039157)
                  ·
                    refine ⟨1108439563446558405659921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11823355343429956327039157 1108439563446558405659921)
                    ·
                      rfl

theorem cell23_6476035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 5].length) (baseStart_6476035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476035 prefixEnd_6476035 := by exact prefixLift 6476035
  have htrace : WordTrace (prefixWord ++ tailWord_6476035) baseStart_6476035 baseEnd_6476035 := by
    simpa [prefixWord, tailWord_6476035, baseEnd_6476035] using wordTrace_append hprefix tailTrace_6476035
  have hstable : (prefixWord ++ tailWord_6476035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476035).length < 2 ^ (prefixWord ++ tailWord_6476035).sum := by decide
  have hdescent : baseEnd_6476035 < baseStart_6476035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476036 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_6476036 : Nat := 118140960795 + 6476036 * 2 ^ 59
def prefixEnd_6476036 : Nat := 4983230072969 + 3 ^ 40 * 6476036 * 2
def baseEnd_6476036 : Nat := 3325319203820329713067259

theorem tailTrace_6476036 : CollatzResearch.WordTrace tailWord_6476036 prefixEnd_6476036 3325319203820329713067259 := by
  unfold tailWord_6476036
  simp only [CollatzResearch.WordTrace]
  refine ⟨118100218783217532869623981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157466958377623377159498641 118100218783217532869623981)
  ·
    refine ⟨44287582043706574826108993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118100218783217532869623981 44287582043706574826108993)
    ·
      refine ⟨33215686532779931119581745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44287582043706574826108993 33215686532779931119581745)
      ·
        refine ⟨24911764899584948339686309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33215686532779931119581745 24911764899584948339686309)
        ·
          refine ⟨4670955918672177813691183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24911764899584948339686309 4670955918672177813691183)
          ·
            refine ⟨7006433878008266720536775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670955918672177813691183 7006433878008266720536775)
            ·
              refine ⟨10509650817012400080805163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006433878008266720536775 10509650817012400080805163)
              ·
                refine ⟨15764476225518600121207745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10509650817012400080805163 15764476225518600121207745)
                ·
                  refine ⟨11823357169138950090905809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15764476225518600121207745 11823357169138950090905809)
                  ·
                    refine ⟨8867517876854212568179357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11823357169138950090905809 8867517876854212568179357)
                    ·
                      refine ⟨3325319203820329713067259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867517876854212568179357 3325319203820329713067259)
                      ·
                        rfl

theorem cell23_6476036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_6476036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476036 prefixEnd_6476036 := by exact prefixLift 6476036
  have htrace : WordTrace (prefixWord ++ tailWord_6476036) baseStart_6476036 baseEnd_6476036 := by
    simpa [prefixWord, tailWord_6476036, baseEnd_6476036] using wordTrace_append hprefix tailTrace_6476036
  have hstable : (prefixWord ++ tailWord_6476036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476036).length < 2 ^ (prefixWord ++ tailWord_6476036).sum := by decide
  have hdescent : baseEnd_6476036 < baseStart_6476036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476049 : List Nat := [1, 2, 2, 1, 1, 5, 1, 5, 1, 1, 3]
def baseStart_6476049 : Nat := 118140960795 + 6476049 * 2 ^ 59
def prefixEnd_6476049 : Nat := 4983230072969 + 3 ^ 40 * 6476049 * 2
def baseEnd_6476049 : Nat := 3325325879068838162204699

theorem tailTrace_6476049 : CollatzResearch.WordTrace tailWord_6476049 prefixEnd_6476049 3325325879068838162204699 := by
  unfold tailWord_6476049
  simp only [CollatzResearch.WordTrace]
  refine ⟨236200911715387968959471201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157467274476925312639647467 236200911715387968959471201)
  ·
    refine ⟨177150683786540976719603401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236200911715387968959471201 177150683786540976719603401)
    ·
      refine ⟨132863012839905732539702551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177150683786540976719603401 132863012839905732539702551)
      ·
        refine ⟨199294519259858598809553827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132863012839905732539702551 199294519259858598809553827)
        ·
          refine ⟨298941778889787898214330741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199294519259858598809553827 298941778889787898214330741)
          ·
            refine ⟨28025791770917615457593507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298941778889787898214330741 28025791770917615457593507)
            ·
              refine ⟨42038687656376423186390261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28025791770917615457593507 42038687656376423186390261)
              ·
                refine ⟨3941126967785289673724087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42038687656376423186390261 3941126967785289673724087)
                ·
                  refine ⟨5911690451677934510586131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941126967785289673724087 5911690451677934510586131)
                  ·
                    refine ⟨8867535677516901765879197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5911690451677934510586131 8867535677516901765879197)
                    ·
                      refine ⟨3325325879068838162204699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867535677516901765879197 3325325879068838162204699)
                      ·
                        rfl

theorem cell23_6476049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_6476049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476049 prefixEnd_6476049 := by exact prefixLift 6476049
  have htrace : WordTrace (prefixWord ++ tailWord_6476049) baseStart_6476049 baseEnd_6476049 := by
    simpa [prefixWord, tailWord_6476049, baseEnd_6476049] using wordTrace_append hprefix tailTrace_6476049
  have hstable : (prefixWord ++ tailWord_6476049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476049).length < 2 ^ (prefixWord ++ tailWord_6476049).sum := by decide
  have hdescent : baseEnd_6476049 < baseStart_6476049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476066 : List Nat := [3, 3, 1, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_6476066 : Nat := 118140960795 + 6476066 * 2 ^ 59
def prefixEnd_6476066 : Nat := 4983230072969 + 3 ^ 40 * 6476066 * 2
def baseEnd_6476066 : Nat := 3325334608239964595692121

theorem tailTrace_6476066 : CollatzResearch.WordTrace tailWord_6476066 prefixEnd_6476066 3325334608239964595692121 := by
  unfold tailWord_6476066
  simp only [CollatzResearch.WordTrace]
  refine ⟨59050382939081595215710013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157467687837550920575226701 59050382939081595215710013)
  ·
    refine ⟨22143893602155598205891255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59050382939081595215710013 22143893602155598205891255)
    ·
      refine ⟨33215840403233397308836883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22143893602155598205891255 33215840403233397308836883)
      ·
        refine ⟨49823760604850095963255325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33215840403233397308836883 49823760604850095963255325)
        ·
          refine ⟨18683910226818785986220747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49823760604850095963255325 18683910226818785986220747)
          ·
            refine ⟨28025865340228178979331121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18683910226818785986220747 28025865340228178979331121)
            ·
              refine ⟨21019399005171134234498341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28025865340228178979331121 21019399005171134234498341)
              ·
                refine ⟨3941137313469587668968439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21019399005171134234498341 3941137313469587668968439)
                ·
                  refine ⟨5911705970204381503452659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941137313469587668968439 5911705970204381503452659)
                  ·
                    refine ⟨8867558955306572255178989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5911705970204381503452659 8867558955306572255178989)
                    ·
                      refine ⟨3325334608239964595692121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867558955306572255178989 3325334608239964595692121)
                      ·
                        rfl

theorem cell23_6476066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_6476066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476066 prefixEnd_6476066 := by exact prefixLift 6476066
  have htrace : WordTrace (prefixWord ++ tailWord_6476066) baseStart_6476066 baseEnd_6476066 := by
    simpa [prefixWord, tailWord_6476066, baseEnd_6476066] using wordTrace_append hprefix tailTrace_6476066
  have hstable : (prefixWord ++ tailWord_6476066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476066).length < 2 ^ (prefixWord ++ tailWord_6476066).sum := by decide
  have hdescent : baseEnd_6476066 < baseStart_6476066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476085 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_6476085 : Nat := 118140960795 + 6476085 * 2 ^ 59
def prefixEnd_6476085 : Nat := 4983230072969 + 3 ^ 40 * 6476085 * 2
def baseEnd_6476085 : Nat := 3325344364372400021354533

theorem tailTrace_6476085 : CollatzResearch.WordTrace tailWord_6476085 prefixEnd_6476085 3325344364372400021354533 := by
  unfold tailWord_6476085
  simp only [CollatzResearch.WordTrace]
  refine ⟨236202224743257547107781709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157468149828838364738521139 236202224743257547107781709)
  ·
    refine ⟨88575834278721580165418141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236202224743257547107781709 88575834278721580165418141)
    ·
      refine ⟨33215937854520592562031803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88575834278721580165418141 33215937854520592562031803)
      ·
        refine ⟨49823906781780888843047705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33215937854520592562031803 49823906781780888843047705)
        ·
          refine ⟨37367930086335666632285779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49823906781780888843047705 37367930086335666632285779)
          ·
            refine ⟨56051895129503499948428669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37367930086335666632285779 56051895129503499948428669)
            ·
              refine ⟨21019460673563812480660751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56051895129503499948428669 21019460673563812480660751)
              ·
                refine ⟨31529191010345718720991127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21019460673563812480660751 31529191010345718720991127)
                ·
                  refine ⟨47293786515518578081486691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31529191010345718720991127 47293786515518578081486691)
                  ·
                    refine ⟨70940679773277867122230037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47293786515518578081486691 70940679773277867122230037)
                    ·
                      refine ⟨3325344364372400021354533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70940679773277867122230037 3325344364372400021354533)
                      ·
                        rfl

theorem cell23_6476085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_6476085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476085 prefixEnd_6476085 := by exact prefixLift 6476085
  have htrace : WordTrace (prefixWord ++ tailWord_6476085) baseStart_6476085 baseEnd_6476085 := by
    simpa [prefixWord, tailWord_6476085, baseEnd_6476085] using wordTrace_append hprefix tailTrace_6476085
  have hstable : (prefixWord ++ tailWord_6476085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476085).length < 2 ^ (prefixWord ++ tailWord_6476085).sum := by decide
  have hdescent : baseEnd_6476085 < baseStart_6476085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476089 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6476089 : Nat := 118140960795 + 6476089 * 2 ^ 59
def prefixEnd_6476089 : Nat := 4983230072969 + 3 ^ 40 * 6476089 * 2
def baseEnd_6476089 : Nat := 3325346418295018005704515

theorem tailTrace_6476089 : CollatzResearch.WordTrace tailWord_6476089 prefixEnd_6476089 3325346418295018005704515 := by
  unfold tailWord_6476089
  simp only [CollatzResearch.WordTrace]
  refine ⟨236202370635243055790927321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157468247090162037193951547 236202370635243055790927321)
  ·
    refine ⟨177151777976432291843195491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236202370635243055790927321 177151777976432291843195491)
    ·
      refine ⟨265727666964648437764793237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177151777976432291843195491 265727666964648437764793237)
      ·
        refine ⟨12455984388967895520224683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 265727666964648437764793237 12455984388967895520224683)
        ·
          refine ⟨18683976583451843280337025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12455984388967895520224683 18683976583451843280337025)
          ·
            refine ⟨14012982437588882460252769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18683976583451843280337025 14012982437588882460252769)
            ·
              refine ⟨10509736828191661845189577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14012982437588882460252769 10509736828191661845189577)
              ·
                refine ⟨7882302621143746383892183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10509736828191661845189577 7882302621143746383892183)
                ·
                  refine ⟨11823453931715619575838275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7882302621143746383892183 11823453931715619575838275)
                  ·
                    refine ⟨17735180897573429363757413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11823453931715619575838275 17735180897573429363757413)
                    ·
                      refine ⟨3325346418295018005704515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17735180897573429363757413 3325346418295018005704515)
                      ·
                        rfl

theorem cell23_6476089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6476089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476089 prefixEnd_6476089 := by exact prefixLift 6476089
  have htrace : WordTrace (prefixWord ++ tailWord_6476089) baseStart_6476089 baseEnd_6476089 := by
    simpa [prefixWord, tailWord_6476089, baseEnd_6476089] using wordTrace_append hprefix tailTrace_6476089
  have hstable : (prefixWord ++ tailWord_6476089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476089).length < 2 ^ (prefixWord ++ tailWord_6476089).sum := by decide
  have hdescent : baseEnd_6476089 < baseStart_6476089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476100 : List Nat := [2, 3, 4, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_6476100 : Nat := 118140960795 + 6476100 * 2 ^ 59
def prefixEnd_6476100 : Nat := 4983230072969 + 3 ^ 40 * 6476100 * 2
def baseEnd_6476100 : Nat := 3325352066582217462666965

theorem tailTrace_6476100 : CollatzResearch.WordTrace tailWord_6476100 prefixEnd_6476100 3325352066582217462666965 := by
  unfold tailWord_6476100
  simp only [CollatzResearch.WordTrace]
  refine ⟨118101385919101602334788877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157468514558802136446385169 118101385919101602334788877)
  ·
    refine ⟨44288019719663100875545829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118101385919101602334788877 44288019719663100875545829)
    ·
      refine ⟨8304003697436831414164843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44288019719663100875545829 8304003697436831414164843)
      ·
        refine ⟨12456005546155247121247265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8304003697436831414164843 12456005546155247121247265)
        ·
          refine ⟨9342004159616435340935449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12456005546155247121247265 9342004159616435340935449)
          ·
            refine ⟨7006503119712326505701587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9342004159616435340935449 7006503119712326505701587)
            ·
              refine ⟨10509754679568489758552381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006503119712326505701587 10509754679568489758552381)
              ·
                refine ⟨3941158004838183659457143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10509754679568489758552381 3941158004838183659457143)
                ·
                  refine ⟨5911737007257275489185715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941158004838183659457143 5911737007257275489185715)
                  ·
                    refine ⟨8867605510885913233778573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5911737007257275489185715 8867605510885913233778573)
                    ·
                      refine ⟨3325352066582217462666965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867605510885913233778573 3325352066582217462666965)
                      ·
                        rfl

theorem cell23_6476100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_6476100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476100 prefixEnd_6476100 := by exact prefixLift 6476100
  have htrace : WordTrace (prefixWord ++ tailWord_6476100) baseStart_6476100 baseEnd_6476100 := by
    simpa [prefixWord, tailWord_6476100, baseEnd_6476100] using wordTrace_append hprefix tailTrace_6476100
  have hstable : (prefixWord ++ tailWord_6476100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476100).length < 2 ^ (prefixWord ++ tailWord_6476100).sum := by decide
  have hdescent : baseEnd_6476100 < baseStart_6476100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476105 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 3]
def baseStart_6476105 : Nat := 118140960795 + 6476105 * 2 ^ 59
def prefixEnd_6476105 : Nat := 4983230072969 + 3 ^ 40 * 6476105 * 2
def baseEnd_6476105 : Nat := 3325354633985489943104441

theorem tailTrace_6476105 : CollatzResearch.WordTrace tailWord_6476105 prefixEnd_6476105 3325354633985489943104441 := by
  unfold tailWord_6476105
  simp only [CollatzResearch.WordTrace]
  refine ⟨236202954203185090523509769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157468636135456727015673179 236202954203185090523509769)
  ·
    refine ⟨177152215652388817892632327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236202954203185090523509769 177152215652388817892632327)
    ·
      refine ⟨265728323478583226838948491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177152215652388817892632327 265728323478583226838948491)
      ·
        refine ⟨398592485217874840258422737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265728323478583226838948491 398592485217874840258422737)
        ·
          refine ⟨298944363913406130193817053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398592485217874840258422737 298944363913406130193817053)
          ·
            refine ⟨112104136467527298822681395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298944363913406130193817053 112104136467527298822681395)
            ·
              refine ⟨168156204701290948234022093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112104136467527298822681395 168156204701290948234022093)
              ·
                refine ⟨63058576762984105587758285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168156204701290948234022093 63058576762984105587758285)
                ·
                  refine ⟨23646966286119039595409357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63058576762984105587758285 23646966286119039595409357)
                  ·
                    refine ⟨8867612357294639848278509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23646966286119039595409357 8867612357294639848278509)
                    ·
                      refine ⟨3325354633985489943104441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867612357294639848278509 3325354633985489943104441)
                      ·
                        rfl

theorem cell23_6476105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_6476105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476105 prefixEnd_6476105 := by exact prefixLift 6476105
  have htrace : WordTrace (prefixWord ++ tailWord_6476105) baseStart_6476105 baseEnd_6476105 := by
    simpa [prefixWord, tailWord_6476105, baseEnd_6476105] using wordTrace_append hprefix tailTrace_6476105
  have hstable : (prefixWord ++ tailWord_6476105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476105).length < 2 ^ (prefixWord ++ tailWord_6476105).sum := by decide
  have hdescent : baseEnd_6476105 < baseStart_6476105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476185 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 7]
def baseStart_6476185 : Nat := 118140960795 + 6476185 * 2 ^ 59
def prefixEnd_6476185 : Nat := 4983230072969 + 3 ^ 40 * 6476185 * 2
def baseEnd_6476185 : Nat := 369488412493094403344897

theorem tailTrace_6476185 : CollatzResearch.WordTrace tailWord_6476185 prefixEnd_6476185 369488412493094403344897 := by
  unfold tailWord_6476185
  simp only [CollatzResearch.WordTrace]
  refine ⟨236205872042895264186422009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157470581361930176124281339 236205872042895264186422009)
  ·
    refine ⟨177154404032171448139816507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236205872042895264186422009 177154404032171448139816507)
    ·
      refine ⟨265731606048257172209724761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177154404032171448139816507 265731606048257172209724761)
      ·
        refine ⟨199298704536192879157293571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265731606048257172209724761 199298704536192879157293571)
        ·
          refine ⟨298948056804289318735940357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199298704536192879157293571 298948056804289318735940357)
          ·
            refine ⟨56052760650804247262988817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298948056804289318735940357 56052760650804247262988817)
            ·
              refine ⟨42039570488103185447241613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56052760650804247262988817 42039570488103185447241613)
              ·
                refine ⟨15764838933038694542715605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42039570488103185447241613 15764838933038694542715605)
                ·
                  refine ⟨369488412493094403344897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15764838933038694542715605 369488412493094403344897)
                  ·
                    rfl

theorem cell23_6476185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 7].length) (baseStart_6476185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476185 prefixEnd_6476185 := by exact prefixLift 6476185
  have htrace : WordTrace (prefixWord ++ tailWord_6476185) baseStart_6476185 baseEnd_6476185 := by
    simpa [prefixWord, tailWord_6476185, baseEnd_6476185] using wordTrace_append hprefix tailTrace_6476185
  have hstable : (prefixWord ++ tailWord_6476185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476185).length < 2 ^ (prefixWord ++ tailWord_6476185).sum := by decide
  have hdescent : baseEnd_6476185 < baseStart_6476185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476192 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_6476192 : Nat := 118140960795 + 6476192 * 2 ^ 59
def prefixEnd_6476192 : Nat := 4983230072969 + 3 ^ 40 * 6476192 * 2
def baseEnd_6476192 : Nat := 3325399306802431102716541

theorem tailTrace_6476192 : CollatzResearch.WordTrace tailWord_6476192 prefixEnd_6476192 3325399306802431102716541 := by
  unfold tailWord_6476192
  simp only [CollatzResearch.WordTrace]
  refine ⟨118103063676934952190963415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157470751569246602921284553 118103063676934952190963415)
  ·
    refine ⟨177154595515402428286445123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118103063676934952190963415 177154595515402428286445123)
    ·
      refine ⟨265731893273103642429667685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177154595515402428286445123 265731893273103642429667685)
      ·
        refine ⟨49824729988706932955562691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265731893273103642429667685 49824729988706932955562691)
        ·
          refine ⟨74737094983060399433344037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49824729988706932955562691 74737094983060399433344037)
          ·
            refine ⟨14013205309323824893752007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74737094983060399433344037 14013205309323824893752007)
            ·
              refine ⟨21019807963985737340628011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14013205309323824893752007 21019807963985737340628011)
              ·
                refine ⟨31529711945978606010942017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21019807963985737340628011 31529711945978606010942017)
                ·
                  refine ⟨23647283959483954508206513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31529711945978606010942017 23647283959483954508206513)
                  ·
                    refine ⟨17735462969612965881154885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23647283959483954508206513 17735462969612965881154885)
                    ·
                      refine ⟨3325399306802431102716541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17735462969612965881154885 3325399306802431102716541)
                      ·
                        rfl

theorem cell23_6476192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_6476192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476192 prefixEnd_6476192 := by exact prefixLift 6476192
  have htrace : WordTrace (prefixWord ++ tailWord_6476192) baseStart_6476192 baseEnd_6476192 := by
    simpa [prefixWord, tailWord_6476192, baseEnd_6476192] using wordTrace_append hprefix tailTrace_6476192
  have hstable : (prefixWord ++ tailWord_6476192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476192).length < 2 ^ (prefixWord ++ tailWord_6476192).sum := by decide
  have hdescent : baseEnd_6476192 < baseStart_6476192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476196 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_6476196 : Nat := 118140960795 + 6476196 * 2 ^ 59
def prefixEnd_6476196 : Nat := 4983230072969 + 3 ^ 40 * 6476196 * 2
def baseEnd_6476196 : Nat := 3325401360725049087066523

theorem tailTrace_6476196 : CollatzResearch.WordTrace tailWord_6476196 prefixEnd_6476196 3325401360725049087066523 := by
  unfold tailWord_6476196
  simp only [CollatzResearch.WordTrace]
  refine ⟨118103136622927706532536221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157470848830570275376714961 118103136622927706532536221)
  ·
    refine ⟨44288676233597889949701083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118103136622927706532536221 44288676233597889949701083)
    ·
      refine ⟨66433014350396834924551625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44288676233597889949701083 66433014350396834924551625)
      ·
        refine ⟨49824760762797626193413719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66433014350396834924551625 49824760762797626193413719)
        ·
          refine ⟨74737141144196439290120579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49824760762797626193413719 74737141144196439290120579)
          ·
            refine ⟨112105711716294658935180869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74737141144196439290120579 112105711716294658935180869)
            ·
              refine ⟨21019820946805248550346413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112105711716294658935180869 21019820946805248550346413)
              ·
                refine ⟨7882432855051968206379905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21019820946805248550346413 7882432855051968206379905)
                ·
                  refine ⟨5911824641288976154784929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7882432855051968206379905 5911824641288976154784929)
                  ·
                    refine ⟨4433868480966732116088697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5911824641288976154784929 4433868480966732116088697)
                    ·
                      refine ⟨3325401360725049087066523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433868480966732116088697 3325401360725049087066523)
                      ·
                        rfl

theorem cell23_6476196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_6476196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476196 prefixEnd_6476196 := by exact prefixLift 6476196
  have htrace : WordTrace (prefixWord ++ tailWord_6476196) baseStart_6476196 baseEnd_6476196 := by
    simpa [prefixWord, tailWord_6476196, baseEnd_6476196] using wordTrace_append hprefix tailTrace_6476196
  have hstable : (prefixWord ++ tailWord_6476196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476196).length < 2 ^ (prefixWord ++ tailWord_6476196).sum := by decide
  have hdescent : baseEnd_6476196 < baseStart_6476196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476265 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_6476265 : Nat := 118140960795 + 6476265 * 2 ^ 59
def prefixEnd_6476265 : Nat := 4983230072969 + 3 ^ 40 * 6476265 * 2
def baseEnd_6476265 : Nat := 3325436790890209317103705

theorem tailTrace_6476265 : CollatzResearch.WordTrace tailWord_6476265 prefixEnd_6476265 3325436790890209317103705 := by
  unfold tailWord_6476265
  simp only [CollatzResearch.WordTrace]
  refine ⟨236208789882605437849334249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157472526588403625232889499 236208789882605437849334249)
  ·
    refine ⟨177156592411954078387000687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236208789882605437849334249 177156592411954078387000687)
    ·
      refine ⟨265734888617931117580501031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177156592411954078387000687 265734888617931117580501031)
      ·
        refine ⟨398602332926896676370751547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265734888617931117580501031 398602332926896676370751547)
        ·
          refine ⟨597903499390345014556127321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398602332926896676370751547 597903499390345014556127321)
          ·
            refine ⟨448427624542758760917095491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597903499390345014556127321 448427624542758760917095491)
            ·
              refine ⟨672641436814138141375643237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448427624542758760917095491 672641436814138141375643237)
              ·
                refine ⟨126120269402650901507933107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672641436814138141375643237 126120269402650901507933107)
                ·
                  refine ⟨189180404103976352261899661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126120269402650901507933107 189180404103976352261899661)
                  ·
                    refine ⟨70942651538991132098212373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189180404103976352261899661 70942651538991132098212373)
                    ·
                      refine ⟨3325436790890209317103705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70942651538991132098212373 3325436790890209317103705)
                      ·
                        rfl

theorem cell23_6476265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_6476265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476265 prefixEnd_6476265 := by exact prefixLift 6476265
  have htrace : WordTrace (prefixWord ++ tailWord_6476265) baseStart_6476265 baseEnd_6476265 := by
    simpa [prefixWord, tailWord_6476265, baseEnd_6476265] using wordTrace_append hprefix tailTrace_6476265
  have hstable : (prefixWord ++ tailWord_6476265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476265).length < 2 ^ (prefixWord ++ tailWord_6476265).sum := by decide
  have hdescent : baseEnd_6476265 < baseStart_6476265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476269 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6476269 : Nat := 118140960795 + 6476269 * 2 ^ 59
def prefixEnd_6476269 : Nat := 4983230072969 + 3 ^ 40 * 6476269 * 2
def baseEnd_6476269 : Nat := 3325438844812827301453687

theorem tailTrace_6476269 : CollatzResearch.WordTrace tailWord_6476269 prefixEnd_6476269 3325438844812827301453687 := by
  unfold tailWord_6476269
  simp only [CollatzResearch.WordTrace]
  refine ⟨236208935774590946532479861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157472623849727297688319907 236208935774590946532479861)
  ·
    refine ⟨22144587728867901237419987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236208935774590946532479861 22144587728867901237419987)
    ·
      refine ⟨33216881593301851856129981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22144587728867901237419987 33216881593301851856129981)
      ·
        refine ⟨12456330597488194446048743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33216881593301851856129981 12456330597488194446048743)
        ·
          refine ⟨18684495896232291669073115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12456330597488194446048743 18684495896232291669073115)
          ·
            refine ⟨28026743844348437503609673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18684495896232291669073115 28026743844348437503609673)
            ·
              refine ⟨21020057883261328127707255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28026743844348437503609673 21020057883261328127707255)
              ·
                refine ⟨31530086824891992191560883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21020057883261328127707255 31530086824891992191560883)
                ·
                  refine ⟨47295130237337988287341325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31530086824891992191560883 47295130237337988287341325)
                  ·
                    refine ⟨17735673839001745607752997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47295130237337988287341325 17735673839001745607752997)
                    ·
                      refine ⟨3325438844812827301453687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17735673839001745607752997 3325438844812827301453687)
                      ·
                        rfl

theorem cell23_6476269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6476269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476269 prefixEnd_6476269 := by exact prefixLift 6476269
  have htrace : WordTrace (prefixWord ++ tailWord_6476269) baseStart_6476269 baseEnd_6476269 := by
    simpa [prefixWord, tailWord_6476269, baseEnd_6476269] using wordTrace_append hprefix tailTrace_6476269
  have hstable : (prefixWord ++ tailWord_6476269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476269).length < 2 ^ (prefixWord ++ tailWord_6476269).sum := by decide
  have hdescent : baseEnd_6476269 < baseStart_6476269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476272 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 3]
def baseStart_6476272 : Nat := 118140960795 + 6476272 * 2 ^ 59
def prefixEnd_6476272 : Nat := 4983230072969 + 3 ^ 40 * 6476272 * 2
def baseEnd_6476272 : Nat := 3325440385254790789716173

theorem tailTrace_6476272 : CollatzResearch.WordTrace tailWord_6476272 prefixEnd_6476272 3325440385254790789716173 := by
  unfold tailWord_6476272
  simp only [CollatzResearch.WordTrace]
  refine ⟨118104522596790039022419535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157472696795720052029892713 118104522596790039022419535)
  ·
    refine ⟨177156783895185058533629303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118104522596790039022419535 177156783895185058533629303)
    ·
      refine ⟨265735175842777587800443955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177156783895185058533629303 265735175842777587800443955)
      ·
        refine ⟨398602763764166381700665933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265735175842777587800443955 398602763764166381700665933)
        ·
          refine ⟨149476036411562393137749725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398602763764166381700665933 149476036411562393137749725)
          ·
            refine ⟨56053513654335897426656147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149476036411562393137749725 56053513654335897426656147)
            ·
              refine ⟨84080270481503846139984221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56053513654335897426656147 84080270481503846139984221)
              ·
                refine ⟨31530101430563942302494083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84080270481503846139984221 31530101430563942302494083)
                ·
                  refine ⟨47295152145845913453741125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31530101430563942302494083 47295152145845913453741125)
                  ·
                    refine ⟨8867841027346108772576461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47295152145845913453741125 8867841027346108772576461)
                    ·
                      refine ⟨3325440385254790789716173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867841027346108772576461 3325440385254790789716173)
                      ·
                        rfl

theorem cell23_6476272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_6476272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476272 prefixEnd_6476272 := by exact prefixLift 6476272
  have htrace : WordTrace (prefixWord ++ tailWord_6476272) baseStart_6476272 baseEnd_6476272 := by
    simpa [prefixWord, tailWord_6476272, baseEnd_6476272] using wordTrace_append hprefix tailTrace_6476272
  have hstable : (prefixWord ++ tailWord_6476272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476272).length < 2 ^ (prefixWord ++ tailWord_6476272).sum := by decide
  have hdescent : baseEnd_6476272 < baseStart_6476272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476275 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 10]
def baseStart_6476275 : Nat := 118140960795 + 6476275 * 2 ^ 59
def prefixEnd_6476275 : Nat := 4983230072969 + 3 ^ 40 * 6476275 * 2
def baseEnd_6476275 : Nat := 369493547299639364219851

theorem tailTrace_6476275 : CollatzResearch.WordTrace tailWord_6476275 prefixEnd_6476275 369493547299639364219851 := by
  unfold tailWord_6476275
  simp only [CollatzResearch.WordTrace]
  refine ⟨236209154612569209557198279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157472769741712806371465519 236209154612569209557198279)
  ·
    refine ⟨354313731918853814335797419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236209154612569209557198279 354313731918853814335797419)
    ·
      refine ⟨531470597878280721503696129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354313731918853814335797419 531470597878280721503696129)
      ·
        refine ⟨398602948408710541127772097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531470597878280721503696129 398602948408710541127772097)
        ·
          refine ⟨298952211306532905845829073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398602948408710541127772097 298952211306532905845829073)
          ·
            refine ⟨224214158479899679384371805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298952211306532905845829073 224214158479899679384371805)
            ·
              refine ⟨84080309429962379769139427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224214158479899679384371805 84080309429962379769139427)
              ·
                refine ⟨126120464144943569653709141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84080309429962379769139427 126120464144943569653709141)
                ·
                  refine ⟨369493547299639364219851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126120464144943569653709141 369493547299639364219851)
                  ·
                    rfl

theorem cell23_6476275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 10].length) (baseStart_6476275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476275 prefixEnd_6476275 := by exact prefixLift 6476275
  have htrace : WordTrace (prefixWord ++ tailWord_6476275) baseStart_6476275 baseEnd_6476275 := by
    simpa [prefixWord, tailWord_6476275, baseEnd_6476275] using wordTrace_append hprefix tailTrace_6476275
  have hstable : (prefixWord ++ tailWord_6476275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476275).length < 2 ^ (prefixWord ++ tailWord_6476275).sum := by decide
  have hdescent : baseEnd_6476275 < baseStart_6476275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476289 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_6476289 : Nat := 118140960795 + 6476289 * 2 ^ 59
def prefixEnd_6476289 : Nat := 4983230072969 + 3 ^ 40 * 6476289 * 2
def baseEnd_6476289 : Nat := 3325449114425917223203595

theorem tailTrace_6476289 : CollatzResearch.WordTrace tailWord_6476289 prefixEnd_6476289 3325449114425917223203595 := by
  unfold tailWord_6476289
  simp only [CollatzResearch.WordTrace]
  refine ⟨236209665234518489948207921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157473110156345659965471947 236209665234518489948207921)
  ·
    refine ⟨177157248925888867461155941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236209665234518489948207921 177157248925888867461155941)
    ·
      refine ⟨33216984173604162648966739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177157248925888867461155941 33216984173604162648966739)
      ·
        refine ⟨49825476260406243973450109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33216984173604162648966739 49825476260406243973450109)
        ·
          refine ⟨18684553597652341490043791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49825476260406243973450109 18684553597652341490043791)
          ·
            refine ⟨28026830396478512235065687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18684553597652341490043791 28026830396478512235065687)
            ·
              refine ⟨42040245594717768352598531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28026830396478512235065687 42040245594717768352598531)
              ·
                refine ⟨63060368392076652528897797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42040245594717768352598531 63060368392076652528897797)
                ·
                  refine ⟨11823819073514372349168337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63060368392076652528897797 11823819073514372349168337)
                  ·
                    refine ⟨8867864305135779261876253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11823819073514372349168337 8867864305135779261876253)
                    ·
                      refine ⟨3325449114425917223203595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867864305135779261876253 3325449114425917223203595)
                      ·
                        rfl

theorem cell23_6476289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_6476289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476289 prefixEnd_6476289 := by exact prefixLift 6476289
  have htrace : WordTrace (prefixWord ++ tailWord_6476289) baseStart_6476289 baseEnd_6476289 := by
    simpa [prefixWord, tailWord_6476289, baseEnd_6476289] using wordTrace_append hprefix tailTrace_6476289
  have hstable : (prefixWord ++ tailWord_6476289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476289).length < 2 ^ (prefixWord ++ tailWord_6476289).sum := by decide
  have hdescent : baseEnd_6476289 < baseStart_6476289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476319 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 3]
def baseStart_6476319 : Nat := 118140960795 + 6476319 * 2 ^ 59
def prefixEnd_6476319 : Nat := 4983230072969 + 3 ^ 40 * 6476319 * 2
def baseEnd_6476319 : Nat := 3325464518845552105828457

theorem tailTrace_6476319 : CollatzResearch.WordTrace tailWord_6476319 prefixEnd_6476319 3325464518845552105828457 := by
  unfold tailWord_6476319
  simp only [CollatzResearch.WordTrace]
  refine ⟨236210759424409805071800011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157473839616273203381200007 236210759424409805071800011)
  ·
    refine ⟨354316139136614707607700017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236210759424409805071800011 354316139136614707607700017)
    ·
      refine ⟨265737104352461030705775013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354316139136614707607700017 265737104352461030705775013)
      ·
        refine ⟨49825707066086443257332815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265737104352461030705775013 49825707066086443257332815)
        ·
          refine ⟨74738560599129664885999223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49825707066086443257332815 74738560599129664885999223)
          ·
            refine ⟨112107840898694497328998835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74738560599129664885999223 112107840898694497328998835)
            ·
              refine ⟨168161761348041745993498253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112107840898694497328998835 168161761348041745993498253)
              ·
                refine ⟨63060660505515654747561845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168161761348041745993498253 63060660505515654747561845)
                ·
                  refine ⟨5911936922392092632583923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63060660505515654747561845 5911936922392092632583923)
                  ·
                    refine ⟨8867905383588138948875885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5911936922392092632583923 8867905383588138948875885)
                    ·
                      refine ⟨3325464518845552105828457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8867905383588138948875885 3325464518845552105828457)
                      ·
                        rfl

theorem cell23_6476319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_6476319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476319 prefixEnd_6476319 := by exact prefixLift 6476319
  have htrace : WordTrace (prefixWord ++ tailWord_6476319) baseStart_6476319 baseEnd_6476319 := by
    simpa [prefixWord, tailWord_6476319, baseEnd_6476319] using wordTrace_append hprefix tailTrace_6476319
  have hstable : (prefixWord ++ tailWord_6476319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476319).length < 2 ^ (prefixWord ++ tailWord_6476319).sum := by decide
  have hdescent : baseEnd_6476319 < baseStart_6476319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476346 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2]
def baseStart_6476346 : Nat := 118140960795 + 6476346 * 2 ^ 59
def prefixEnd_6476346 : Nat := 4983230072969 + 3 ^ 40 * 6476346 * 2
def baseEnd_6476346 : Nat := 3325478382823223500190833

theorem tailTrace_6476346 : CollatzResearch.WordTrace tailWord_6476346 prefixEnd_6476346 3325478382823223500190833 := by
  unfold tailWord_6476346
  simp only [CollatzResearch.WordTrace]
  refine ⟨59052936048827997170758223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157474496130207992455355261 59052936048827997170758223)
  ·
    refine ⟨88579404073241995756137335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59052936048827997170758223 88579404073241995756137335)
    ·
      refine ⟨132869106109862993634206003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88579404073241995756137335 132869106109862993634206003)
      ·
        refine ⟨199303659164794490451309005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132869106109862993634206003 199303659164794490451309005)
        ·
          refine ⟨74738872186797933919240877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199303659164794490451309005 74738872186797933919240877)
          ·
            refine ⟨28027077070049225219715329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74738872186797933919240877 28027077070049225219715329)
            ·
              refine ⟨21020307802536918914786497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28027077070049225219715329 21020307802536918914786497)
              ·
                refine ⟨15765230851902689186089873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21020307802536918914786497 15765230851902689186089873)
                ·
                  refine ⟨11823923138927016889567405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15765230851902689186089873 11823923138927016889567405)
                  ·
                    refine ⟨4433971177097631333587777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11823923138927016889567405 4433971177097631333587777)
                    ·
                      refine ⟨3325478382823223500190833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433971177097631333587777 3325478382823223500190833)
                      ·
                        rfl

theorem cell23_6476346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_6476346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476346 prefixEnd_6476346 := by exact prefixLift 6476346
  have htrace : WordTrace (prefixWord ++ tailWord_6476346) baseStart_6476346 baseEnd_6476346 := by
    simpa [prefixWord, tailWord_6476346, baseEnd_6476346] using wordTrace_append hprefix tailTrace_6476346
  have hstable : (prefixWord ++ tailWord_6476346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476346).length < 2 ^ (prefixWord ++ tailWord_6476346).sum := by decide
  have hdescent : baseEnd_6476346 < baseStart_6476346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476359 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_6476359 : Nat := 118140960795 + 6476359 * 2 ^ 59
def prefixEnd_6476359 : Nat := 4983230072969 + 3 ^ 40 * 6476359 * 2
def baseEnd_6476359 : Nat := 3325485058071731949328273

theorem tailTrace_6476359 : CollatzResearch.WordTrace tailWord_6476359 prefixEnd_6476359 3325485058071731949328273 := by
  unfold tailWord_6476359
  simp only [CollatzResearch.WordTrace]
  refine ⟨236212218344264891903256131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157474812229509927935504087 236212218344264891903256131)
  ·
    refine ⟨354318327516397337854884197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236212218344264891903256131 354318327516397337854884197)
    ·
      refine ⟨66434686409324500847790787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354318327516397337854884197 66434686409324500847790787)
      ·
        refine ⟨99652029613986751271686181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66434686409324500847790787 99652029613986751271686181)
        ·
          refine ⟨18684755552622515863441159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99652029613986751271686181 18684755552622515863441159)
          ·
            refine ⟨28027133328933773795161739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18684755552622515863441159 28027133328933773795161739)
            ·
              refine ⟨42040699993400660692742609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28027133328933773795161739 42040699993400660692742609)
              ·
                refine ⟨31530524995050495519556957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42040699993400660692742609 31530524995050495519556957)
                ·
                  refine ⟨11823946873143935819833859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31530524995050495519556957 11823946873143935819833859)
                  ·
                    refine ⟨17735920309715903729750789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11823946873143935819833859 17735920309715903729750789)
                    ·
                      refine ⟨3325485058071731949328273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17735920309715903729750789 3325485058071731949328273)
                      ·
                        rfl

theorem cell23_6476359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_6476359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476359 prefixEnd_6476359 := by exact prefixLift 6476359
  have htrace : WordTrace (prefixWord ++ tailWord_6476359) baseStart_6476359 baseEnd_6476359 := by
    simpa [prefixWord, tailWord_6476359, baseEnd_6476359] using wordTrace_append hprefix tailTrace_6476359
  have hstable : (prefixWord ++ tailWord_6476359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476359).length < 2 ^ (prefixWord ++ tailWord_6476359).sum := by decide
  have hdescent : baseEnd_6476359 < baseStart_6476359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476369 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 1, 6]
def baseStart_6476369 : Nat := 118140960795 + 6476369 * 2 ^ 59
def prefixEnd_6476369 : Nat := 4983230072969 + 3 ^ 40 * 6476369 * 2
def baseEnd_6476369 : Nat := 1108496730959425636734409

theorem tailTrace_6476369 : CollatzResearch.WordTrace tailWord_6476369 prefixEnd_6476369 1108496730959425636734409 := by
  unfold tailWord_6476369
  simp only [CollatzResearch.WordTrace]
  refine ⟨236212583074228663611120161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157475055382819109074080107 236212583074228663611120161)
  ·
    refine ⟨177159437305671497708340121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236212583074228663611120161 177159437305671497708340121)
    ·
      refine ⟨132869577979253623281255091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177159437305671497708340121 132869577979253623281255091)
      ·
        refine ⟨199304366968880434921882637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132869577979253623281255091 199304366968880434921882637)
        ·
          refine ⟨74739137613330163095705989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199304366968880434921882637 74739137613330163095705989)
          ·
            refine ⟨14013588302499405580444873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74739137613330163095705989 14013588302499405580444873)
            ·
              refine ⟨10510191226874554185333655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14013588302499405580444873 10510191226874554185333655)
              ·
                refine ⟨15765286840311831278000483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10510191226874554185333655 15765286840311831278000483)
                ·
                  refine ⟨23647930260467746917000725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15765286840311831278000483 23647930260467746917000725)
                  ·
                    refine ⟨1108496730959425636734409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23647930260467746917000725 1108496730959425636734409)
                    ·
                      rfl

theorem cell23_6476369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_6476369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476369 prefixEnd_6476369 := by exact prefixLift 6476369
  have htrace : WordTrace (prefixWord ++ tailWord_6476369) baseStart_6476369 baseEnd_6476369 := by
    simpa [prefixWord, tailWord_6476369, baseEnd_6476369] using wordTrace_append hprefix tailTrace_6476369
  have hstable : (prefixWord ++ tailWord_6476369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476369).length < 2 ^ (prefixWord ++ tailWord_6476369).sum := by decide
  have hdescent : baseEnd_6476369 < baseStart_6476369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476376 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 5, 2, 2]
def baseStart_6476376 : Nat := 118140960795 + 6476376 * 2 ^ 59
def prefixEnd_6476376 : Nat := 4983230072969 + 3 ^ 40 * 6476376 * 2
def baseEnd_6476376 : Nat := 3325493787242858382815695

theorem tailTrace_6476376 : CollatzResearch.WordTrace tailWord_6476376 prefixEnd_6476376 3325493787242858382815695 := by
  unfold tailWord_6476376
  simp only [CollatzResearch.WordTrace]
  refine ⟨118106419192601651903312491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157475225590135535871083321 118106419192601651903312491)
  ·
    refine ⟨177159628788902477854968737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118106419192601651903312491 177159628788902477854968737)
    ·
      refine ⟨132869721591676858391226553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177159628788902477854968737 132869721591676858391226553)
      ·
        refine ⟨99652291193757643793419915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132869721591676858391226553 99652291193757643793419915)
        ·
          refine ⟨149478436790636465690129873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99652291193757643793419915 149478436790636465690129873)
          ·
            refine ⟨112108827592977349267597405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149478436790636465690129873 112108827592977349267597405)
            ·
              refine ⟨42040810347366505975349027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112108827592977349267597405 42040810347366505975349027)
              ·
                refine ⟨63061215521049758963023541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42040810347366505975349027 63061215521049758963023541)
                ·
                  refine ⟨5911988955098414902783457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63061215521049758963023541 5911988955098414902783457)
                  ·
                    refine ⟨4433991716323811177087593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5911988955098414902783457 4433991716323811177087593)
                    ·
                      refine ⟨3325493787242858382815695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433991716323811177087593 3325493787242858382815695)
                      ·
                        rfl

theorem cell23_6476376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_6476376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476376 prefixEnd_6476376 := by exact prefixLift 6476376
  have htrace : WordTrace (prefixWord ++ tailWord_6476376) baseStart_6476376 baseEnd_6476376 := by
    simpa [prefixWord, tailWord_6476376, baseEnd_6476376] using wordTrace_append hprefix tailTrace_6476376
  have hstable : (prefixWord ++ tailWord_6476376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476376).length < 2 ^ (prefixWord ++ tailWord_6476376).sum := by decide
  have hdescent : baseEnd_6476376 < baseStart_6476376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476380 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_6476380 : Nat := 118140960795 + 6476380 * 2 ^ 59
def prefixEnd_6476380 : Nat := 4983230072969 + 3 ^ 40 * 6476380 * 2
def baseEnd_6476380 : Nat := 3325495841165476367165677

theorem tailTrace_6476380 : CollatzResearch.WordTrace tailWord_6476380 prefixEnd_6476380 3325495841165476367165677 := by
  unfold tailWord_6476380
  simp only [CollatzResearch.WordTrace]
  refine ⟨118106492138594406244885297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157475322851459208326513729 118106492138594406244885297)
  ·
    refine ⟨88579869103945804683663973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118106492138594406244885297 88579869103945804683663973)
    ·
      refine ⟨16608725456989838378186995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88579869103945804683663973 16608725456989838378186995)
      ·
        refine ⟨24913088185484757567280493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16608725456989838378186995 24913088185484757567280493)
        ·
          refine ⟨9342408069556784087730185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24913088185484757567280493 9342408069556784087730185)
          ·
            refine ⟨7006806052167588065797639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9342408069556784087730185 7006806052167588065797639)
            ·
              refine ⟨10510209078251382098696459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006806052167588065797639 10510209078251382098696459)
              ·
                refine ⟨15765313617377073148044689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10510209078251382098696459 15765313617377073148044689)
                ·
                  refine ⟨11823985213032804861033517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15765313617377073148044689 11823985213032804861033517)
                  ·
                    refine ⟨4433994454887301822887569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11823985213032804861033517 4433994454887301822887569)
                    ·
                      refine ⟨3325495841165476367165677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4433994454887301822887569 3325495841165476367165677)
                      ·
                        rfl

theorem cell23_6476380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_6476380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476380 prefixEnd_6476380 := by exact prefixLift 6476380
  have htrace : WordTrace (prefixWord ++ tailWord_6476380) baseStart_6476380 baseEnd_6476380 := by
    simpa [prefixWord, tailWord_6476380, baseEnd_6476380] using wordTrace_append hprefix tailTrace_6476380
  have hstable : (prefixWord ++ tailWord_6476380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476380).length < 2 ^ (prefixWord ++ tailWord_6476380).sum := by decide
  have hdescent : baseEnd_6476380 < baseStart_6476380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476412 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_6476412 : Nat := 118140960795 + 6476412 * 2 ^ 59
def prefixEnd_6476412 : Nat := 4983230072969 + 3 ^ 40 * 6476412 * 2
def baseEnd_6476412 : Nat := 1108504090848806747321843

theorem tailTrace_6476412 : CollatzResearch.WordTrace tailWord_6476412 prefixEnd_6476412 1108504090848806747321843 := by
  unfold tailWord_6476412
  simp only [CollatzResearch.WordTrace]
  refine ⟨118107075706536440977467745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157476100942048587969956993 118107075706536440977467745)
  ·
    refine ⟨88580306779902330733100809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118107075706536440977467745 88580306779902330733100809)
    ·
      refine ⟨66435230084926748049825607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88580306779902330733100809 66435230084926748049825607)
      ·
        refine ⟨99652845127390122074738411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66435230084926748049825607 99652845127390122074738411)
        ·
          refine ⟨149479267691085183112107617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99652845127390122074738411 149479267691085183112107617)
          ·
            refine ⟨112109450768313887334080713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149479267691085183112107617 112109450768313887334080713)
            ·
              refine ⟨84082088076235415500560535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112109450768313887334080713 84082088076235415500560535)
              ·
                refine ⟨126123132114353123250840803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84082088076235415500560535 126123132114353123250840803)
                ·
                  refine ⟨189184698171529684876261205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126123132114353123250840803 189184698171529684876261205)
                  ·
                    refine ⟨1108504090848806747321843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 189184698171529684876261205 1108504090848806747321843)
                    ·
                      rfl

theorem cell23_6476412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_6476412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476412 prefixEnd_6476412 := by exact prefixLift 6476412
  have htrace : WordTrace (prefixWord ++ tailWord_6476412) baseStart_6476412 baseEnd_6476412 := by
    simpa [prefixWord, tailWord_6476412, baseEnd_6476412] using wordTrace_append hprefix tailTrace_6476412
  have hstable : (prefixWord ++ tailWord_6476412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476412).length < 2 ^ (prefixWord ++ tailWord_6476412).sum := by decide
  have hdescent : baseEnd_6476412 < baseStart_6476412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476500 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6476500 : Nat := 118140960795 + 6476500 * 2 ^ 59
def prefixEnd_6476500 : Nat := 4983230072969 + 3 ^ 40 * 6476500 * 2
def baseEnd_6476500 : Nat := 3325557458844015897665125

theorem tailTrace_6476500 : CollatzResearch.WordTrace tailWord_6476500 prefixEnd_6476500 3325557458844015897665125 := by
  unfold tailWord_6476500
  simp only [CollatzResearch.WordTrace]
  refine ⟨118108680518377036492069477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157478240691169381989425969 118108680518377036492069477)
  ·
    refine ⟨22145377597195694342263027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118108680518377036492069477 22145377597195694342263027)
    ·
      refine ⟨33218066395793541513394541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22145377597195694342263027 33218066395793541513394541)
      ·
        refine ⟨12456774898422578067522953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33218066395793541513394541 12456774898422578067522953)
        ·
          refine ⟨9342581173816933550642215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12456774898422578067522953 9342581173816933550642215)
          ·
            refine ⟨14013871760725400325963323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9342581173816933550642215 14013871760725400325963323)
            ·
              refine ⟨21020807641088100488944985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14013871760725400325963323 21020807641088100488944985)
              ·
                refine ⟨15765605730816075366708739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21020807641088100488944985 15765605730816075366708739)
                ·
                  refine ⟨23648408596224113050063109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15765605730816075366708739 23648408596224113050063109)
                  ·
                    refine ⟨4434076611792021196886833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23648408596224113050063109 4434076611792021196886833)
                    ·
                      refine ⟨3325557458844015897665125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434076611792021196886833 3325557458844015897665125)
                      ·
                        rfl

theorem cell23_6476500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6476500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476500 prefixEnd_6476500 := by exact prefixLift 6476500
  have htrace : WordTrace (prefixWord ++ tailWord_6476500) baseStart_6476500 baseEnd_6476500 := by
    simpa [prefixWord, tailWord_6476500, baseEnd_6476500] using wordTrace_append hprefix tailTrace_6476500
  have hstable : (prefixWord ++ tailWord_6476500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476500).length < 2 ^ (prefixWord ++ tailWord_6476500).sum := by decide
  have hdescent : baseEnd_6476500 < baseStart_6476500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476506 : List Nat := [3, 1, 1, 2, 2, 2, 2, 5, 5]
def baseStart_6476506 : Nat := 118140960795 + 6476506 * 2 ^ 59
def prefixEnd_6476506 : Nat := 4983230072969 + 3 ^ 40 * 6476506 * 2
def baseEnd_6476506 : Nat := 369506726636438097132233

theorem tailTrace_6476506 : CollatzResearch.WordTrace tailWord_6476506 prefixEnd_6476506 369506726636438097132233 := by
  unfold tailWord_6476506
  simp only [CollatzResearch.WordTrace]
  refine ⟨59054394968683084002214343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157478386583154890672571581 59054394968683084002214343)
  ·
    refine ⟨88581592453024626003321515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59054394968683084002214343 88581592453024626003321515)
    ·
      refine ⟨132872388679536939004982273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88581592453024626003321515 132872388679536939004982273)
      ·
        refine ⟨99654291509652704253736705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132872388679536939004982273 99654291509652704253736705)
        ·
          refine ⟨74740718632239528190302529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99654291509652704253736705 74740718632239528190302529)
          ·
            refine ⟨56055538974179646142726897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74740718632239528190302529 56055538974179646142726897)
            ·
              refine ⟨42041654230634734607045173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56055538974179646142726897 42041654230634734607045173)
              ·
                refine ⟨3941405084122006369410485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42041654230634734607045173 3941405084122006369410485)
                ·
                  refine ⟨369506726636438097132233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3941405084122006369410485 369506726636438097132233)
                  ·
                    rfl

theorem cell23_6476506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_6476506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476506 prefixEnd_6476506 := by exact prefixLift 6476506
  have htrace : WordTrace (prefixWord ++ tailWord_6476506) baseStart_6476506 baseEnd_6476506 := by
    simpa [prefixWord, tailWord_6476506, baseEnd_6476506] using wordTrace_append hprefix tailTrace_6476506
  have hstable : (prefixWord ++ tailWord_6476506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476506).length < 2 ^ (prefixWord ++ tailWord_6476506).sum := by decide
  have hdescent : baseEnd_6476506 < baseStart_6476506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476529 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_6476529 : Nat := 118140960795 + 6476529 * 2 ^ 59
def prefixEnd_6476529 : Nat := 4983230072969 + 3 ^ 40 * 6476529 * 2
def baseEnd_6476529 : Nat := 3325572349782996284202491

theorem tailTrace_6476529 : CollatzResearch.WordTrace tailWord_6476529 prefixEnd_6476529 3325572349782996284202491 := by
  unfold tailWord_6476529
  simp only [CollatzResearch.WordTrace]
  refine ⟨236218418753649010936944641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157478945835766007291296427 236218418753649010936944641)
  ·
    refine ⟨177163814065236758202708481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236218418753649010936944641 177163814065236758202708481)
    ·
      refine ⟨132872860548927568652031361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177163814065236758202708481 132872860548927568652031361)
      ·
        refine ⟨99654645411695676489023521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132872860548927568652031361 99654645411695676489023521)
        ·
          refine ⟨74740984058771757366767641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99654645411695676489023521 74740984058771757366767641)
          ·
            refine ⟨56055738044078818025075731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74740984058771757366767641 56055738044078818025075731)
            ·
              refine ⟨84083607066118227037613597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56055738044078818025075731 84083607066118227037613597)
              ·
                refine ⟨31531352649794335139105099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84083607066118227037613597 31531352649794335139105099)
                ·
                  refine ⟨47297028974691502708657649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31531352649794335139105099 47297028974691502708657649)
                  ·
                    refine ⟨35472771731018627031493237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47297028974691502708657649 35472771731018627031493237)
                    ·
                      refine ⟨3325572349782996284202491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35472771731018627031493237 3325572349782996284202491)
                      ·
                        rfl

theorem cell23_6476529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_6476529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476529 prefixEnd_6476529 := by exact prefixLift 6476529
  have htrace : WordTrace (prefixWord ++ tailWord_6476529) baseStart_6476529 baseEnd_6476529 := by
    simpa [prefixWord, tailWord_6476529, baseEnd_6476529] using wordTrace_append hprefix tailTrace_6476529
  have hstable : (prefixWord ++ tailWord_6476529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476529).length < 2 ^ (prefixWord ++ tailWord_6476529).sum := by decide
  have hdescent : baseEnd_6476529 < baseStart_6476529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476556 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 3, 6, 2]
def baseStart_6476556 : Nat := 118140960795 + 6476556 * 2 ^ 59
def prefixEnd_6476556 : Nat := 4983230072969 + 3 ^ 40 * 6476556 * 2
def baseEnd_6476556 : Nat := 3325586213760667678564867

theorem tailTrace_6476556 : CollatzResearch.WordTrace tailWord_6476556 prefixEnd_6476556 3325586213760667678564867 := by
  unfold tailWord_6476556
  simp only [CollatzResearch.WordTrace]
  refine ⟨118109701762275597274088761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157479602349700796365451681 118109701762275597274088761)
  ·
    refine ⟨88582276321706697955566571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118109701762275597274088761 88582276321706697955566571)
    ·
      refine ⟨132873414482560046933349857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88582276321706697955566571 132873414482560046933349857)
      ·
        refine ⟨99655060861920035200012393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132873414482560046933349857 99655060861920035200012393)
        ·
          refine ⟨74741295646440026400009295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99655060861920035200012393 74741295646440026400009295)
          ·
            refine ⟨112111943469660039600013943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74741295646440026400009295 112111943469660039600013943)
            ·
              refine ⟨168167915204490059400020915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112111943469660039600013943 168167915204490059400020915)
              ·
                refine ⟨252251872806735089100031373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168167915204490059400020915 252251872806735089100031373)
                ·
                  refine ⟨94594452302525658412511765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252251872806735089100031373 94594452302525658412511765)
                  ·
                    refine ⟨4434114951680890238086489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94594452302525658412511765 4434114951680890238086489)
                    ·
                      refine ⟨3325586213760667678564867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434114951680890238086489 3325586213760667678564867)
                      ·
                        rfl

theorem cell23_6476556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_6476556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476556 prefixEnd_6476556 := by exact prefixLift 6476556
  have htrace : WordTrace (prefixWord ++ tailWord_6476556) baseStart_6476556 baseEnd_6476556 := by
    simpa [prefixWord, tailWord_6476556, baseEnd_6476556] using wordTrace_append hprefix tailTrace_6476556
  have hstable : (prefixWord ++ tailWord_6476556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476556).length < 2 ^ (prefixWord ++ tailWord_6476556).sum := by decide
  have hdescent : baseEnd_6476556 < baseStart_6476556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476590 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6476590 : Nat := 118140960795 + 6476590 * 2 ^ 59
def prefixEnd_6476590 : Nat := 4983230072969 + 3 ^ 40 * 6476590 * 2
def baseEnd_6476590 : Nat := 3325603672102920545539711

theorem tailTrace_6476590 : CollatzResearch.WordTrace tailWord_6476590 prefixEnd_6476590 3325603672102920545539711 := by
  unfold tailWord_6476590
  simp only [CollatzResearch.WordTrace]
  refine ⟨29527580450803502294364403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157480429070952012236610149 29527580450803502294364403)
  ·
    refine ⟨44291370676205253441546605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29527580450803502294364403 44291370676205253441546605)
    ·
      refine ⟨16609264003576970040579977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44291370676205253441546605 16609264003576970040579977)
      ·
        refine ⟨12456948002682727530434983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16609264003576970040579977 12456948002682727530434983)
        ·
          refine ⟨18685422004024091295652475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12456948002682727530434983 18685422004024091295652475)
          ·
            refine ⟨28028133006036136943478713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18685422004024091295652475 28028133006036136943478713)
            ·
              refine ⟨21021099754527102707609035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28028133006036136943478713 21021099754527102707609035)
              ·
                refine ⟨31531649631790654061413553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21021099754527102707609035 31531649631790654061413553)
                ·
                  refine ⟨23648737223842990546060165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31531649631790654061413553 23648737223842990546060165)
                  ·
                    refine ⟨4434138229470560727386281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23648737223842990546060165 4434138229470560727386281)
                    ·
                      refine ⟨3325603672102920545539711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434138229470560727386281 3325603672102920545539711)
                      ·
                        rfl

theorem cell23_6476590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6476590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476590 prefixEnd_6476590 := by exact prefixLift 6476590
  have htrace : WordTrace (prefixWord ++ tailWord_6476590) baseStart_6476590 baseEnd_6476590 := by
    simpa [prefixWord, tailWord_6476590, baseEnd_6476590] using wordTrace_append hprefix tailTrace_6476590
  have hstable : (prefixWord ++ tailWord_6476590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476590).length < 2 ^ (prefixWord ++ tailWord_6476590).sum := by decide
  have hdescent : baseEnd_6476590 < baseStart_6476590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476599 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_6476599 : Nat := 118140960795 + 6476599 * 2 ^ 59
def prefixEnd_6476599 : Nat := 4983230072969 + 3 ^ 40 * 6476599 * 2
def baseEnd_6476599 : Nat := 3325608293428811010327169

theorem tailTrace_6476599 : CollatzResearch.WordTrace tailWord_6476599 prefixEnd_6476599 3325608293428811010327169 := by
  unfold tailWord_6476599
  simp only [CollatzResearch.WordTrace]
  refine ⟨236220971863395412891992851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157480647908930275261328567 236220971863395412891992851)
  ·
    refine ⟨354331457795093119337989277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236220971863395412891992851 354331457795093119337989277)
    ·
      refine ⟨132874296673159919751745979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 354331457795093119337989277 132874296673159919751745979)
      ·
        refine ⟨199311445009739879627618969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132874296673159919751745979 199311445009739879627618969)
        ·
          refine ⟨149483583757304909720714227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199311445009739879627618969 149483583757304909720714227)
          ·
            refine ⟨224225375635957364581071341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149483583757304909720714227 224225375635957364581071341)
            ·
              refine ⟨84084515863484011717901753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224225375635957364581071341 84084515863484011717901753)
              ·
                refine ⟨63063386897613008788426315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84084515863484011717901753 63063386897613008788426315)
                ·
                  refine ⟨94595080346419513182639473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63063386897613008788426315 94595080346419513182639473)
                  ·
                    refine ⟨70946310259814634886979605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94595080346419513182639473 70946310259814634886979605)
                    ·
                      refine ⟨3325608293428811010327169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70946310259814634886979605 3325608293428811010327169)
                      ·
                        rfl

theorem cell23_6476599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_6476599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476599 prefixEnd_6476599 := by exact prefixLift 6476599
  have htrace : WordTrace (prefixWord ++ tailWord_6476599) baseStart_6476599 baseEnd_6476599 := by
    simpa [prefixWord, tailWord_6476599, baseEnd_6476599] using wordTrace_append hprefix tailTrace_6476599
  have hstable : (prefixWord ++ tailWord_6476599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476599).length < 2 ^ (prefixWord ++ tailWord_6476599).sum := by decide
  have hdescent : baseEnd_6476599 < baseStart_6476599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476633 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 4, 3, 2]
def baseStart_6476633 : Nat := 118140960795 + 6476633 * 2 ^ 59
def prefixEnd_6476633 : Nat := 4983230072969 + 3 ^ 40 * 6476633 * 2
def baseEnd_6476633 : Nat := 3325625751771063877302013

theorem tailTrace_6476633 : CollatzResearch.WordTrace tailWord_6476633 prefixEnd_6476633 3325625751771063877302013 := by
  unfold tailWord_6476633
  simp only [CollatzResearch.WordTrace]
  refine ⟨236222211945272236698730553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157481474630181491132487035 236222211945272236698730553)
  ·
    refine ⟨177166658958954177524047915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236222211945272236698730553 177166658958954177524047915)
    ·
      refine ⟨265749988438431266286071873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177166658958954177524047915 265749988438431266286071873)
      ·
        refine ⟨199312491328823449714553905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265749988438431266286071873 199312491328823449714553905)
        ·
          refine ⟨149484368496617587285915429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199312491328823449714553905 149484368496617587285915429)
          ·
            refine ⟨28028319093115797616109143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149484368496617587285915429 28028319093115797616109143)
            ·
              refine ⟨42042478639673696424163715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28028319093115797616109143 42042478639673696424163715)
              ·
                refine ⟨63063717959510544636245573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42042478639673696424163715 63063717959510544636245573)
                ·
                  refine ⟨11824447117408227119296045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63063717959510544636245573 11824447117408227119296045)
                  ·
                    refine ⟨4434167669028085169736017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11824447117408227119296045 4434167669028085169736017)
                    ·
                      refine ⟨3325625751771063877302013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4434167669028085169736017 3325625751771063877302013)
                      ·
                        rfl

theorem cell23_6476633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_6476633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476633 prefixEnd_6476633 := by exact prefixLift 6476633
  have htrace : WordTrace (prefixWord ++ tailWord_6476633) baseStart_6476633 baseEnd_6476633 := by
    simpa [prefixWord, tailWord_6476633, baseEnd_6476633] using wordTrace_append hprefix tailTrace_6476633
  have hstable : (prefixWord ++ tailWord_6476633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476633).length < 2 ^ (prefixWord ++ tailWord_6476633).sum := by decide
  have hdescent : baseEnd_6476633 < baseStart_6476633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476683 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 3]
def baseStart_6476683 : Nat := 118140960795 + 6476683 * 2 ^ 59
def prefixEnd_6476683 : Nat := 4983230072969 + 3 ^ 40 * 6476683 * 2
def baseEnd_6476683 : Nat := 3325651425803788681676783

theorem tailTrace_6476683 : CollatzResearch.WordTrace tailWord_6476683 prefixEnd_6476683 3325651425803788681676783 := by
  unfold tailWord_6476683
  simp only [CollatzResearch.WordTrace]
  refine ⟨236224035595091095238050703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157482690396727396825367135 236224035595091095238050703)
  ·
    refine ⟨354336053392636642857076055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236224035595091095238050703 354336053392636642857076055)
    ·
      refine ⟨531504080088954964285614083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354336053392636642857076055 531504080088954964285614083)
      ·
        refine ⟨797256120133432446428421125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531504080088954964285614083 797256120133432446428421125)
        ·
          refine ⟨149485522525018583705328961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 797256120133432446428421125 149485522525018583705328961)
          ·
            refine ⟨112114141893763937778996721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149485522525018583705328961 112114141893763937778996721)
            ·
              refine ⟨84085606420322953334247541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112114141893763937778996721 84085606420322953334247541)
              ·
                refine ⟨7883025601905276875085707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84085606420322953334247541 7883025601905276875085707)
                ·
                  refine ⟨11824538402857915312628561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883025601905276875085707 11824538402857915312628561)
                  ·
                    refine ⟨8868403802143436484471421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11824538402857915312628561 8868403802143436484471421)
                    ·
                      refine ⟨3325651425803788681676783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8868403802143436484471421 3325651425803788681676783)
                      ·
                        rfl

theorem cell23_6476683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 2, 3].length) (baseStart_6476683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476683 prefixEnd_6476683 := by exact prefixLift 6476683
  have htrace : WordTrace (prefixWord ++ tailWord_6476683) baseStart_6476683 baseEnd_6476683 := by
    simpa [prefixWord, tailWord_6476683, baseEnd_6476683] using wordTrace_append hprefix tailTrace_6476683
  have hstable : (prefixWord ++ tailWord_6476683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476683).length < 2 ^ (prefixWord ++ tailWord_6476683).sum := by decide
  have hdescent : baseEnd_6476683 < baseStart_6476683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476703 : List Nat := [1, 1, 2, 5, 2, 3, 1, 8]
def baseStart_6476703 : Nat := 118140960795 + 6476703 * 2 ^ 59
def prefixEnd_6476703 : Nat := 4983230072969 + 3 ^ 40 * 6476703 * 2
def baseEnd_6476703 : Nat := 123172655385810318645433

theorem tailTrace_6476703 : CollatzResearch.WordTrace tailWord_6476703 prefixEnd_6476703 123172655385810318645433 := by
  unfold tailWord_6476703
  simp only [CollatzResearch.WordTrace]
  refine ⟨236224765055018638653778763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157483176703345759102519175 236224765055018638653778763)
  ·
    refine ⟨354337147582527957980668145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236224765055018638653778763 354337147582527957980668145)
    ·
      refine ⟨265752860686895968485501109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354337147582527957980668145 265752860686895968485501109)
      ·
        refine ⟨24914330689396497045515729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265752860686895968485501109 24914330689396497045515729)
        ·
          refine ⟨18685748017047372784136797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24914330689396497045515729 18685748017047372784136797)
          ·
            refine ⟨7007155506392764794051299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18685748017047372784136797 7007155506392764794051299)
            ·
              refine ⟨10510733259589147191076949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007155506392764794051299 10510733259589147191076949)
              ·
                refine ⟨123172655385810318645433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10510733259589147191076949 123172655385810318645433)
                ·
                  rfl

theorem cell23_6476703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 8].length) (baseStart_6476703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476703 prefixEnd_6476703 := by exact prefixLift 6476703
  have htrace : WordTrace (prefixWord ++ tailWord_6476703) baseStart_6476703 baseEnd_6476703 := by
    simpa [prefixWord, tailWord_6476703, baseEnd_6476703] using wordTrace_append hprefix tailTrace_6476703
  have hstable : (prefixWord ++ tailWord_6476703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476703).length < 2 ^ (prefixWord ++ tailWord_6476703).sum := by decide
  have hdescent : baseEnd_6476703 < baseStart_6476703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476713 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 3]
def baseStart_6476713 : Nat := 118140960795 + 6476713 * 2 ^ 59
def prefixEnd_6476713 : Nat := 4983230072969 + 3 ^ 40 * 6476713 * 2
def baseEnd_6476713 : Nat := 3325666830223423564301645

theorem tailTrace_6476713 : CollatzResearch.WordTrace tailWord_6476713 prefixEnd_6476713 3325666830223423564301645 := by
  unfold tailWord_6476713
  simp only [CollatzResearch.WordTrace]
  refine ⟨236225129784982410361642793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157483419856654940241095195 236225129784982410361642793)
  ·
    refine ⟨177168847338736807771232095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236225129784982410361642793 177168847338736807771232095)
    ·
      refine ⟨265753271008105211656848143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177168847338736807771232095 265753271008105211656848143)
      ·
        refine ⟨398629906512157817485272215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265753271008105211656848143 398629906512157817485272215)
        ·
          refine ⟨597944859768236726227908323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398629906512157817485272215 597944859768236726227908323)
          ·
            refine ⟨896917289652355089341862485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597944859768236726227908323 896917289652355089341862485)
            ·
              refine ⟨10510749488113536203224951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 896917289652355089341862485 10510749488113536203224951)
              ·
                refine ⟨15766124232170304304837427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10510749488113536203224951 15766124232170304304837427)
                ·
                  refine ⟨23649186348255456457256141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15766124232170304304837427 23649186348255456457256141)
                  ·
                    refine ⟨8868444880595796171471053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23649186348255456457256141 8868444880595796171471053)
                    ·
                      refine ⟨3325666830223423564301645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8868444880595796171471053 3325666830223423564301645)
                      ·
                        rfl

theorem cell23_6476713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_6476713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476713 prefixEnd_6476713 := by exact prefixLift 6476713
  have htrace : WordTrace (prefixWord ++ tailWord_6476713) baseStart_6476713 baseEnd_6476713 := by
    simpa [prefixWord, tailWord_6476713, baseEnd_6476713] using wordTrace_append hprefix tailTrace_6476713
  have hstable : (prefixWord ++ tailWord_6476713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476713).length < 2 ^ (prefixWord ++ tailWord_6476713).sum := by decide
  have hdescent : baseEnd_6476713 < baseStart_6476713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6476747 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 3]
def baseStart_6476747 : Nat := 118140960795 + 6476747 * 2 ^ 59
def prefixEnd_6476747 : Nat := 4983230072969 + 3 ^ 40 * 6476747 * 2
def baseEnd_6476747 : Nat := 3325684288565676431276489

theorem tailTrace_6476747 : CollatzResearch.WordTrace tailWord_6476747 prefixEnd_6476747 3325684288565676431276489 := by
  unfold tailWord_6476747
  simp only [CollatzResearch.WordTrace]
  refine ⟨236226369866859234168380495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157484246577906156112253663 236226369866859234168380495)
  ·
    refine ⟨354339554800288851252570743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236226369866859234168380495 354339554800288851252570743)
    ·
      refine ⟨531509332200433276878856115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354339554800288851252570743 531509332200433276878856115)
      ·
        refine ⟨797263998300649915318284173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531509332200433276878856115 797263998300649915318284173)
        ·
          refine ⟨298973999362743718244356565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 797263998300649915318284173 298973999362743718244356565)
          ·
            refine ⟨7007203110064305896352107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 298973999362743718244356565 7007203110064305896352107)
            ·
              refine ⟨10510804665096458844528161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007203110064305896352107 10510804665096458844528161)
              ·
                refine ⟨7883103498822344133396121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10510804665096458844528161 7883103498822344133396121)
                ·
                  refine ⟨5912327624116758100047091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883103498822344133396121 5912327624116758100047091)
                  ·
                    refine ⟨8868491436175137150070637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5912327624116758100047091 8868491436175137150070637)
                    ·
                      refine ⟨3325684288565676431276489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8868491436175137150070637 3325684288565676431276489)
                      ·
                        rfl

theorem cell23_6476747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 3].length) (baseStart_6476747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6476747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6476747 prefixEnd_6476747 := by exact prefixLift 6476747
  have htrace : WordTrace (prefixWord ++ tailWord_6476747) baseStart_6476747 baseEnd_6476747 := by
    simpa [prefixWord, tailWord_6476747, baseEnd_6476747] using wordTrace_append hprefix tailTrace_6476747
  have hstable : (prefixWord ++ tailWord_6476747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6476747).length < 2 ^ (prefixWord ++ tailWord_6476747).sum := by decide
  have hdescent : baseEnd_6476747 < baseStart_6476747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6476747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
