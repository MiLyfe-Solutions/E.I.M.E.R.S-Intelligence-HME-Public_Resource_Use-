import V185TrunkScan23Chunk1312

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7775900 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_7775900 : Nat := 118140960795 + 7775900 * 2 ^ 59
def prefixEnd_7775900 : Nat := 4983230072969 + 3 ^ 40 * 7775900 * 2
def baseEnd_7775900 : Nat := 3992774221296231989189293

theorem tailTrace_7775900 : CollatzResearch.WordTrace tailWord_7775900 prefixEnd_7775900 3992774221296231989189293 := by
  unfold tailWord_7775900
  simp only [CollatzResearch.WordTrace]
  refine ⟨141805186264624896418098577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189073581686166528557464769 141805186264624896418098577)
  ·
    refine ⟨106353889698468672313573933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141805186264624896418098577 106353889698468672313573933)
    ·
      refine ⟨39882708636925752117590225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106353889698468672313573933 39882708636925752117590225)
      ·
        refine ⟨29912031477694314088192669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39882708636925752117590225 29912031477694314088192669)
        ·
          refine ⟨11217011804135367783072251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29912031477694314088192669 11217011804135367783072251)
          ·
            refine ⟨16825517706203051674608377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11217011804135367783072251 16825517706203051674608377)
            ·
              refine ⟨12619138279652288755956283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16825517706203051674608377 12619138279652288755956283)
              ·
                refine ⟨18928707419478433133934425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12619138279652288755956283 18928707419478433133934425)
                ·
                  refine ⟨14196530564608824850450819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18928707419478433133934425 14196530564608824850450819)
                  ·
                    refine ⟨21294795846913237275676229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14196530564608824850450819 21294795846913237275676229)
                    ·
                      refine ⟨3992774221296231989189293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21294795846913237275676229 3992774221296231989189293)
                      ·
                        rfl

theorem cell23_7775900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_7775900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775900 prefixEnd_7775900 := by exact prefixLift 7775900
  have htrace : WordTrace (prefixWord ++ tailWord_7775900) baseStart_7775900 baseEnd_7775900 := by
    simpa [prefixWord, tailWord_7775900, baseEnd_7775900] using wordTrace_append hprefix tailTrace_7775900
  have hstable : (prefixWord ++ tailWord_7775900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775900).length < 2 ^ (prefixWord ++ tailWord_7775900).sum := by decide
  have hdescent : baseEnd_7775900 < baseStart_7775900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775927 : List Nat := [1, 1, 3, 1, 5, 1, 4, 2, 1, 4]
def baseStart_7775927 : Nat := 118140960795 + 7775927 * 2 ^ 59
def prefixEnd_7775927 : Nat := 4983230072969 + 3 ^ 40 * 7775927 * 2
def baseEnd_7775927 : Nat := 1330929361757967794517223

theorem tailTrace_7775927 : CollatzResearch.WordTrace tailWord_7775927 prefixEnd_7775927 1330929361757967794517223 := by
  unfold tailWord_7775927
  simp only [CollatzResearch.WordTrace]
  refine ⟨283611357300151976447430035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189074238200101317631620023 283611357300151976447430035)
  ·
    refine ⟨425417035950227964671145053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283611357300151976447430035 425417035950227964671145053)
    ·
      refine ⟨159531388481335486751679395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425417035950227964671145053 159531388481335486751679395)
      ·
        refine ⟨239297082722003230127519093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159531388481335486751679395 239297082722003230127519093)
        ·
          refine ⟨22434101505187802824454915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239297082722003230127519093 22434101505187802824454915)
          ·
            refine ⟨33651152257781704236682373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22434101505187802824454915 33651152257781704236682373)
            ·
              refine ⟨6309591048334069544377945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33651152257781704236682373 6309591048334069544377945)
              ·
                refine ⟨4732193286250552158283459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6309591048334069544377945 4732193286250552158283459)
                ·
                  refine ⟨7098289929375828237425189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732193286250552158283459 7098289929375828237425189)
                  ·
                    refine ⟨1330929361757967794517223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7098289929375828237425189 1330929361757967794517223)
                    ·
                      rfl

theorem cell23_7775927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_7775927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775927 prefixEnd_7775927 := by exact prefixLift 7775927
  have htrace : WordTrace (prefixWord ++ tailWord_7775927) baseStart_7775927 baseEnd_7775927 := by
    simpa [prefixWord, tailWord_7775927, baseEnd_7775927] using wordTrace_append hprefix tailTrace_7775927
  have hstable : (prefixWord ++ tailWord_7775927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775927).length < 2 ^ (prefixWord ++ tailWord_7775927).sum := by decide
  have hdescent : baseEnd_7775927 < baseStart_7775927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775936 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 5, 5]
def baseStart_7775936 : Nat := 118140960795 + 7775936 * 2 ^ 59
def prefixEnd_7775936 : Nat := 4983230072969 + 3 ^ 40 * 7775936 * 2
def baseEnd_7775936 : Nat := 1330930902199931282779709

theorem tailTrace_7775936 : CollatzResearch.WordTrace tailWord_7775936 prefixEnd_7775936 1330930902199931282779709 := by
  unfold tailWord_7775936
  simp only [CollatzResearch.WordTrace]
  refine ⟨141805842778559685492253831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189074457038079580656338441 141805842778559685492253831)
  ·
    refine ⟨212708764167839528238380747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141805842778559685492253831 212708764167839528238380747)
    ·
      refine ⟨319063146251759292357571121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212708764167839528238380747 319063146251759292357571121)
      ·
        refine ⟨239297359688819469268178341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319063146251759292357571121 239297359688819469268178341)
        ·
          refine ⟨44868254941653650487783439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239297359688819469268178341 44868254941653650487783439)
          ·
            refine ⟨67302382412480475731675159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44868254941653650487783439 67302382412480475731675159)
            ·
              refine ⟨100953573618720713597512739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67302382412480475731675159 100953573618720713597512739)
              ·
                refine ⟨151430360428081070396269109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100953573618720713597512739 151430360428081070396269109)
                ·
                  refine ⟨14196596290132600349650229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151430360428081070396269109 14196596290132600349650229)
                  ·
                    refine ⟨1330930902199931282779709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14196596290132600349650229 1330930902199931282779709)
                    ·
                      rfl

theorem cell23_7775936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_7775936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775936 prefixEnd_7775936 := by exact prefixLift 7775936
  have htrace : WordTrace (prefixWord ++ tailWord_7775936) baseStart_7775936 baseEnd_7775936 := by
    simpa [prefixWord, tailWord_7775936, baseEnd_7775936] using wordTrace_append hprefix tailTrace_7775936
  have hstable : (prefixWord ++ tailWord_7775936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775936).length < 2 ^ (prefixWord ++ tailWord_7775936).sum := by decide
  have hdescent : baseEnd_7775936 < baseStart_7775936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775943 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_7775943 : Nat := 118140960795 + 7775943 * 2 ^ 59
def prefixEnd_7775943 : Nat := 4983230072969 + 3 ^ 40 * 7775943 * 2
def baseEnd_7775943 : Nat := 3992796300964375320951595

theorem tailTrace_7775943 : CollatzResearch.WordTrace tailWord_7775943 prefixEnd_7775943 3992796300964375320951595 := by
  unfold tailWord_7775943
  simp only [CollatzResearch.WordTrace]
  refine ⟨283611940868094011180012483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189074627245396007453341655 283611940868094011180012483)
  ·
    refine ⟨425417911302141016770018725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283611940868094011180012483 425417911302141016770018725)
    ·
      refine ⟨79765858369151440644378511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425417911302141016770018725 79765858369151440644378511)
      ·
        refine ⟨119648787553727160966567767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79765858369151440644378511 119648787553727160966567767)
        ·
          refine ⟨179473181330590741449851651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119648787553727160966567767 179473181330590741449851651)
          ·
            refine ⟨269209771995886112174777477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179473181330590741449851651 269209771995886112174777477)
            ·
              refine ⟨50476832249228646032770777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269209771995886112174777477 50476832249228646032770777)
              ·
                refine ⟨37857624186921484524578083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50476832249228646032770777 37857624186921484524578083)
                ·
                  refine ⟨56786436280382226786867125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37857624186921484524578083 56786436280382226786867125)
                  ·
                    refine ⟨5323728401285833761268793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56786436280382226786867125 5323728401285833761268793)
                    ·
                      refine ⟨3992796300964375320951595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323728401285833761268793 3992796300964375320951595)
                      ·
                        rfl

theorem cell23_7775943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_7775943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775943 prefixEnd_7775943 := by exact prefixLift 7775943
  have htrace : WordTrace (prefixWord ++ tailWord_7775943) baseStart_7775943 baseEnd_7775943 := by
    simpa [prefixWord, tailWord_7775943, baseEnd_7775943] using wordTrace_append hprefix tailTrace_7775943
  have hstable : (prefixWord ++ tailWord_7775943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775943).length < 2 ^ (prefixWord ++ tailWord_7775943).sum := by decide
  have hdescent : baseEnd_7775943 < baseStart_7775943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775950 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_7775950 : Nat := 118140960795 + 7775950 * 2 ^ 59
def prefixEnd_7775950 : Nat := 4983230072969 + 3 ^ 40 * 7775950 * 2
def baseEnd_7775950 : Nat := 3992799895328956793564063

theorem tailTrace_7775950 : CollatzResearch.WordTrace tailWord_7775950 prefixEnd_7775950 3992799895328956793564063 := by
  unfold tailWord_7775950
  simp only [CollatzResearch.WordTrace]
  refine ⟨35451524522383581421939663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189074797452712434250344869 35451524522383581421939663)
  ·
    refine ⟨53177286783575372132909495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35451524522383581421939663 53177286783575372132909495)
    ·
      refine ⟨79765930175363058199364243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53177286783575372132909495 79765930175363058199364243)
      ·
        refine ⟨119648895263044587299046365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79765930175363058199364243 119648895263044587299046365)
        ·
          refine ⟨44868335723641720237142387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119648895263044587299046365 44868335723641720237142387)
          ·
            refine ⟨67302503585462580355713581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44868335723641720237142387 67302503585462580355713581)
            ·
              refine ⟨25238438844548467633392593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67302503585462580355713581 25238438844548467633392593)
              ·
                refine ⟨18928829133411350725044445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25238438844548467633392593 18928829133411350725044445)
                ·
                  refine ⟨7098310925029256521891667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18928829133411350725044445 7098310925029256521891667)
                  ·
                    refine ⟨10647466387543884782837501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7098310925029256521891667 10647466387543884782837501)
                    ·
                      refine ⟨3992799895328956793564063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10647466387543884782837501 3992799895328956793564063)
                      ·
                        rfl

theorem cell23_7775950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_7775950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775950 prefixEnd_7775950 := by exact prefixLift 7775950
  have htrace : WordTrace (prefixWord ++ tailWord_7775950) baseStart_7775950 baseEnd_7775950 := by
    simpa [prefixWord, tailWord_7775950, baseEnd_7775950] using wordTrace_append hprefix tailTrace_7775950
  have hstable : (prefixWord ++ tailWord_7775950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775950).length < 2 ^ (prefixWord ++ tailWord_7775950).sum := by decide
  have hdescent : baseEnd_7775950 < baseStart_7775950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775967 : List Nat := [1, 1, 2, 3, 2, 2, 4, 3, 1, 1, 3]
def baseStart_7775967 : Nat := 118140960795 + 7775967 * 2 ^ 59
def prefixEnd_7775967 : Nat := 4983230072969 + 3 ^ 40 * 7775967 * 2
def baseEnd_7775967 : Nat := 3992808624500083227051485

theorem tailTrace_7775967 : CollatzResearch.WordTrace tailWord_7775967 prefixEnd_7775967 3992808624500083227051485 := by
  unfold tailWord_7775967
  simp only [CollatzResearch.WordTrace]
  refine ⟨283612816220007063278886155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189075210813338042185924103 283612816220007063278886155)
  ·
    refine ⟨425419224330010594918329233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283612816220007063278886155 425419224330010594918329233)
    ·
      refine ⟨319064418247507946188746925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425419224330010594918329233 319064418247507946188746925)
      ·
        refine ⟨119649156842815479820780097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319064418247507946188746925 119649156842815479820780097)
        ·
          refine ⟨89736867632111609865585073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119649156842815479820780097 89736867632111609865585073)
          ·
            refine ⟨67302650724083707399188805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89736867632111609865585073 67302650724083707399188805)
            ·
              refine ⟨12619247010765695137347901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67302650724083707399188805 12619247010765695137347901)
              ·
                refine ⟨4732217629037135676505463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12619247010765695137347901 4732217629037135676505463)
                ·
                  refine ⟨7098326443555703514758195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732217629037135676505463 7098326443555703514758195)
                  ·
                    refine ⟨10647489665333555272137293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7098326443555703514758195 10647489665333555272137293)
                    ·
                      refine ⟨3992808624500083227051485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10647489665333555272137293 3992808624500083227051485)
                      ·
                        rfl

theorem cell23_7775967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_7775967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775967 prefixEnd_7775967 := by exact prefixLift 7775967
  have htrace : WordTrace (prefixWord ++ tailWord_7775967) baseStart_7775967 baseEnd_7775967 := by
    simpa [prefixWord, tailWord_7775967, baseEnd_7775967] using wordTrace_append hprefix tailTrace_7775967
  have hstable : (prefixWord ++ tailWord_7775967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775967).length < 2 ^ (prefixWord ++ tailWord_7775967).sum := by decide
  have hdescent : baseEnd_7775967 < baseStart_7775967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775983 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 4, 4]
def baseStart_7775983 : Nat := 118140960795 + 7775983 * 2 ^ 59
def prefixEnd_7775983 : Nat := 4983230072969 + 3 ^ 40 * 7775983 * 2
def baseEnd_7775983 : Nat := 1330938946730185054817137

theorem tailTrace_7775983 : CollatzResearch.WordTrace tailWord_7775983 prefixEnd_7775983 1330938946730185054817137 := by
  unfold tailWord_7775983
  simp only [CollatzResearch.WordTrace]
  refine ⟨283613399787949098011468603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189075599858632732007645735 283613399787949098011468603)
  ·
    refine ⟨425420099681923647017202905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283613399787949098011468603 425420099681923647017202905)
    ·
      refine ⟨319065074761442735262902179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425420099681923647017202905 319065074761442735262902179)
      ·
        refine ⟨478597612142164102894353269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319065074761442735262902179 478597612142164102894353269)
        ·
          refine ⟨44868526138327884646345619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 478597612142164102894353269 44868526138327884646345619)
          ·
            refine ⟨67302789207491826969518429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44868526138327884646345619 67302789207491826969518429)
            ·
              refine ⟨25238545952809435113569411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67302789207491826969518429 25238545952809435113569411)
              ·
                refine ⟨37857818929214152670354117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25238545952809435113569411 37857818929214152670354117)
                ·
                  refine ⟨7098341049227653625691397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37857818929214152670354117 7098341049227653625691397)
                  ·
                    refine ⟨1330938946730185054817137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7098341049227653625691397 1330938946730185054817137)
                    ·
                      rfl

theorem cell23_7775983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 4].length) (baseStart_7775983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775983 prefixEnd_7775983 := by exact prefixLift 7775983
  have htrace : WordTrace (prefixWord ++ tailWord_7775983) baseStart_7775983 baseEnd_7775983 := by
    simpa [prefixWord, tailWord_7775983, baseEnd_7775983] using wordTrace_append hprefix tailTrace_7775983
  have hstable : (prefixWord ++ tailWord_7775983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775983).length < 2 ^ (prefixWord ++ tailWord_7775983).sum := by decide
  have hdescent : baseEnd_7775983 < baseStart_7775983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7775996 : List Nat := [2, 2, 2, 1, 3, 1, 2, 10]
def baseStart_7775996 : Nat := 118140960795 + 7775996 * 2 ^ 59
def prefixEnd_7775996 : Nat := 4983230072969 + 3 ^ 40 * 7775996 * 2
def baseEnd_7775996 : Nat := 147882352423669022725513

theorem tailTrace_7775996 : CollatzResearch.WordTrace tailWord_7775996 prefixEnd_7775996 147882352423669022725513 := by
  unfold tailWord_7775996
  simp only [CollatzResearch.WordTrace]
  refine ⟨141806936968451000615845921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189075915957934667487794561 141806936968451000615845921)
  ·
    refine ⟨106355202726338250461884441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141806936968451000615845921 106355202726338250461884441)
    ·
      refine ⟨79766402044753687846413331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106355202726338250461884441 79766402044753687846413331)
      ·
        refine ⟨119649603067130531769619997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79766402044753687846413331 119649603067130531769619997)
        ·
          refine ⟨44868601150173949413607499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119649603067130531769619997 44868601150173949413607499)
          ·
            refine ⟨67302901725260924120411249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44868601150173949413607499 67302901725260924120411249)
            ·
              refine ⟨50477176293945693090308437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67302901725260924120411249 50477176293945693090308437)
              ·
                refine ⟨147882352423669022725513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50477176293945693090308437 147882352423669022725513)
                ·
                  rfl

theorem cell23_7775996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 10].length) (baseStart_7775996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7775996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7775996 prefixEnd_7775996 := by exact prefixLift 7775996
  have htrace : WordTrace (prefixWord ++ tailWord_7775996) baseStart_7775996 baseEnd_7775996 := by
    simpa [prefixWord, tailWord_7775996, baseEnd_7775996] using wordTrace_append hprefix tailTrace_7775996
  have hstable : (prefixWord ++ tailWord_7775996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7775996).length < 2 ^ (prefixWord ++ tailWord_7775996).sum := by decide
  have hdescent : baseEnd_7775996 < baseStart_7775996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7775996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776003 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 4]
def baseStart_7776003 : Nat := 118140960795 + 7776003 * 2 ^ 59
def prefixEnd_7776003 : Nat := 4983230072969 + 3 ^ 40 * 7776003 * 2
def baseEnd_7776003 : Nat := 3992827109803645086201319

theorem tailTrace_7776003 : CollatzResearch.WordTrace tailWord_7776003 prefixEnd_7776003 3992827109803645086201319 := by
  unfold tailWord_7776003
  simp only [CollatzResearch.WordTrace]
  refine ⟨283614129247876641427196663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189076086165251094284797775 283614129247876641427196663)
  ·
    refine ⟨425421193871814962140794995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283614129247876641427196663 425421193871814962140794995)
    ·
      refine ⟨638131790807722443211192493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425421193871814962140794995 638131790807722443211192493)
      ·
        refine ⟨239299421552895916204197185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638131790807722443211192493 239299421552895916204197185)
        ·
          refine ⟨179474566164671937153147889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239299421552895916204197185 179474566164671937153147889)
          ·
            refine ⟨134605924623503952864860917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179474566164671937153147889 134605924623503952864860917)
            ·
              refine ⟨12619305433453495581080711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134605924623503952864860917 12619305433453495581080711)
              ·
                refine ⟨18928958150180243371621067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12619305433453495581080711 18928958150180243371621067)
                ·
                  refine ⟨28393437225270365057431601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18928958150180243371621067 28393437225270365057431601)
                  ·
                    refine ⟨21295077918952773793073701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28393437225270365057431601 21295077918952773793073701)
                    ·
                      refine ⟨3992827109803645086201319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21295077918952773793073701 3992827109803645086201319)
                      ·
                        rfl

theorem cell23_7776003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_7776003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776003 prefixEnd_7776003 := by exact prefixLift 7776003
  have htrace : WordTrace (prefixWord ++ tailWord_7776003) baseStart_7776003 baseEnd_7776003 := by
    simpa [prefixWord, tailWord_7776003, baseEnd_7776003] using wordTrace_append hprefix tailTrace_7776003
  have hstable : (prefixWord ++ tailWord_7776003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776003).length < 2 ^ (prefixWord ++ tailWord_7776003).sum := by decide
  have hdescent : baseEnd_7776003 < baseStart_7776003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776007 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7776007 : Nat := 118140960795 + 7776007 * 2 ^ 59
def prefixEnd_7776007 : Nat := 4983230072969 + 3 ^ 40 * 7776007 * 2
def baseEnd_7776007 : Nat := 3992829163726263070551301

theorem tailTrace_7776007 : CollatzResearch.WordTrace tailWord_7776007 prefixEnd_7776007 3992829163726263070551301 := by
  unfold tailWord_7776007
  simp only [CollatzResearch.WordTrace]
  refine ⟨283614275139862150110342275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189076183426574766740228183 283614275139862150110342275)
  ·
    refine ⟨425421412709793225165513413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283614275139862150110342275 425421412709793225165513413)
    ·
      refine ⟨79766514883086229718533765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425421412709793225165513413 79766514883086229718533765)
      ·
        refine ⟨14956221540578668072225081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79766514883086229718533765 14956221540578668072225081)
        ·
          refine ⟨11217166155434001054168811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14956221540578668072225081 11217166155434001054168811)
          ·
            refine ⟨16825749233151001581253217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11217166155434001054168811 16825749233151001581253217)
            ·
              refine ⟨12619311924863251185939913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16825749233151001581253217 12619311924863251185939913)
              ·
                refine ⟨9464483943647438389454935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12619311924863251185939913 9464483943647438389454935)
                ·
                  refine ⟨14196725915471157584182403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464483943647438389454935 14196725915471157584182403)
                  ·
                    refine ⟨21295088873206736376273605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14196725915471157584182403 21295088873206736376273605)
                    ·
                      refine ⟨3992829163726263070551301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21295088873206736376273605 3992829163726263070551301)
                      ·
                        rfl

theorem cell23_7776007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7776007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776007 prefixEnd_7776007 := by exact prefixLift 7776007
  have htrace : WordTrace (prefixWord ++ tailWord_7776007) baseStart_7776007 baseEnd_7776007 := by
    simpa [prefixWord, tailWord_7776007, baseEnd_7776007] using wordTrace_append hprefix tailTrace_7776007
  have hstable : (prefixWord ++ tailWord_7776007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776007).length < 2 ^ (prefixWord ++ tailWord_7776007).sum := by decide
  have hdescent : baseEnd_7776007 < baseStart_7776007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776010 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_7776010 : Nat := 118140960795 + 7776010 * 2 ^ 59
def prefixEnd_7776010 : Nat := 4983230072969 + 3 ^ 40 * 7776010 * 2
def baseEnd_7776010 : Nat := 3992830704168226558813787

theorem tailTrace_7776010 : CollatzResearch.WordTrace tailWord_7776010 prefixEnd_7776010 3992830704168226558813787 := by
  unfold tailWord_7776010
  simp only [CollatzResearch.WordTrace]
  refine ⟨70903596139712820405675371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189076256372567521081800989 70903596139712820405675371)
  ·
    refine ⟨106355394209569230608513057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70903596139712820405675371 106355394209569230608513057)
    ·
      refine ⟨79766545657176922956384793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106355394209569230608513057 79766545657176922956384793)
      ·
        refine ⟨59824909242882692217288595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79766545657176922956384793 59824909242882692217288595)
        ·
          refine ⟨89737363864324038325932893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59824909242882692217288595 89737363864324038325932893)
          ·
            refine ⟨33651511449121514372224835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89737363864324038325932893 33651511449121514372224835)
            ·
              refine ⟨50477267173682271558337253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33651511449121514372224835 50477267173682271558337253)
              ·
                refine ⟨9464487595065425917188235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50477267173682271558337253 9464487595065425917188235)
                ·
                  refine ⟨14196731392598138875782353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464487595065425917188235 14196731392598138875782353)
                  ·
                    refine ⟨10647548544448604156836765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14196731392598138875782353 10647548544448604156836765)
                    ·
                      refine ⟨3992830704168226558813787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10647548544448604156836765 3992830704168226558813787)
                      ·
                        rfl

theorem cell23_7776010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_7776010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776010 prefixEnd_7776010 := by exact prefixLift 7776010
  have htrace : WordTrace (prefixWord ++ tailWord_7776010) baseStart_7776010 baseEnd_7776010 := by
    simpa [prefixWord, tailWord_7776010, baseEnd_7776010] using wordTrace_append hprefix tailTrace_7776010
  have hstable : (prefixWord ++ tailWord_7776010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776010).length < 2 ^ (prefixWord ++ tailWord_7776010).sum := by decide
  have hdescent : baseEnd_7776010 < baseStart_7776010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776024 : List Nat := [2, 1, 2, 3, 1, 1, 5, 3, 1, 2, 2]
def baseStart_7776024 : Nat := 118140960795 + 7776024 * 2 ^ 59
def prefixEnd_7776024 : Nat := 4983230072969 + 3 ^ 40 * 7776024 * 2
def baseEnd_7776024 : Nat := 3992837892897389504038723

theorem tailTrace_7776024 : CollatzResearch.WordTrace tailWord_7776024 prefixEnd_7776024 3992837892897389504038723 := by
  unfold tailWord_7776024
  simp only [CollatzResearch.WordTrace]
  refine ⟨141807447590400281006855563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189076596787200374675807417 141807447590400281006855563)
  ·
    refine ⟨212711171385600421510283345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141807447590400281006855563 212711171385600421510283345)
    ·
      refine ⟨159533378539200316132712509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212711171385600421510283345 159533378539200316132712509)
      ·
        refine ⟨59825016952200118549767191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159533378539200316132712509 59825016952200118549767191)
        ·
          refine ⟨89737525428300177824650787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59825016952200118549767191 89737525428300177824650787)
          ·
            refine ⟨134606288142450266736976181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89737525428300177824650787 134606288142450266736976181)
            ·
              refine ⟨12619339513354712506591517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134606288142450266736976181 12619339513354712506591517)
              ·
                refine ⟨4732252317508017189971819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12619339513354712506591517 4732252317508017189971819)
                ·
                  refine ⟨7098378476262025784957729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732252317508017189971819 7098378476262025784957729)
                  ·
                    refine ⟨5323783857196519338718297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7098378476262025784957729 5323783857196519338718297)
                    ·
                      refine ⟨3992837892897389504038723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323783857196519338718297 3992837892897389504038723)
                      ·
                        rfl

theorem cell23_7776024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_7776024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776024 prefixEnd_7776024 := by exact prefixLift 7776024
  have htrace : WordTrace (prefixWord ++ tailWord_7776024) baseStart_7776024 baseEnd_7776024 := by
    simpa [prefixWord, tailWord_7776024, baseEnd_7776024] using wordTrace_append hprefix tailTrace_7776024
  have hstable : (prefixWord ++ tailWord_7776024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776024).length < 2 ^ (prefixWord ++ tailWord_7776024).sum := by decide
  have hdescent : baseEnd_7776024 < baseStart_7776024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776067 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 1, 3, 2]
def baseStart_7776067 : Nat := 118140960795 + 7776067 * 2 ^ 59
def prefixEnd_7776067 : Nat := 4983230072969 + 3 ^ 40 * 7776067 * 2
def baseEnd_7776067 : Nat := 3992859972565532835801025

theorem tailTrace_7776067 : CollatzResearch.WordTrace tailWord_7776067 prefixEnd_7776067 3992859972565532835801025 := by
  unfold tailWord_7776067
  simp only [CollatzResearch.WordTrace]
  refine ⟨283616463519644780357526455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189077642346429853571684303 283616463519644780357526455)
  ·
    refine ⟨425424695279467170536289683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283616463519644780357526455 425424695279467170536289683)
    ·
      refine ⟨638137042919200755804434525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425424695279467170536289683 638137042919200755804434525)
      ·
        refine ⟨239301391094700283426662947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638137042919200755804434525 239301391094700283426662947)
        ·
          refine ⟨358952086642050425139994421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239301391094700283426662947 358952086642050425139994421)
          ·
            refine ⟨33651758122692227356874477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358952086642050425139994421 33651758122692227356874477)
            ·
              refine ⟨12619409296009585258827929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33651758122692227356874477 12619409296009585258827929)
              ·
                refine ⟨9464556972007188944120947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12619409296009585258827929 9464556972007188944120947)
                ·
                  refine ⟨14196835458010783416181421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464556972007188944120947 14196835458010783416181421)
                  ·
                    refine ⟨5323813296754043781068033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14196835458010783416181421 5323813296754043781068033)
                    ·
                      refine ⟨3992859972565532835801025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323813296754043781068033 3992859972565532835801025)
                      ·
                        rfl

theorem cell23_7776067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_7776067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776067 prefixEnd_7776067 := by exact prefixLift 7776067
  have htrace : WordTrace (prefixWord ++ tailWord_7776067) baseStart_7776067 baseEnd_7776067 := by
    simpa [prefixWord, tailWord_7776067, baseEnd_7776067] using wordTrace_append hprefix tailTrace_7776067
  have hstable : (prefixWord ++ tailWord_7776067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776067).length < 2 ^ (prefixWord ++ tailWord_7776067).sum := by decide
  have hdescent : baseEnd_7776067 < baseStart_7776067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776103 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 7]
def baseStart_7776103 : Nat := 118140960795 + 7776103 * 2 ^ 59
def prefixEnd_7776103 : Nat := 4983230072969 + 3 ^ 40 * 7776103 * 2
def baseEnd_7776103 : Nat := 443653161985454966105651

theorem tailTrace_7776103 : CollatzResearch.WordTrace tailWord_7776103 prefixEnd_7776103 443653161985454966105651 := by
  unfold tailWord_7776103
  simp only [CollatzResearch.WordTrace]
  refine ⟨283617776547514358505836963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189078517698342905670557975 283617776547514358505836963)
  ·
    refine ⟨425426664821271537758755445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283617776547514358505836963 425426664821271537758755445)
    ·
      refine ⟨39883749826994206664883323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 425426664821271537758755445 39883749826994206664883323)
      ·
        refine ⟨59825624740491309997324985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39883749826994206664883323 59825624740491309997324985)
        ·
          refine ⟨44869218555368482497993739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59825624740491309997324985 44869218555368482497993739)
          ·
            refine ⟨67303827833052723746990609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44869218555368482497993739 67303827833052723746990609)
            ·
              refine ⟨50477870874789542810242957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67303827833052723746990609 50477870874789542810242957)
              ·
                refine ⟨18929201578046078553841109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50477870874789542810242957 18929201578046078553841109)
                ·
                  refine ⟨443653161985454966105651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18929201578046078553841109 443653161985454966105651)
                  ·
                    rfl

theorem cell23_7776103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 7].length) (baseStart_7776103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776103 prefixEnd_7776103 := by exact prefixLift 7776103
  have htrace : WordTrace (prefixWord ++ tailWord_7776103) baseStart_7776103 baseEnd_7776103 := by
    simpa [prefixWord, tailWord_7776103, baseEnd_7776103] using wordTrace_append hprefix tailTrace_7776103
  have hstable : (prefixWord ++ tailWord_7776103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776103).length < 2 ^ (prefixWord ++ tailWord_7776103).sum := by decide
  have hdescent : baseEnd_7776103 < baseStart_7776103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776110 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7776110 : Nat := 118140960795 + 7776110 * 2 ^ 59
def prefixEnd_7776110 : Nat := 4983230072969 + 3 ^ 40 * 7776110 * 2
def baseEnd_7776110 : Nat := 3992882052233676167563327

theorem tailTrace_7776110 : CollatzResearch.WordTrace tailWord_7776110 prefixEnd_7776110 3992882052233676167563327 := by
  unfold tailWord_7776110
  simp only [CollatzResearch.WordTrace]
  refine ⟨35452253982311124837667723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189078687905659332467561189 35452253982311124837667723)
  ·
    refine ⟨53178380973466687256501585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35452253982311124837667723 53178380973466687256501585)
    ·
      refine ⟨39883785730100015442376189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53178380973466687256501585 39883785730100015442376189)
      ·
        refine ⟨14956419648787505790891071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39883785730100015442376189 14956419648787505790891071)
        ·
          refine ⟨22434629473181258686336607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14956419648787505790891071 22434629473181258686336607)
          ·
            refine ⟨33651944209771888029504911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22434629473181258686336607 33651944209771888029504911)
            ·
              refine ⟨50477916314657832044257367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33651944209771888029504911 50477916314657832044257367)
              ·
                refine ⟨75716874471986748066386051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50477916314657832044257367 75716874471986748066386051)
                ·
                  refine ⟨113575311707980122099579077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75716874471986748066386051 113575311707980122099579077)
                  ·
                    refine ⟨21295370945246272893671077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113575311707980122099579077 21295370945246272893671077)
                    ·
                      refine ⟨3992882052233676167563327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21295370945246272893671077 3992882052233676167563327)
                      ·
                        rfl

theorem cell23_7776110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7776110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776110 prefixEnd_7776110 := by exact prefixLift 7776110
  have htrace : WordTrace (prefixWord ++ tailWord_7776110) baseStart_7776110 baseEnd_7776110 := by
    simpa [prefixWord, tailWord_7776110, baseEnd_7776110] using wordTrace_append hprefix tailTrace_7776110
  have hstable : (prefixWord ++ tailWord_7776110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776110).length < 2 ^ (prefixWord ++ tailWord_7776110).sum := by decide
  have hdescent : baseEnd_7776110 < baseStart_7776110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776133 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_7776133 : Nat := 118140960795 + 7776133 * 2 ^ 59
def prefixEnd_7776133 : Nat := 4983230072969 + 3 ^ 40 * 7776133 * 2
def baseEnd_7776133 : Nat := 1330964620762909859191907

theorem tailTrace_7776133 : CollatzResearch.WordTrace tailWord_7776133 prefixEnd_7776133 1330964620762909859191907 := by
  unfold tailWord_7776133
  simp only [CollatzResearch.WordTrace]
  refine ⟨283618870737405673629429053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189079247158270449086286035 283618870737405673629429053)
  ·
    refine ⟨106357076526527127611035895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283618870737405673629429053 106357076526527127611035895)
    ·
      refine ⟨159535614789790691416553843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106357076526527127611035895 159535614789790691416553843)
      ·
        refine ⟨239303422184686037124830765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159535614789790691416553843 239303422184686037124830765)
        ·
          refine ⟨89738783319257263921811537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239303422184686037124830765 89738783319257263921811537)
          ·
            refine ⟨67304087489442947941358653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89738783319257263921811537 67304087489442947941358653)
            ·
              refine ⟨25239032808541105478009495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67304087489442947941358653 25239032808541105478009495)
              ·
                refine ⟨37858549212811658217014243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25239032808541105478009495 37858549212811658217014243)
                ·
                  refine ⟨56787823819217487325521365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37858549212811658217014243 56787823819217487325521365)
                  ·
                    refine ⟨1330964620762909859191907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56787823819217487325521365 1330964620762909859191907)
                    ·
                      rfl

theorem cell23_7776133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_7776133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776133 prefixEnd_7776133 := by exact prefixLift 7776133
  have htrace : WordTrace (prefixWord ++ tailWord_7776133) baseStart_7776133 baseEnd_7776133 := by
    simpa [prefixWord, tailWord_7776133, baseEnd_7776133] using wordTrace_append hprefix tailTrace_7776133
  have hstable : (prefixWord ++ tailWord_7776133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776133).length < 2 ^ (prefixWord ++ tailWord_7776133).sum := by decide
  have hdescent : baseEnd_7776133 < baseStart_7776133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776183 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_7776183 : Nat := 118140960795 + 7776183 * 2 ^ 59
def prefixEnd_7776183 : Nat := 4983230072969 + 3 ^ 40 * 7776183 * 2
def baseEnd_7776183 : Nat := 3992919536321454381950491

theorem tailTrace_7776183 : CollatzResearch.WordTrace tailWord_7776183 prefixEnd_7776183 3992919536321454381950491 := by
  unfold tailWord_7776183
  simp only [CollatzResearch.WordTrace]
  refine ⟨283620694387224532168749203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189080462924816354779166135 283620694387224532168749203)
  ·
    refine ⟨425431041580836798253123805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283620694387224532168749203 425431041580836798253123805)
    ·
      refine ⟨159536640592813799344921427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425431041580836798253123805 159536640592813799344921427)
      ·
        refine ⟨239304960889220699017382141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159536640592813799344921427 239304960889220699017382141)
        ·
          refine ⟨89739360333457762131518303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239304960889220699017382141 89739360333457762131518303)
          ·
            refine ⟨134609040500186643197277455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89739360333457762131518303 134609040500186643197277455)
            ·
              refine ⟨201913560750279964795916183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134609040500186643197277455 201913560750279964795916183)
              ·
                refine ⟨302870341125419947193874275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201913560750279964795916183 302870341125419947193874275)
                ·
                  refine ⟨454305511688129920790811413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302870341125419947193874275 454305511688129920790811413)
                  ·
                    refine ⟨21295570860381090037069285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 454305511688129920790811413 21295570860381090037069285)
                    ·
                      refine ⟨3992919536321454381950491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21295570860381090037069285 3992919536321454381950491)
                      ·
                        rfl

theorem cell23_7776183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_7776183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776183 prefixEnd_7776183 := by exact prefixLift 7776183
  have htrace : WordTrace (prefixWord ++ tailWord_7776183) baseStart_7776183 baseEnd_7776183 := by
    simpa [prefixWord, tailWord_7776183, baseEnd_7776183] using wordTrace_append hprefix tailTrace_7776183
  have hstable : (prefixWord ++ tailWord_7776183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776183).length < 2 ^ (prefixWord ++ tailWord_7776183).sum := by decide
  have hdescent : baseEnd_7776183 < baseStart_7776183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776197 : List Nat := [1, 3, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_7776197 : Nat := 118140960795 + 7776197 * 2 ^ 59
def prefixEnd_7776197 : Nat := 4983230072969 + 3 ^ 40 * 7776197 * 2
def baseEnd_7776197 : Nat := 1330975575016872442391809

theorem tailTrace_7776197 : CollatzResearch.WordTrace tailWord_7776197 prefixEnd_7776197 1330975575016872442391809 := by
  unfold tailWord_7776197
  simp only [CollatzResearch.WordTrace]
  refine ⟨283621205009173812559758845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189080803339449208373172563 283621205009173812559758845)
  ·
    refine ⟨106357951878440179709909567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283621205009173812559758845 106357951878440179709909567)
    ·
      refine ⟨159536927817660269564864351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106357951878440179709909567 159536927817660269564864351)
      ·
        refine ⟨239305391726490404347296527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159536927817660269564864351 239305391726490404347296527)
        ·
          refine ⟨358958087589735606520944791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239305391726490404347296527 358958087589735606520944791)
          ·
            refine ⟨538437131384603409781417187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358958087589735606520944791 538437131384603409781417187)
            ·
              refine ⟨807655697076905114672125781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538437131384603409781417187 807655697076905114672125781)
              ·
                refine ⟨4732357600059990906281987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 807655697076905114672125781 4732357600059990906281987)
                ·
                  refine ⟨7098536400089986359422981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732357600059990906281987 7098536400089986359422981)
                  ·
                    refine ⟨1330975575016872442391809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7098536400089986359422981 1330975575016872442391809)
                    ·
                      rfl

theorem cell23_7776197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_7776197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776197 prefixEnd_7776197 := by exact prefixLift 7776197
  have htrace : WordTrace (prefixWord ++ tailWord_7776197) baseStart_7776197 baseEnd_7776197 := by
    simpa [prefixWord, tailWord_7776197, baseEnd_7776197] using wordTrace_append hprefix tailTrace_7776197
  have hstable : (prefixWord ++ tailWord_7776197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776197).length < 2 ^ (prefixWord ++ tailWord_7776197).sum := by decide
  have hdescent : baseEnd_7776197 < baseStart_7776197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776227 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 6]
def baseStart_7776227 : Nat := 118140960795 + 7776227 * 2 ^ 59
def prefixEnd_7776227 : Nat := 4983230072969 + 3 ^ 40 * 7776227 * 2
def baseEnd_7776227 : Nat := 443660236607805801088921

theorem tailTrace_7776227 : CollatzResearch.WordTrace tailWord_7776227 prefixEnd_7776227 443660236607805801088921 := by
  unfold tailWord_7776227
  simp only [CollatzResearch.WordTrace]
  refine ⟨283622299199065127683350935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189081532799376751788900623 283622299199065127683350935)
  ·
    refine ⟨425433448798597691525026403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283622299199065127683350935 425433448798597691525026403)
    ·
      refine ⟨638150173197896537287539605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425433448798597691525026403 638150173197896537287539605)
      ·
        refine ⟨29913289368651400185353419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 638150173197896537287539605 29913289368651400185353419)
        ·
          refine ⟨44869934052977100278030129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29913289368651400185353419 44869934052977100278030129)
          ·
            refine ⟨33652450539732825208522597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44869934052977100278030129 33652450539732825208522597)
            ·
              refine ⟨6309834476199904726597987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33652450539732825208522597 6309834476199904726597987)
              ·
                refine ⟨9464751714299857089896981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309834476199904726597987 9464751714299857089896981)
                ·
                  refine ⟨443660236607805801088921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9464751714299857089896981 443660236607805801088921)
                  ·
                    rfl

theorem cell23_7776227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 6].length) (baseStart_7776227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776227 prefixEnd_7776227 := by exact prefixLift 7776227
  have htrace : WordTrace (prefixWord ++ tailWord_7776227) baseStart_7776227 baseEnd_7776227 := by
    simpa [prefixWord, tailWord_7776227, baseEnd_7776227] using wordTrace_append hprefix tailTrace_7776227
  have hstable : (prefixWord ++ tailWord_7776227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776227).length < 2 ^ (prefixWord ++ tailWord_7776227).sum := by decide
  have hdescent : baseEnd_7776227 < baseStart_7776227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776270 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_7776270 : Nat := 118140960795 + 7776270 * 2 ^ 59
def prefixEnd_7776270 : Nat := 4983230072969 + 3 ^ 40 * 7776270 * 2
def baseEnd_7776270 : Nat := 1330988069712798513854197

theorem tailTrace_7776270 : CollatzResearch.WordTrace tailWord_7776270 prefixEnd_7776270 1330988069712798513854197 := by
  unfold tailWord_7776270
  simp only [CollatzResearch.WordTrace]
  refine ⟨35452983442238668253395783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189082578358606230684777509 35452983442238668253395783)
  ·
    refine ⟨53179475163358002380093675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35452983442238668253395783 53179475163358002380093675)
    ·
      refine ⟨79769212745037003570140513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53179475163358002380093675 79769212745037003570140513)
      ·
        refine ⟨59826909558777752677605385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79769212745037003570140513 59826909558777752677605385)
        ·
          refine ⟨44870182169083314508204039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59826909558777752677605385 44870182169083314508204039)
          ·
            refine ⟨67305273253624971762306059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44870182169083314508204039 67305273253624971762306059)
            ·
              refine ⟨100957909880437457643459089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67305273253624971762306059 100957909880437457643459089)
              ·
                refine ⟨75718432410328093232594317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100957909880437457643459089 75718432410328093232594317)
                ·
                  refine ⟨28394412153873034962222869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75718432410328093232594317 28394412153873034962222869)
                  ·
                    refine ⟨1330988069712798513854197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28394412153873034962222869 1330988069712798513854197)
                    ·
                      rfl

theorem cell23_7776270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_7776270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776270 prefixEnd_7776270 := by exact prefixLift 7776270
  have htrace : WordTrace (prefixWord ++ tailWord_7776270) baseStart_7776270 baseEnd_7776270 := by
    simpa [prefixWord, tailWord_7776270, baseEnd_7776270] using wordTrace_append hprefix tailTrace_7776270
  have hstable : (prefixWord ++ tailWord_7776270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776270).length < 2 ^ (prefixWord ++ tailWord_7776270).sum := by decide
  have hdescent : baseEnd_7776270 < baseStart_7776270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776280 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_7776280 : Nat := 118140960795 + 7776280 * 2 ^ 59
def prefixEnd_7776280 : Nat := 4983230072969 + 3 ^ 40 * 7776280 * 2
def baseEnd_7776280 : Nat := 3992969343944940502437545

theorem tailTrace_7776280 : CollatzResearch.WordTrace tailWord_7776280 prefixEnd_7776280 3992969343944940502437545 := by
  unfold tailWord_7776280
  simp only [CollatzResearch.WordTrace]
  refine ⟨141812116133936558867515147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189082821511915411823353529 141812116133936558867515147)
  ·
    refine ⟨212718174200904838301272721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141812116133936558867515147 212718174200904838301272721)
    ·
      refine ⟨159538630650678628725954541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212718174200904838301272721 159538630650678628725954541)
      ·
        refine ⟨59826986494004485772232953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159538630650678628725954541 59826986494004485772232953)
        ·
          refine ⟨44870239870503364329174715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59826986494004485772232953 44870239870503364329174715)
          ·
            refine ⟨67305359805755046493762073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44870239870503364329174715 67305359805755046493762073)
            ·
              refine ⟨50479019854316284870321555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67305359805755046493762073 50479019854316284870321555)
              ·
                refine ⟨75718529781474427305482333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50479019854316284870321555 75718529781474427305482333)
                ·
                  refine ⟨28394448668052910239555875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75718529781474427305482333 28394448668052910239555875)
                  ·
                    refine ⟨42591673002079365359333813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28394448668052910239555875 42591673002079365359333813)
                    ·
                      refine ⟨3992969343944940502437545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42591673002079365359333813 3992969343944940502437545)
                      ·
                        rfl

theorem cell23_7776280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_7776280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776280 prefixEnd_7776280 := by exact prefixLift 7776280
  have htrace : WordTrace (prefixWord ++ tailWord_7776280) baseStart_7776280 baseEnd_7776280 := by
    simpa [prefixWord, tailWord_7776280, baseEnd_7776280] using wordTrace_append hprefix tailTrace_7776280
  have hstable : (prefixWord ++ tailWord_7776280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776280).length < 2 ^ (prefixWord ++ tailWord_7776280).sum := by decide
  have hdescent : baseEnd_7776280 < baseStart_7776280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776283 : List Nat := [1, 1, 1, 1, 1, 1, 3, 14]
def baseStart_7776283 : Nat := 118140960795 + 7776283 * 2 ^ 59
def prefixEnd_7776283 : Nat := 4983230072969 + 3 ^ 40 * 7776283 * 2
def baseEnd_7776283 : Nat := 147887810532848295951853

theorem tailTrace_7776283 : CollatzResearch.WordTrace tailWord_7776283 prefixEnd_7776283 147887810532848295951853 := by
  unfold tailWord_7776283
  simp only [CollatzResearch.WordTrace]
  refine ⟨283624341686862249247389503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189082894457908166164926335 283624341686862249247389503)
  ·
    refine ⟨425436512530293373871084255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283624341686862249247389503 425436512530293373871084255)
    ·
      refine ⟨638154768795440060806626383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425436512530293373871084255 638154768795440060806626383)
      ·
        refine ⟨957232153193160091209939575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638154768795440060806626383 957232153193160091209939575)
        ·
          refine ⟨1435848229789740136814909363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957232153193160091209939575 1435848229789740136814909363)
          ·
            refine ⟨2153772344684610205222364045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435848229789740136814909363 2153772344684610205222364045)
            ·
              refine ⟨807664629256728826958386517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2153772344684610205222364045 807664629256728826958386517)
              ·
                refine ⟨147887810532848295951853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 807664629256728826958386517 147887810532848295951853)
                ·
                  rfl

theorem cell23_7776283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 14].length) (baseStart_7776283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776283 prefixEnd_7776283 := by exact prefixLift 7776283
  have htrace : WordTrace (prefixWord ++ tailWord_7776283) baseStart_7776283 baseEnd_7776283 := by
    simpa [prefixWord, tailWord_7776283, baseEnd_7776283] using wordTrace_append hprefix tailTrace_7776283
  have hstable : (prefixWord ++ tailWord_7776283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776283).length < 2 ^ (prefixWord ++ tailWord_7776283).sum := by decide
  have hdescent : baseEnd_7776283 < baseStart_7776283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776287 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 2, 4]
def baseStart_7776287 : Nat := 118140960795 + 7776287 * 2 ^ 59
def prefixEnd_7776287 : Nat := 4983230072969 + 3 ^ 40 * 7776287 * 2
def baseEnd_7776287 : Nat := 1330990979436507325016671

theorem tailTrace_7776287 : CollatzResearch.WordTrace tailWord_7776287 prefixEnd_7776287 1330990979436507325016671 := by
  unfold tailWord_7776287
  simp only [CollatzResearch.WordTrace]
  refine ⟨283624487578847757930535115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189082991719231838620356743 283624487578847757930535115)
  ·
    refine ⟨425436731368271636895802673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283624487578847757930535115 425436731368271636895802673)
    ·
      refine ⟨319077548526203727671852005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425436731368271636895802673 319077548526203727671852005)
      ·
        refine ⟨59827040348663198938472251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319077548526203727671852005 59827040348663198938472251)
        ·
          refine ⟨89740560522994798407708377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59827040348663198938472251 89740560522994798407708377)
          ·
            refine ⟨67305420392246098805781283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89740560522994798407708377 67305420392246098805781283)
            ·
              refine ⟨100958130588369148208671925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67305420392246098805781283 100958130588369148208671925)
              ·
                refine ⟨9464824742659607644562993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100958130588369148208671925 9464824742659607644562993)
                ·
                  refine ⟨7098618556994705733422245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9464824742659607644562993 7098618556994705733422245)
                  ·
                    refine ⟨1330990979436507325016671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7098618556994705733422245 1330990979436507325016671)
                    ·
                      rfl

theorem cell23_7776287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 4].length) (baseStart_7776287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776287 prefixEnd_7776287 := by exact prefixLift 7776287
  have htrace : WordTrace (prefixWord ++ tailWord_7776287) baseStart_7776287 baseEnd_7776287 := by
    simpa [prefixWord, tailWord_7776287, baseEnd_7776287] using wordTrace_append hprefix tailTrace_7776287
  have hstable : (prefixWord ++ tailWord_7776287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776287).length < 2 ^ (prefixWord ++ tailWord_7776287).sum := by decide
  have hdescent : baseEnd_7776287 < baseStart_7776287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776308 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_7776308 : Nat := 118140960795 + 7776308 * 2 ^ 59
def prefixEnd_7776308 : Nat := 4983230072969 + 3 ^ 40 * 7776308 * 2
def baseEnd_7776308 : Nat := 1330994573801088797629139

theorem tailTrace_7776308 : CollatzResearch.WordTrace tailWord_7776308 prefixEnd_7776308 1330994573801088797629139 := by
  unfold tailWord_7776308
  simp only [CollatzResearch.WordTrace]
  refine ⟨141812626755885839258524789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189083502341181119011366385 141812626755885839258524789)
  ·
    refine ⟨13294933758364297430486699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141812626755885839258524789 13294933758364297430486699)
    ·
      refine ⟨19942400637546446145730049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13294933758364297430486699 19942400637546446145730049)
      ·
        refine ⟨14956800478159834609297537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19942400637546446145730049 14956800478159834609297537)
        ·
          refine ⟨11217600358619875956973153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14956800478159834609297537 11217600358619875956973153)
          ·
            refine ⟨8413200268964906967729865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11217600358619875956973153 8413200268964906967729865)
            ·
              refine ⟨6309900201723680225797399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8413200268964906967729865 6309900201723680225797399)
              ·
                refine ⟨9464850302585520338696099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309900201723680225797399 9464850302585520338696099)
                ·
                  refine ⟨14197275453878280508044149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464850302585520338696099 14197275453878280508044149)
                  ·
                    refine ⟨1330994573801088797629139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14197275453878280508044149 1330994573801088797629139)
                    ·
                      rfl

theorem cell23_7776308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_7776308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776308 prefixEnd_7776308 := by exact prefixLift 7776308
  have htrace : WordTrace (prefixWord ++ tailWord_7776308) baseStart_7776308 baseEnd_7776308 := by
    simpa [prefixWord, tailWord_7776308, baseEnd_7776308] using wordTrace_append hprefix tailTrace_7776308
  have hstable : (prefixWord ++ tailWord_7776308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776308).length < 2 ^ (prefixWord ++ tailWord_7776308).sum := by decide
  have hdescent : baseEnd_7776308 < baseStart_7776308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776311 : List Nat := [1, 1, 3, 1, 2, 2, 3, 5, 1, 2, 2]
def baseStart_7776311 : Nat := 118140960795 + 7776311 * 2 ^ 59
def prefixEnd_7776311 : Nat := 4983230072969 + 3 ^ 40 * 7776311 * 2
def baseEnd_7776311 : Nat := 3992985261845229881149903

theorem tailTrace_7776311 : CollatzResearch.WordTrace tailWord_7776311 prefixEnd_7776311 3992985261845229881149903 := by
  unfold tailWord_7776311
  simp only [CollatzResearch.WordTrace]
  refine ⟨283625362930760810029408787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189083575287173873352939191 283625362930760810029408787)
  ·
    refine ⟨425438044396141215044113181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283625362930760810029408787 425438044396141215044113181)
    ·
      refine ⟨159539266648552955641542443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425438044396141215044113181 159539266648552955641542443)
      ·
        refine ⟨239308899972829433462313665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159539266648552955641542443 239308899972829433462313665)
        ·
          refine ⟨179481674979622075096735249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239308899972829433462313665 179481674979622075096735249)
          ·
            refine ⟨134611256234716556322551437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179481674979622075096735249 134611256234716556322551437)
            ·
              refine ⟨50479221088018708620956789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134611256234716556322551437 50479221088018708620956789)
              ·
                refine ⟨4732426977001753933214699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50479221088018708620956789 4732426977001753933214699)
                ·
                  refine ⟨7098640465502630899822049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732426977001753933214699 7098640465502630899822049)
                  ·
                    refine ⟨5323980349126973174866537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7098640465502630899822049 5323980349126973174866537)
                    ·
                      refine ⟨3992985261845229881149903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5323980349126973174866537 3992985261845229881149903)
                      ·
                        rfl

theorem cell23_7776311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_7776311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776311 prefixEnd_7776311 := by exact prefixLift 7776311
  have htrace : WordTrace (prefixWord ++ tailWord_7776311) baseStart_7776311 baseEnd_7776311 := by
    simpa [prefixWord, tailWord_7776311, baseEnd_7776311] using wordTrace_append hprefix tailTrace_7776311
  have hstable : (prefixWord ++ tailWord_7776311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776311).length < 2 ^ (prefixWord ++ tailWord_7776311).sum := by decide
  have hdescent : baseEnd_7776311 < baseStart_7776311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776321 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7776321 : Nat := 118140960795 + 7776321 * 2 ^ 59
def prefixEnd_7776321 : Nat := 4983230072969 + 3 ^ 40 * 7776321 * 2
def baseEnd_7776321 : Nat := 1330996798883924947341619

theorem tailTrace_7776321 : CollatzResearch.WordTrace tailWord_7776321 prefixEnd_7776321 1330996798883924947341619 := by
  unfold tailWord_7776321
  simp only [CollatzResearch.WordTrace]
  refine ⟨283625727660724581737272817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189083818440483054491515211 283625727660724581737272817)
  ·
    refine ⟨212719295745543436302954613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283625727660724581737272817 212719295745543436302954613)
    ·
      refine ⟨19942433976144697153401995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212719295745543436302954613 19942433976144697153401995)
      ·
        refine ⟨29913650964217045730102993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19942433976144697153401995 29913650964217045730102993)
        ·
          refine ⟨22435238223162784297577245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29913650964217045730102993 22435238223162784297577245)
          ·
            refine ⟨8413214333686044111591467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22435238223162784297577245 8413214333686044111591467)
            ·
              refine ⟨12619821500529066167387201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413214333686044111591467 12619821500529066167387201)
              ·
                refine ⟨9464866125396799625540401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12619821500529066167387201 9464866125396799625540401)
                ·
                  refine ⟨7098649594047599719155301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9464866125396799625540401 7098649594047599719155301)
                  ·
                    refine ⟨1330996798883924947341619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7098649594047599719155301 1330996798883924947341619)
                    ·
                      rfl

theorem cell23_7776321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7776321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776321 prefixEnd_7776321 := by exact prefixLift 7776321
  have htrace : WordTrace (prefixWord ++ tailWord_7776321) baseStart_7776321 baseEnd_7776321 := by
    simpa [prefixWord, tailWord_7776321, baseEnd_7776321] using wordTrace_append hprefix tailTrace_7776321
  have hstable : (prefixWord ++ tailWord_7776321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776321).length < 2 ^ (prefixWord ++ tailWord_7776321).sum := by decide
  have hdescent : baseEnd_7776321 < baseStart_7776321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776344 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_7776344 : Nat := 118140960795 + 7776344 * 2 ^ 59
def prefixEnd_7776344 : Nat := 4983230072969 + 3 ^ 40 * 7776344 * 2
def baseEnd_7776344 : Nat := 3993002206706828252037251

theorem tailTrace_7776344 : CollatzResearch.WordTrace tailWord_7776344 prefixEnd_7776344 3993002206706828252037251 := by
  unfold tailWord_7776344
  simp only [CollatzResearch.WordTrace]
  refine ⟨141813283269820628332680043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189084377693094171110240057 141813283269820628332680043)
  ·
    refine ⟨212719924904730942499020065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141813283269820628332680043 212719924904730942499020065)
    ·
      refine ⟨159539943678548206874265049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212719924904730942499020065 159539943678548206874265049)
      ·
        refine ⟨119654957758911155155698787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159539943678548206874265049 119654957758911155155698787)
        ·
          refine ⟨179482436638366732733548181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119654957758911155155698787 179482436638366732733548181)
          ·
            refine ⟨8413239217423440596885071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179482436638366732733548181 8413239217423440596885071)
            ·
              refine ⟨12619858826135160895327607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413239217423440596885071 12619858826135160895327607)
              ·
                refine ⟨18929788239202741342991411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12619858826135160895327607 18929788239202741342991411)
                ·
                  refine ⟨28394682358804112014487117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18929788239202741342991411 28394682358804112014487117)
                  ·
                    refine ⟨10648005884551542005432669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28394682358804112014487117 10648005884551542005432669)
                    ·
                      refine ⟨3993002206706828252037251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10648005884551542005432669 3993002206706828252037251)
                      ·
                        rfl

theorem cell23_7776344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_7776344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776344 prefixEnd_7776344 := by exact prefixLift 7776344
  have htrace : WordTrace (prefixWord ++ tailWord_7776344) baseStart_7776344 baseEnd_7776344 := by
    simpa [prefixWord, tailWord_7776344, baseEnd_7776344] using wordTrace_append hprefix tailTrace_7776344
  have hstable : (prefixWord ++ tailWord_7776344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776344).length < 2 ^ (prefixWord ++ tailWord_7776344).sum := by decide
  have hdescent : baseEnd_7776344 < baseStart_7776344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776362 : List Nat := [3, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_7776362 : Nat := 118140960795 + 7776362 * 2 ^ 59
def prefixEnd_7776362 : Nat := 4983230072969 + 3 ^ 40 * 7776362 * 2
def baseEnd_7776362 : Nat := 3993011449358609181612169

theorem tailTrace_7776362 : CollatzResearch.WordTrace tailWord_7776362 prefixEnd_7776362 3993011449358609181612169 := by
  unfold tailWord_7776362
  simp only [CollatzResearch.WordTrace]
  refine ⟨70906805763394011434878835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189084815369050697159676893 70906805763394011434878835)
  ·
    refine ⟨106360208645091017152318253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70906805763394011434878835 106360208645091017152318253)
    ·
      refine ⟨39885078241909131432119345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106360208645091017152318253 39885078241909131432119345)
      ·
        refine ⟨29913808681431848574089509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39885078241909131432119345 29913808681431848574089509)
        ·
          refine ⟨5608839127768471607641783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29913808681431848574089509 5608839127768471607641783)
          ·
            refine ⟨8413258691652707411462675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608839127768471607641783 8413258691652707411462675)
            ·
              refine ⟨12619888037479061117194013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413258691652707411462675 12619888037479061117194013)
              ·
                refine ⟨4732458014054647918947755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12619888037479061117194013 4732458014054647918947755)
                ·
                  refine ⟨7098687021081971878421633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732458014054647918947755 7098687021081971878421633)
                  ·
                    refine ⟨5324015265811478908816225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7098687021081971878421633 5324015265811478908816225)
                    ·
                      refine ⟨3993011449358609181612169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324015265811478908816225 3993011449358609181612169)
                      ·
                        rfl

theorem cell23_7776362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_7776362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776362 prefixEnd_7776362 := by exact prefixLift 7776362
  have htrace : WordTrace (prefixWord ++ tailWord_7776362) baseStart_7776362 baseEnd_7776362 := by
    simpa [prefixWord, tailWord_7776362, baseEnd_7776362] using wordTrace_append hprefix tailTrace_7776362
  have hstable : (prefixWord ++ tailWord_7776362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776362).length < 2 ^ (prefixWord ++ tailWord_7776362).sum := by decide
  have hdescent : baseEnd_7776362 < baseStart_7776362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776474 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_7776474 : Nat := 118140960795 + 7776474 * 2 ^ 59
def prefixEnd_7776474 : Nat := 4983230072969 + 3 ^ 40 * 7776474 * 2
def baseEnd_7776474 : Nat := 3993068959191912743411653

theorem tailTrace_7776474 : CollatzResearch.WordTrace tailWord_7776474 prefixEnd_7776474 3993068959191912743411653 := by
  unfold tailWord_7776474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70907827007292572216898119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189087538686113525911728317 70907827007292572216898119)
  ·
    refine ⟨106361740510938858325347179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70907827007292572216898119 106361740510938858325347179)
    ·
      refine ⟨159542610766408287488020769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106361740510938858325347179 159542610766408287488020769)
      ·
        refine ⟨119656958074806215616015577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159542610766408287488020769 119656958074806215616015577)
        ·
          refine ⟨89742718556104661712011683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119656958074806215616015577 89742718556104661712011683)
          ·
            refine ⟨134614077834156992568017525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89742718556104661712011683 134614077834156992568017525)
            ·
              refine ⟨12620069796952218053251643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134614077834156992568017525 12620069796952218053251643)
              ·
                refine ⟨18930104695428327079877465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12620069796952218053251643 18930104695428327079877465)
                ·
                  refine ⟨14197578521571245309908099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18930104695428327079877465 14197578521571245309908099)
                  ·
                    refine ⟨21296367782356867964862149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14197578521571245309908099 21296367782356867964862149)
                    ·
                      refine ⟨3993068959191912743411653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21296367782356867964862149 3993068959191912743411653)
                      ·
                        rfl

theorem cell23_7776474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_7776474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776474 prefixEnd_7776474 := by exact prefixLift 7776474
  have htrace : WordTrace (prefixWord ++ tailWord_7776474) baseStart_7776474 baseEnd_7776474 := by
    simpa [prefixWord, tailWord_7776474, baseEnd_7776474] using wordTrace_append hprefix tailTrace_7776474
  have hstable : (prefixWord ++ tailWord_7776474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776474).length < 2 ^ (prefixWord ++ tailWord_7776474).sum := by decide
  have hdescent : baseEnd_7776474 < baseStart_7776474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776494 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_7776494 : Nat := 118140960795 + 7776494 * 2 ^ 59
def prefixEnd_7776494 : Nat := 4983230072969 + 3 ^ 40 * 7776494 * 2
def baseEnd_7776494 : Nat := 3993079228805002665161561

theorem tailTrace_7776494 : CollatzResearch.WordTrace tailWord_7776494 prefixEnd_7776494 3993079228805002665161561 := by
  unfold tailWord_7776494
  simp only [CollatzResearch.WordTrace]
  refine ⟨35454004686137229035415067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189088024992731888188880357 35454004686137229035415067)
  ·
    refine ⟨53181007029205843553122601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35454004686137229035415067 53181007029205843553122601)
    ·
      refine ⟨39885755271904382664841951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53181007029205843553122601 39885755271904382664841951)
      ·
        refine ⟨59828632907856573997262927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39885755271904382664841951 59828632907856573997262927)
        ·
          refine ⟨89742949361784860995894391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59828632907856573997262927 89742949361784860995894391)
          ·
            refine ⟨134614424042677291493841587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89742949361784860995894391 134614424042677291493841587)
            ·
              refine ⟨201921636064015937240762381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134614424042677291493841587 201921636064015937240762381)
              ·
                refine ⟨75720613524005976465285893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201921636064015937240762381 75720613524005976465285893)
                ·
                  refine ⟨14197615035751120587241105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75720613524005976465285893 14197615035751120587241105)
                  ·
                    refine ⟨10648211276813340440430829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14197615035751120587241105 10648211276813340440430829)
                    ·
                      refine ⟨3993079228805002665161561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10648211276813340440430829 3993079228805002665161561)
                      ·
                        rfl

theorem cell23_7776494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_7776494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776494 prefixEnd_7776494 := by exact prefixLift 7776494
  have htrace : WordTrace (prefixWord ++ tailWord_7776494) baseStart_7776494 baseEnd_7776494 := by
    simpa [prefixWord, tailWord_7776494, baseEnd_7776494] using wordTrace_append hprefix tailTrace_7776494
  have hstable : (prefixWord ++ tailWord_7776494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776494).length < 2 ^ (prefixWord ++ tailWord_7776494).sum := by decide
  have hdescent : baseEnd_7776494 < baseStart_7776494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776527 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 3, 5]
def baseStart_7776527 : Nat := 118140960795 + 7776527 * 2 ^ 59
def prefixEnd_7776527 : Nat := 4983230072969 + 3 ^ 40 * 7776527 * 2
def baseEnd_7776527 : Nat := 1331032057888867012016303

theorem tailTrace_7776527 : CollatzResearch.WordTrace tailWord_7776527 prefixEnd_7776527 1331032057888867012016303 := by
  unfold tailWord_7776527
  simp only [CollatzResearch.WordTrace]
  refine ⟨283633241097978278919271835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189088827398652185946181223 283633241097978278919271835)
  ·
    refine ⟨425449861646967418378907753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283633241097978278919271835 425449861646967418378907753)
    ·
      refine ⟨319087396235225563784180815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425449861646967418378907753 319087396235225563784180815)
      ·
        refine ⟨478631094352838345676271223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319087396235225563784180815 478631094352838345676271223)
        ·
          refine ⟨717946641529257518514406835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478631094352838345676271223 717946641529257518514406835)
          ·
            refine ⟨1076919962293886277771610253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717946641529257518514406835 1076919962293886277771610253)
            ·
              refine ⟨403844985860207354164353845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076919962293886277771610253 403844985860207354164353845)
              ·
                refine ⟨37860467424394439452908173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 403844985860207354164353845 37860467424394439452908173)
                ·
                  refine ⟨14197675284147914794840565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37860467424394439452908173 14197675284147914794840565)
                  ·
                    refine ⟨1331032057888867012016303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14197675284147914794840565 1331032057888867012016303)
                    ·
                      rfl

theorem cell23_7776527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_7776527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776527 prefixEnd_7776527 := by exact prefixLift 7776527
  have htrace : WordTrace (prefixWord ++ tailWord_7776527) baseStart_7776527 baseEnd_7776527 := by
    simpa [prefixWord, tailWord_7776527, baseEnd_7776527] using wordTrace_append hprefix tailTrace_7776527
  have hstable : (prefixWord ++ tailWord_7776527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776527).length < 2 ^ (prefixWord ++ tailWord_7776527).sum := by decide
  have hdescent : baseEnd_7776527 < baseStart_7776527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776594 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_7776594 : Nat := 118140960795 + 7776594 * 2 ^ 59
def prefixEnd_7776594 : Nat := 4983230072969 + 3 ^ 40 * 7776594 * 2
def baseEnd_7776594 : Nat := 3993130576870452273911101

theorem tailTrace_7776594 : CollatzResearch.WordTrace tailWord_7776594 prefixEnd_7776594 3993130576870452273911101 := by
  unfold tailWord_7776594
  simp only [CollatzResearch.WordTrace]
  refine ⟨70908921197183887340490209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189090456525823699574640557 70908921197183887340490209)
  ·
    refine ⟨53181690897887915505367657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70908921197183887340490209 53181690897887915505367657)
    ·
      refine ⟨39886268173415936629025743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53181690897887915505367657 39886268173415936629025743)
      ·
        refine ⟨59829402260123904943538615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39886268173415936629025743 59829402260123904943538615)
        ·
          refine ⟨89744103390185857415307923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59829402260123904943538615 89744103390185857415307923)
          ·
            refine ⟨134616155085278786122961885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89744103390185857415307923 134616155085278786122961885)
            ·
              refine ⟨50481058156979544796110707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134616155085278786122961885 50481058156979544796110707)
              ·
                refine ⟨75721587235469317194166061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50481058156979544796110707 75721587235469317194166061)
                ·
                  refine ⟨28395595213300993947812273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75721587235469317194166061 28395595213300993947812273)
                  ·
                    refine ⟨21296696409975745460859205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28395595213300993947812273 21296696409975745460859205)
                    ·
                      refine ⟨3993130576870452273911101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21296696409975745460859205 3993130576870452273911101)
                      ·
                        rfl

theorem cell23_7776594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_7776594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776594 prefixEnd_7776594 := by exact prefixLift 7776594
  have htrace : WordTrace (prefixWord ++ tailWord_7776594) baseStart_7776594 baseEnd_7776594 := by
    simpa [prefixWord, tailWord_7776594, baseEnd_7776594] using wordTrace_append hprefix tailTrace_7776594
  have hstable : (prefixWord ++ tailWord_7776594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776594).length < 2 ^ (prefixWord ++ tailWord_7776594).sum := by decide
  have hdescent : baseEnd_7776594 < baseStart_7776594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776604 : List Nat := [2, 2, 4, 3, 12]
def baseStart_7776604 : Nat := 118140960795 + 7776604 * 2 ^ 59
def prefixEnd_7776604 : Nat := 4983230072969 + 3 ^ 40 * 7776604 * 2
def baseEnd_7776604 : Nat := 5477552416566525699295

theorem tailTrace_7776604 : CollatzResearch.WordTrace tailWord_7776604 prefixEnd_7776604 5477552416566525699295 := by
  unfold tailWord_7776604
  simp only [CollatzResearch.WordTrace]
  refine ⟨141818024759349660534912433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189090699679132880713216577 141818024759349660534912433)
  ·
    refine ⟨106363518569512245401184325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141818024759349660534912433 106363518569512245401184325)
    ·
      refine ⟨19943159731783546012722061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106363518569512245401184325 19943159731783546012722061)
      ·
        refine ⟨7478684899418829754770773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19943159731783546012722061 7478684899418829754770773)
        ·
          refine ⟨5477552416566525699295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7478684899418829754770773 5477552416566525699295)
          ·
            rfl

theorem cell23_7776604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 12].length) (baseStart_7776604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776604 prefixEnd_7776604 := by exact prefixLift 7776604
  have htrace : WordTrace (prefixWord ++ tailWord_7776604) baseStart_7776604 baseEnd_7776604 := by
    simpa [prefixWord, tailWord_7776604, baseEnd_7776604] using wordTrace_append hprefix tailTrace_7776604
  have hstable : (prefixWord ++ tailWord_7776604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776604).length < 2 ^ (prefixWord ++ tailWord_7776604).sum := by decide
  have hdescent : baseEnd_7776604 < baseStart_7776604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776608 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 2, 4]
def baseStart_7776608 : Nat := 118140960795 + 7776608 * 2 ^ 59
def prefixEnd_7776608 : Nat := 4983230072969 + 3 ^ 40 * 7776608 * 2
def baseEnd_7776608 : Nat := 1331045921866538406378679

theorem tailTrace_7776608 : CollatzResearch.WordTrace tailWord_7776608 prefixEnd_7776608 1331045921866538406378679 := by
  unfold tailWord_7776608
  simp only [CollatzResearch.WordTrace]
  refine ⟨141818097705342414876485239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189090796940456553168646985 141818097705342414876485239)
  ·
    refine ⟨212727146558013622314727859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141818097705342414876485239 212727146558013622314727859)
    ·
      refine ⟨319090719837020433472091789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212727146558013622314727859 319090719837020433472091789)
      ·
        refine ⟨119659019938882662552034421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319090719837020433472091789 119659019938882662552034421)
        ·
          refine ⟨11218033119270249614253227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119659019938882662552034421 11218033119270249614253227)
          ·
            refine ⟨16827049678905374421379841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11218033119270249614253227 16827049678905374421379841)
            ·
              refine ⟨12620287259179030816034881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16827049678905374421379841 12620287259179030816034881)
              ·
                refine ⟨9465215444384273112026161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12620287259179030816034881 9465215444384273112026161)
                ·
                  refine ⟨7098911583288204834019621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9465215444384273112026161 7098911583288204834019621)
                  ·
                    refine ⟨1331045921866538406378679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7098911583288204834019621 1331045921866538406378679)
                    ·
                      rfl

theorem cell23_7776608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 4].length) (baseStart_7776608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776608 prefixEnd_7776608 := by exact prefixLift 7776608
  have htrace : WordTrace (prefixWord ++ tailWord_7776608) baseStart_7776608 baseEnd_7776608 := by
    simpa [prefixWord, tailWord_7776608, baseEnd_7776608] using wordTrace_append hprefix tailTrace_7776608
  have hstable : (prefixWord ++ tailWord_7776608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776608).length < 2 ^ (prefixWord ++ tailWord_7776608).sum := by decide
  have hdescent : baseEnd_7776608 < baseStart_7776608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776617 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 1, 9]
def baseStart_7776617 : Nat := 118140960795 + 7776617 * 2 ^ 59
def prefixEnd_7776617 : Nat := 4983230072969 + 3 ^ 40 * 7776617 * 2
def baseEnd_7776617 : Nat := 1331047462308501894641165

theorem tailTrace_7776617 : CollatzResearch.WordTrace tailWord_7776617 prefixEnd_7776617 1331047462308501894641165 := by
  unfold tailWord_7776617
  simp only [CollatzResearch.WordTrace]
  refine ⟨283636523667652224290048105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189091015778434816193365403 283636523667652224290048105)
  ·
    refine ⟨212727392750739168217536079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283636523667652224290048105 212727392750739168217536079)
    ·
      refine ⟨319091089126108752326304119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212727392750739168217536079 319091089126108752326304119)
      ·
        refine ⟨478636633689163128489456179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319091089126108752326304119 478636633689163128489456179)
        ·
          refine ⟨717954950533744692734184269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478636633689163128489456179 717954950533744692734184269)
          ·
            refine ⟨269233106450154259775319101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 717954950533744692734184269 269233106450154259775319101)
            ·
              refine ⟨100962414918807847415744663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269233106450154259775319101 100962414918807847415744663)
              ·
                refine ⟨151443622378211771123616995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100962414918807847415744663 151443622378211771123616995)
                ·
                  refine ⟨227165433567317656685425493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151443622378211771123616995 227165433567317656685425493)
                  ·
                    refine ⟨1331047462308501894641165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227165433567317656685425493 1331047462308501894641165)
                    ·
                      rfl

theorem cell23_7776617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_7776617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776617 prefixEnd_7776617 := by exact prefixLift 7776617
  have htrace : WordTrace (prefixWord ++ tailWord_7776617) baseStart_7776617 baseEnd_7776617 := by
    simpa [prefixWord, tailWord_7776617, baseEnd_7776617] using wordTrace_append hprefix tailTrace_7776617
  have hstable : (prefixWord ++ tailWord_7776617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776617).length < 2 ^ (prefixWord ++ tailWord_7776617).sum := by decide
  have hdescent : baseEnd_7776617 < baseStart_7776617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776644 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7776644 : Nat := 118140960795 + 7776644 * 2 ^ 59
def prefixEnd_7776644 : Nat := 4983230072969 + 3 ^ 40 * 7776644 * 2
def baseEnd_7776644 : Nat := 3993156250903177078285871

theorem tailTrace_7776644 : CollatzResearch.WordTrace tailWord_7776644 prefixEnd_7776644 3993156250903177078285871 := by
  unfold tailWord_7776644
  simp only [CollatzResearch.WordTrace]
  refine ⟨141818754219277203950640493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189091672292369605267520657 141818754219277203950640493)
  ·
    refine ⟨53182032832228951481490185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141818754219277203950640493 53182032832228951481490185)
    ·
      refine ⟨39886524624171713611117639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53182032832228951481490185 39886524624171713611117639)
      ·
        refine ⟨59829786936257570416676459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39886524624171713611117639 59829786936257570416676459)
        ·
          refine ⟨89744680404386355625014689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59829786936257570416676459 89744680404386355625014689)
          ·
            refine ⟨67308510303289766718761017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89744680404386355625014689 67308510303289766718761017)
            ·
              refine ⟨50481382727467325039070763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67308510303289766718761017 50481382727467325039070763)
              ·
                refine ⟨75722074091200987558606145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50481382727467325039070763 75722074091200987558606145)
                ·
                  refine ⟨56791555568400740668954609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75722074091200987558606145 56791555568400740668954609)
                  ·
                    refine ⟨42593666676300555501715957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56791555568400740668954609 42593666676300555501715957)
                    ·
                      refine ⟨3993156250903177078285871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42593666676300555501715957 3993156250903177078285871)
                      ·
                        rfl

theorem cell23_7776644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7776644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776644 prefixEnd_7776644 := by exact prefixLift 7776644
  have htrace : WordTrace (prefixWord ++ tailWord_7776644) baseStart_7776644 baseEnd_7776644 := by
    simpa [prefixWord, tailWord_7776644, baseEnd_7776644] using wordTrace_append hprefix tailTrace_7776644
  have hstable : (prefixWord ++ tailWord_7776644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776644).length < 2 ^ (prefixWord ++ tailWord_7776644).sum := by decide
  have hdescent : baseEnd_7776644 < baseStart_7776644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776708 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7776708 : Nat := 118140960795 + 7776708 * 2 ^ 59
def prefixEnd_7776708 : Nat := 4983230072969 + 3 ^ 40 * 7776708 * 2
def baseEnd_7776708 : Nat := 3993189113665064827885577

theorem tailTrace_7776708 : CollatzResearch.WordTrace tailWord_7776708 prefixEnd_7776708 3993189113665064827885577 := by
  unfold tailWord_7776708
  simp only [CollatzResearch.WordTrace]
  refine ⟨141819921355161273415805389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189093228473548364554407185 141819921355161273415805389)
  ·
    refine ⟨53182470508185477530927021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141819921355161273415805389 53182470508185477530927021)
    ·
      refine ⟨19943426440569554074097633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53182470508185477530927021 19943426440569554074097633)
      ·
        refine ⟨14957569830427165555573225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19943426440569554074097633 14957569830427165555573225)
        ·
          refine ⟨11218177372820374166679919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14957569830427165555573225 11218177372820374166679919)
          ·
            refine ⟨16827266059230561250019879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11218177372820374166679919 16827266059230561250019879)
            ·
              refine ⟨25240899088845841875029819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16827266059230561250019879 25240899088845841875029819)
              ·
                refine ⟨37861348633268762812544729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25240899088845841875029819 37861348633268762812544729)
                ·
                  refine ⟨28396011474951572109408547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37861348633268762812544729 28396011474951572109408547)
                  ·
                    refine ⟨42594017212427358164112821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28396011474951572109408547 42594017212427358164112821)
                    ·
                      refine ⟨3993189113665064827885577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42594017212427358164112821 3993189113665064827885577)
                      ·
                        rfl

theorem cell23_7776708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7776708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776708 prefixEnd_7776708 := by exact prefixLift 7776708
  have htrace : WordTrace (prefixWord ++ tailWord_7776708) baseStart_7776708 baseEnd_7776708 := by
    simpa [prefixWord, tailWord_7776708, baseEnd_7776708] using wordTrace_append hprefix tailTrace_7776708
  have hstable : (prefixWord ++ tailWord_7776708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776708).length < 2 ^ (prefixWord ++ tailWord_7776708).sum := by decide
  have hdescent : baseEnd_7776708 < baseStart_7776708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776739 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 2, 2, 2]
def baseStart_7776739 : Nat := 118140960795 + 7776739 * 2 ^ 59
def prefixEnd_7776739 : Nat := 4983230072969 + 3 ^ 40 * 7776739 * 2
def baseEnd_7776739 : Nat := 3993205031565354206597935

theorem tailTrace_7776739 : CollatzResearch.WordTrace tailWord_7776739 prefixEnd_7776739 3993205031565354206597935 := by
  unfold tailWord_7776739
  simp only [CollatzResearch.WordTrace]
  refine ⟨283640973373210239125989271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189093982248806826083992847 283640973373210239125989271)
  ·
    refine ⟨425461460059815358688983907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283640973373210239125989271 425461460059815358688983907)
    ·
      refine ⟨638192190089723038033475861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425461460059815358688983907 638192190089723038033475861)
      ·
        refine ⟨29915258910455767407819181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 638192190089723038033475861 29915258910455767407819181)
        ·
          refine ⟨11218222091420912777932193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29915258910455767407819181 11218222091420912777932193)
          ·
            refine ⟨8413666568565684583449145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11218222091420912777932193 8413666568565684583449145)
            ·
              refine ⟨6310249926424263437586859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8413666568565684583449145 6310249926424263437586859)
              ·
                refine ⟨9465374889636395156380289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310249926424263437586859 9465374889636395156380289)
                ·
                  refine ⟨7099031167227296367285217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9465374889636395156380289 7099031167227296367285217)
                  ·
                    refine ⟨5324273375420472275463913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7099031167227296367285217 5324273375420472275463913)
                    ·
                      refine ⟨3993205031565354206597935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324273375420472275463913 3993205031565354206597935)
                      ·
                        rfl

theorem cell23_7776739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_7776739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776739 prefixEnd_7776739 := by exact prefixLift 7776739
  have htrace : WordTrace (prefixWord ++ tailWord_7776739) baseStart_7776739 baseEnd_7776739 := by
    simpa [prefixWord, tailWord_7776739, baseEnd_7776739] using wordTrace_append hprefix tailTrace_7776739
  have hstable : (prefixWord ++ tailWord_7776739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776739).length < 2 ^ (prefixWord ++ tailWord_7776739).sum := by decide
  have hdescent : baseEnd_7776739 < baseStart_7776739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776758 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_7776758 : Nat := 118140960795 + 7776758 * 2 ^ 59
def prefixEnd_7776758 : Nat := 4983230072969 + 3 ^ 40 * 7776758 * 2
def baseEnd_7776758 : Nat := 1331071595899263210753449

theorem tailTrace_7776758 : CollatzResearch.WordTrace tailWord_7776758 prefixEnd_7776758 1331071595899263210753449 := by
  unfold tailWord_7776758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17727604147508837835683183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189094444240094270247287285 17727604147508837835683183)
  ·
    refine ⟨26591406221263256753524775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17727604147508837835683183 26591406221263256753524775)
    ·
      refine ⟨39887109331894885130287163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26591406221263256753524775 39887109331894885130287163)
      ·
        refine ⟨59830663997842327695430745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39887109331894885130287163 59830663997842327695430745)
        ·
          refine ⟨44872997998381745771573059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59830663997842327695430745 44872997998381745771573059)
          ·
            refine ⟨67309496997572618657359589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44872997998381745771573059 67309496997572618657359589)
            ·
              refine ⟨12620530687044865998254923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67309496997572618657359589 12620530687044865998254923)
              ·
                refine ⟨18930796030567298997382385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12620530687044865998254923 18930796030567298997382385)
                ·
                  refine ⟨14198097022925474248036789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18930796030567298997382385 14198097022925474248036789)
                  ·
                    refine ⟨1331071595899263210753449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14198097022925474248036789 1331071595899263210753449)
                    ·
                      rfl

theorem cell23_7776758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_7776758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776758 prefixEnd_7776758 := by exact prefixLift 7776758
  have htrace : WordTrace (prefixWord ++ tailWord_7776758) baseStart_7776758 baseEnd_7776758 := by
    simpa [prefixWord, tailWord_7776758, baseEnd_7776758] using wordTrace_append hprefix tailTrace_7776758
  have hstable : (prefixWord ++ tailWord_7776758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776758).length < 2 ^ (prefixWord ++ tailWord_7776758).sum := by decide
  have hdescent : baseEnd_7776758 < baseStart_7776758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776761 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_7776761 : Nat := 118140960795 + 7776761 * 2 ^ 59
def prefixEnd_7776761 : Nat := 4983230072969 + 3 ^ 40 * 7776761 * 2
def baseEnd_7776761 : Nat := 3993216328139753120522833

theorem tailTrace_7776761 : CollatzResearch.WordTrace tailWord_7776761 prefixEnd_7776761 3993216328139753120522833 := by
  unfold tailWord_7776761
  simp only [CollatzResearch.WordTrace]
  refine ⟨283641775779130536883290137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189094517186087024588860091 283641775779130536883290137)
  ·
    refine ⟨212731331834347902662467603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283641775779130536883290137 212731331834347902662467603)
    ·
      refine ⟨319096997751521853993701405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212731331834347902662467603 319096997751521853993701405)
      ·
        refine ⟨119661374156820695247638027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319096997751521853993701405 119661374156820695247638027)
        ·
          refine ⟨179492061235231042871457041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119661374156820695247638027 179492061235231042871457041)
          ·
            refine ⟨134619045926423282153592781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179492061235231042871457041 134619045926423282153592781)
            ·
              refine ⟨50482142222408730807597293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134619045926423282153592781 50482142222408730807597293)
              ·
                refine ⟨18930803333403274052848985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50482142222408730807597293 18930803333403274052848985)
                ·
                  refine ⟨14198102500052455539636739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18930803333403274052848985 14198102500052455539636739)
                  ·
                    refine ⟨21297153750078683309455109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14198102500052455539636739 21297153750078683309455109)
                    ·
                      refine ⟨3993216328139753120522833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21297153750078683309455109 3993216328139753120522833)
                      ·
                        rfl

theorem cell23_7776761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_7776761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776761 prefixEnd_7776761 := by exact prefixLift 7776761
  have htrace : WordTrace (prefixWord ++ tailWord_7776761) baseStart_7776761 baseEnd_7776761 := by
    simpa [prefixWord, tailWord_7776761, baseEnd_7776761] using wordTrace_append hprefix tailTrace_7776761
  have hstable : (prefixWord ++ tailWord_7776761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776761).length < 2 ^ (prefixWord ++ tailWord_7776761).sum := by decide
  have hdescent : baseEnd_7776761 < baseStart_7776761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776778 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_7776778 : Nat := 118140960795 + 7776778 * 2 ^ 59
def prefixEnd_7776778 : Nat := 4983230072969 + 3 ^ 40 * 7776778 * 2
def baseEnd_7776778 : Nat := 3993225057310879554010255

theorem tailTrace_7776778 : CollatzResearch.WordTrace tailWord_7776778 prefixEnd_7776778 3993225057310879554010255 := by
  unfold tailWord_7776778
  simp only [CollatzResearch.WordTrace]
  refine ⟨70910598955017237196664747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189094930546712632524439325 70910598955017237196664747)
  ·
    refine ⟨106365898432525855794997121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70910598955017237196664747 106365898432525855794997121)
    ·
      refine ⟨79774423824394391846247841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106365898432525855794997121 79774423824394391846247841)
      ·
        refine ⟨59830817868295793884685881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79774423824394391846247841 59830817868295793884685881)
        ·
          refine ⟨44873113401221845413514411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59830817868295793884685881 44873113401221845413514411)
          ·
            refine ⟨67309670101832768120271617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44873113401221845413514411 67309670101832768120271617)
            ·
              refine ⟨50482252576374576090203713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67309670101832768120271617 50482252576374576090203713)
              ·
                refine ⟨37861689432280932067652785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50482252576374576090203713 37861689432280932067652785)
                ·
                  refine ⟨28396267074210699050739589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37861689432280932067652785 28396267074210699050739589)
                  ·
                    refine ⟨5324300076414506072013673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28396267074210699050739589 5324300076414506072013673)
                    ·
                      refine ⟨3993225057310879554010255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324300076414506072013673 3993225057310879554010255)
                      ·
                        rfl

theorem cell23_7776778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_7776778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776778 prefixEnd_7776778 := by exact prefixLift 7776778
  have htrace : WordTrace (prefixWord ++ tailWord_7776778) baseStart_7776778 baseEnd_7776778 := by
    simpa [prefixWord, tailWord_7776778, baseEnd_7776778] using wordTrace_append hprefix tailTrace_7776778
  have hstable : (prefixWord ++ tailWord_7776778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776778).length < 2 ^ (prefixWord ++ tailWord_7776778).sum := by decide
  have hdescent : baseEnd_7776778 < baseStart_7776778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776801 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 6]
def baseStart_7776801 : Nat := 118140960795 + 7776801 * 2 ^ 59
def prefixEnd_7776801 : Nat := 4983230072969 + 3 ^ 40 * 7776801 * 2
def baseEnd_7776801 : Nat := 443692985262881440446961

theorem tailTrace_7776801 : CollatzResearch.WordTrace tailWord_7776801 prefixEnd_7776801 443692985262881440446961 := by
  unfold tailWord_7776801
  simp only [CollatzResearch.WordTrace]
  refine ⟨283643234698985623714746257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189095489799323749143164171 283643234698985623714746257)
  ·
    refine ⟨212732426024239217786059693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283643234698985623714746257 212732426024239217786059693)
    ·
      refine ⟨79774659759089706669772385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212732426024239217786059693 79774659759089706669772385)
      ·
        refine ⟨59830994819317280002329289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79774659759089706669772385 59830994819317280002329289)
        ·
          refine ⟨44873246114487960001746967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59830994819317280002329289 44873246114487960001746967)
          ·
            refine ⟨67309869171731940002620451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44873246114487960001746967 67309869171731940002620451)
            ·
              refine ⟨100964803757597910003930677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67309869171731940002620451 100964803757597910003930677)
              ·
                refine ⟨9465450352274804062868501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100964803757597910003930677 9465450352274804062868501)
                ·
                  refine ⟨443692985262881440446961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9465450352274804062868501 443692985262881440446961)
                  ·
                    rfl

theorem cell23_7776801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 6].length) (baseStart_7776801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776801 prefixEnd_7776801 := by exact prefixLift 7776801
  have htrace : WordTrace (prefixWord ++ tailWord_7776801) baseStart_7776801 baseEnd_7776801 := by
    simpa [prefixWord, tailWord_7776801, baseEnd_7776801] using wordTrace_append hprefix tailTrace_7776801
  have hstable : (prefixWord ++ tailWord_7776801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776801).length < 2 ^ (prefixWord ++ tailWord_7776801).sum := by decide
  have hdescent : baseEnd_7776801 < baseStart_7776801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776822 : List Nat := [5, 1, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_7776822 : Nat := 118140960795 + 7776822 * 2 ^ 59
def prefixEnd_7776822 : Nat := 4983230072969 + 3 ^ 40 * 7776822 * 2
def baseEnd_7776822 : Nat := 1331082550153225793953351

theorem tailTrace_7776822 : CollatzResearch.WordTrace tailWord_7776822 prefixEnd_7776822 1331082550153225793953351 := by
  unfold tailWord_7776822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17727750039494346518828795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189096000421273029534173813 17727750039494346518828795)
  ·
    refine ⟨26591625059241519778243193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17727750039494346518828795 26591625059241519778243193)
    ·
      refine ⟨19943718794431139833682395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26591625059241519778243193 19943718794431139833682395)
      ·
        refine ⟨29915578191646709750523593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19943718794431139833682395 29915578191646709750523593)
        ·
          refine ⟨22436683643735032312892695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29915578191646709750523593 22436683643735032312892695)
          ·
            refine ⟨33655025465602548469339043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22436683643735032312892695 33655025465602548469339043)
            ·
              refine ⟨50482538198403822704008565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33655025465602548469339043 50482538198403822704008565)
              ·
                refine ⟨4732737956100358378500803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50482538198403822704008565 4732737956100358378500803)
                ·
                  refine ⟨7099106934150537567751205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732737956100358378500803 7099106934150537567751205)
                  ·
                    refine ⟨1331082550153225793953351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099106934150537567751205 1331082550153225793953351)
                    ·
                      rfl

theorem cell23_7776822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_7776822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776822 prefixEnd_7776822 := by exact prefixLift 7776822
  have htrace : WordTrace (prefixWord ++ tailWord_7776822) baseStart_7776822 baseEnd_7776822 := by
    simpa [prefixWord, tailWord_7776822, baseEnd_7776822] using wordTrace_append hprefix tailTrace_7776822
  have hstable : (prefixWord ++ tailWord_7776822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776822).length < 2 ^ (prefixWord ++ tailWord_7776822).sum := by decide
  have hdescent : baseEnd_7776822 < baseStart_7776822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776868 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_7776868 : Nat := 118140960795 + 7776868 * 2 ^ 59
def prefixEnd_7776868 : Nat := 4983230072969 + 3 ^ 40 * 7776868 * 2
def baseEnd_7776868 : Nat := 3993271270569784201884841

theorem tailTrace_7776868 : CollatzResearch.WordTrace tailWord_7776868 prefixEnd_7776868 3993271270569784201884841 := by
  unfold tailWord_7776868
  simp only [CollatzResearch.WordTrace]
  refine ⟨141822839194871447078717629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189097118926495262771623505 141822839194871447078717629)
  ·
    refine ⟨53183564698076792654519111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141822839194871447078717629 53183564698076792654519111)
    ·
      refine ⟨79775347047115188981778667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53183564698076792654519111 79775347047115188981778667)
      ·
        refine ⟨119663020570672783472668001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79775347047115188981778667 119663020570672783472668001)
        ·
          refine ⟨89747265428004587604501001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119663020570672783472668001 89747265428004587604501001)
          ·
            refine ⟨67310449071003440703375751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89747265428004587604501001 67310449071003440703375751)
            ·
              refine ⟨100965673606505161055063627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67310449071003440703375751 100965673606505161055063627)
              ·
                refine ⟨151448510409757741582595441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100965673606505161055063627 151448510409757741582595441)
                ·
                  refine ⟨113586382807318306186946581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151448510409757741582595441 113586382807318306186946581)
                  ·
                    refine ⟨5324361694093045602513121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113586382807318306186946581 5324361694093045602513121)
                    ·
                      refine ⟨3993271270569784201884841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324361694093045602513121 3993271270569784201884841)
                      ·
                        rfl

theorem cell23_7776868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_7776868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776868 prefixEnd_7776868 := by exact prefixLift 7776868
  have htrace : WordTrace (prefixWord ++ tailWord_7776868) baseStart_7776868 baseEnd_7776868 := by
    simpa [prefixWord, tailWord_7776868, baseEnd_7776868] using wordTrace_append hprefix tailTrace_7776868
  have hstable : (prefixWord ++ tailWord_7776868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776868).length < 2 ^ (prefixWord ++ tailWord_7776868).sum := by decide
  have hdescent : baseEnd_7776868 < baseStart_7776868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776871 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_7776871 : Nat := 118140960795 + 7776871 * 2 ^ 59
def prefixEnd_7776871 : Nat := 4983230072969 + 3 ^ 40 * 7776871 * 2
def baseEnd_7776871 : Nat := 3993272811011747690147327

theorem tailTrace_7776871 : CollatzResearch.WordTrace tailWord_7776871 prefixEnd_7776871 3993272811011747690147327 := by
  unfold tailWord_7776871
  simp only [CollatzResearch.WordTrace]
  refine ⟨283645787808732025669794467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189097191872488017113196311 283645787808732025669794467)
  ·
    refine ⟨425468681713098038504691701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283645787808732025669794467 425468681713098038504691701)
    ·
      refine ⟨39887688910602941109814847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 425468681713098038504691701 39887688910602941109814847)
      ·
        refine ⟨59831533365904411664722271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39887688910602941109814847 59831533365904411664722271)
        ·
          refine ⟨89747300048856617497083407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59831533365904411664722271 89747300048856617497083407)
          ·
            refine ⟨134620950073284926245625111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89747300048856617497083407 134620950073284926245625111)
            ·
              refine ⟨201931425109927389368437667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134620950073284926245625111 201931425109927389368437667)
              ·
                refine ⟨302897137664891084052656501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201931425109927389368437667 302897137664891084052656501)
                ·
                  refine ⟨28396606656083539129936547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 302897137664891084052656501 28396606656083539129936547)
                  ·
                    refine ⟨42594909984125308694904821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28396606656083539129936547 42594909984125308694904821)
                    ·
                      refine ⟨3993272811011747690147327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42594909984125308694904821 3993272811011747690147327)
                      ·
                        rfl

theorem cell23_7776871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_7776871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776871 prefixEnd_7776871 := by exact prefixLift 7776871
  have htrace : WordTrace (prefixWord ++ tailWord_7776871) baseStart_7776871 baseEnd_7776871 := by
    simpa [prefixWord, tailWord_7776871, baseEnd_7776871] using wordTrace_append hprefix tailTrace_7776871
  have hstable : (prefixWord ++ tailWord_7776871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776871).length < 2 ^ (prefixWord ++ tailWord_7776871).sum := by decide
  have hdescent : baseEnd_7776871 < baseStart_7776871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776922 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7776922 : Nat := 118140960795 + 7776922 * 2 ^ 59
def prefixEnd_7776922 : Nat := 4983230072969 + 3 ^ 40 * 7776922 * 2
def baseEnd_7776922 : Nat := 3993298998525126990609593

theorem tailTrace_7776922 : CollatzResearch.WordTrace tailWord_7776922 prefixEnd_7776922 3993298998525126990609593 := by
  unfold tailWord_7776922
  simp only [CollatzResearch.WordTrace]
  refine ⟨70911911982886815344975255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189098431954364840919934013 70911911982886815344975255)
  ·
    refine ⟨106367867974330223017462883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70911911982886815344975255 106367867974330223017462883)
    ·
      refine ⟨159551801961495334526194325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106367867974330223017462883 159551801961495334526194325)
      ·
        refine ⟨7478990716945093805915359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159551801961495334526194325 7478990716945093805915359)
        ·
          refine ⟨11218486075417640708873039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478990716945093805915359 11218486075417640708873039)
          ·
            refine ⟨16827729113126461063309559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11218486075417640708873039 16827729113126461063309559)
            ·
              refine ⟨25241593669689691594964339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16827729113126461063309559 25241593669689691594964339)
              ·
                refine ⟨37862390504534537392446509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25241593669689691594964339 37862390504534537392446509)
                ·
                  refine ⟨14198396439200451522167441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37862390504534537392446509 14198396439200451522167441)
                  ·
                    refine ⟨10648797329400338641625581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14198396439200451522167441 10648797329400338641625581)
                    ·
                      refine ⟨3993298998525126990609593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10648797329400338641625581 3993298998525126990609593)
                      ·
                        rfl

theorem cell23_7776922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7776922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776922 prefixEnd_7776922 := by exact prefixLift 7776922
  have htrace : WordTrace (prefixWord ++ tailWord_7776922) baseStart_7776922 baseEnd_7776922 := by
    simpa [prefixWord, tailWord_7776922, baseEnd_7776922] using wordTrace_append hprefix tailTrace_7776922
  have hstable : (prefixWord ++ tailWord_7776922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776922).length < 2 ^ (prefixWord ++ tailWord_7776922).sum := by decide
  have hdescent : baseEnd_7776922 < baseStart_7776922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776931 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 5]
def baseStart_7776931 : Nat := 118140960795 + 7776931 * 2 ^ 59
def prefixEnd_7776931 : Nat := 4983230072969 + 3 ^ 40 * 7776931 * 2
def baseEnd_7776931 : Nat := 3993303619851017455397051

theorem tailTrace_7776931 : CollatzResearch.WordTrace tailWord_7776931 prefixEnd_7776931 3993303619851017455397051 := by
  unfold tailWord_7776931
  simp only [CollatzResearch.WordTrace]
  refine ⟨283647976188514655916978647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189098650792343103944652431 283647976188514655916978647)
  ·
    refine ⟨425471964282771983875467971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283647976188514655916978647 425471964282771983875467971)
    ·
      refine ⟨638207946424157975813201957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425471964282771983875467971 638207946424157975813201957)
      ·
        refine ⟨119663989954529620464975367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 638207946424157975813201957 119663989954529620464975367)
        ·
          refine ⟨179495984931794430697463051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119663989954529620464975367 179495984931794430697463051)
          ·
            refine ⟨269243977397691646046194577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179495984931794430697463051 269243977397691646046194577)
            ·
              refine ⟨201932983048268734534645933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269243977397691646046194577 201932983048268734534645933)
              ·
                refine ⟨75724868643100775450492225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201932983048268734534645933 75724868643100775450492225)
                ·
                  refine ⟨56793651482325581587869169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75724868643100775450492225 56793651482325581587869169)
                  ·
                    refine ⟨42595238611744186190901877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56793651482325581587869169 42595238611744186190901877)
                    ·
                      refine ⟨3993303619851017455397051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42595238611744186190901877 3993303619851017455397051)
                      ·
                        rfl

theorem cell23_7776931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_7776931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776931 prefixEnd_7776931 := by exact prefixLift 7776931
  have htrace : WordTrace (prefixWord ++ tailWord_7776931) baseStart_7776931 baseEnd_7776931 := by
    simpa [prefixWord, tailWord_7776931, baseEnd_7776931] using wordTrace_append hprefix tailTrace_7776931
  have hstable : (prefixWord ++ tailWord_7776931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776931).length < 2 ^ (prefixWord ++ tailWord_7776931).sum := by decide
  have hdescent : baseEnd_7776931 < baseStart_7776931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776958 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_7776958 : Nat := 118140960795 + 7776958 * 2 ^ 59
def prefixEnd_7776958 : Nat := 4983230072969 + 3 ^ 40 * 7776958 * 2
def baseEnd_7776958 : Nat := 3993317483828688849759427

theorem tailTrace_7776958 : CollatzResearch.WordTrace tailWord_7776958 prefixEnd_7776958 3993317483828688849759427 := by
  unfold tailWord_7776958
  simp only [CollatzResearch.WordTrace]
  refine ⟨35456120119927104941026441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189099307306277893018807685 35456120119927104941026441)
  ·
    refine ⟨26592090089945328705769831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35456120119927104941026441 26592090089945328705769831)
    ·
      refine ⟨39888135134917993058654747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26592090089945328705769831 39888135134917993058654747)
      ·
        refine ⟨59832202702376989587982121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39888135134917993058654747 59832202702376989587982121)
        ·
          refine ⟨44874152026782742190986591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59832202702376989587982121 44874152026782742190986591)
          ·
            refine ⟨67311228040174113286479887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44874152026782742190986591 67311228040174113286479887)
            ·
              refine ⟨100966842060261169929719831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67311228040174113286479887 100966842060261169929719831)
              ·
                refine ⟨151450263090391754894579747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100966842060261169929719831 151450263090391754894579747)
                ·
                  refine ⟨227175394635587632341869621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151450263090391754894579747 227175394635587632341869621)
                  ·
                    refine ⟨21297693247086340532050277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 227175394635587632341869621 21297693247086340532050277)
                    ·
                      refine ⟨3993317483828688849759427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21297693247086340532050277 3993317483828688849759427)
                      ·
                        rfl

theorem cell23_7776958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_7776958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776958 prefixEnd_7776958 := by exact prefixLift 7776958
  have htrace : WordTrace (prefixWord ++ tailWord_7776958) baseStart_7776958 baseEnd_7776958 := by
    simpa [prefixWord, tailWord_7776958, baseEnd_7776958] using wordTrace_append hprefix tailTrace_7776958
  have hstable : (prefixWord ++ tailWord_7776958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776958).length < 2 ^ (prefixWord ++ tailWord_7776958).sum := by decide
  have hdescent : baseEnd_7776958 < baseStart_7776958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776968 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 2, 6]
def baseStart_7776968 : Nat := 118140960795 + 7776968 * 2 ^ 59
def prefixEnd_7776968 : Nat := 4983230072969 + 3 ^ 40 * 7776968 * 2
def baseEnd_7776968 : Nat := 1331107539545077936878127

theorem tailTrace_7776968 : CollatzResearch.WordTrace tailWord_7776968 prefixEnd_7776968 1331107539545077936878127 := by
  unfold tailWord_7776968
  simp only [CollatzResearch.WordTrace]
  refine ⟨141824662844690305618037779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189099550459587074157383705 141824662844690305618037779)
  ·
    refine ⟨212736994267035458427056669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141824662844690305618037779 212736994267035458427056669)
    ·
      refine ⟨79776372850138296910146251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212736994267035458427056669 79776372850138296910146251)
      ·
        refine ⟨119664559275207445365219377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79776372850138296910146251 119664559275207445365219377)
        ·
          refine ⟨89748419456405584023914533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119664559275207445365219377 89748419456405584023914533)
          ·
            refine ⟨16827828648076047004483975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89748419456405584023914533 16827828648076047004483975)
            ·
              refine ⟨25241742972114070506725963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16827828648076047004483975 25241742972114070506725963)
              ·
                refine ⟨37862614458171105760088945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25241742972114070506725963 37862614458171105760088945)
                ·
                  refine ⟨28396960843628329320066709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37862614458171105760088945 28396960843628329320066709)
                  ·
                    refine ⟨1331107539545077936878127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28396960843628329320066709 1331107539545077936878127)
                    ·
                      rfl

theorem cell23_7776968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_7776968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776968 prefixEnd_7776968 := by exact prefixLift 7776968
  have htrace : WordTrace (prefixWord ++ tailWord_7776968) baseStart_7776968 baseEnd_7776968 := by
    simpa [prefixWord, tailWord_7776968, baseEnd_7776968] using wordTrace_append hprefix tailTrace_7776968
  have hstable : (prefixWord ++ tailWord_7776968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776968).length < 2 ^ (prefixWord ++ tailWord_7776968).sum := by decide
  have hdescent : baseEnd_7776968 < baseStart_7776968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7776975 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 8, 2, 2]
def baseStart_7776975 : Nat := 118140960795 + 7776975 * 2 ^ 59
def prefixEnd_7776975 : Nat := 4983230072969 + 3 ^ 40 * 7776975 * 2
def baseEnd_7776975 : Nat := 3993326212999815283246849

theorem tailTrace_7776975 : CollatzResearch.WordTrace tailWord_7776975 prefixEnd_7776975 3993326212999815283246849 := by
  unfold tailWord_7776975
  simp only [CollatzResearch.WordTrace]
  refine ⟨283649581000355251431580379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189099720666903500954386919 283649581000355251431580379)
  ·
    refine ⟨425474371500532877147370569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283649581000355251431580379 425474371500532877147370569)
    ·
      refine ⟨319105778625399657860527927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425474371500532877147370569 319105778625399657860527927)
      ·
        refine ⟨478658667938099486790791891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319105778625399657860527927 478658667938099486790791891)
        ·
          refine ⟨717988001907149230186187837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478658667938099486790791891 717988001907149230186187837)
          ·
            refine ⟨269245500715180961319820439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 717988001907149230186187837 269245500715180961319820439)
            ·
              refine ⟨403868251072771441979730659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269245500715180961319820439 403868251072771441979730659)
              ·
                refine ⟨605802376609157162969595989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403868251072771441979730659 605802376609157162969595989)
                ·
                  refine ⟨7099246600888560503549953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 605802376609157162969595989 7099246600888560503549953)
                  ·
                    refine ⟨5324434950666420377662465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7099246600888560503549953 5324434950666420377662465)
                    ·
                      refine ⟨3993326212999815283246849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324434950666420377662465 3993326212999815283246849)
                      ·
                        rfl

theorem cell23_7776975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 2, 2].length) (baseStart_7776975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7776975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7776975 prefixEnd_7776975 := by exact prefixLift 7776975
  have htrace : WordTrace (prefixWord ++ tailWord_7776975) baseStart_7776975 baseEnd_7776975 := by
    simpa [prefixWord, tailWord_7776975, baseEnd_7776975] using wordTrace_append hprefix tailTrace_7776975
  have hstable : (prefixWord ++ tailWord_7776975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7776975).length < 2 ^ (prefixWord ++ tailWord_7776975).sum := by decide
  have hdescent : baseEnd_7776975 < baseStart_7776975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7776975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777008 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 3]
def baseStart_7777008 : Nat := 118140960795 + 7777008 * 2 ^ 59
def prefixEnd_7777008 : Nat := 4983230072969 + 3 ^ 40 * 7777008 * 2
def baseEnd_7777008 : Nat := 3993343157861413654134197

theorem tailTrace_7777008 : CollatzResearch.WordTrace tailWord_7777008 prefixEnd_7777008 3993343157861413654134197 := by
  unfold tailWord_7777008
  simp only [CollatzResearch.WordTrace]
  refine ⟨141825392304617849033765839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189100523072823798711687785 141825392304617849033765839)
  ·
    refine ⟨212738088456926773550648759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141825392304617849033765839 212738088456926773550648759)
    ·
      refine ⟨319107132685390160325973139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212738088456926773550648759 319107132685390160325973139)
      ·
        refine ⟨478660699028085240488959709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319107132685390160325973139 478660699028085240488959709)
        ·
          refine ⟨179497762135531965183359891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478660699028085240488959709 179497762135531965183359891)
          ·
            refine ⟨269246643203297947775039837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179497762135531965183359891 269246643203297947775039837)
            ·
              refine ⟨100967491201236730415639939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269246643203297947775039837 100967491201236730415639939)
              ·
                refine ⟨151451236801855095623459909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100967491201236730415639939 151451236801855095623459909)
                ·
                  refine ⟨28397106900347830429398733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151451236801855095623459909 28397106900347830429398733)
                  ·
                    refine ⟨10648915087630436411024525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28397106900347830429398733 10648915087630436411024525)
                    ·
                      refine ⟨3993343157861413654134197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10648915087630436411024525 3993343157861413654134197)
                      ·
                        rfl

theorem cell23_7777008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_7777008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777008 prefixEnd_7777008 := by exact prefixLift 7777008
  have htrace : WordTrace (prefixWord ++ tailWord_7777008) baseStart_7777008 baseEnd_7777008 := by
    simpa [prefixWord, tailWord_7777008, baseEnd_7777008] using wordTrace_append hprefix tailTrace_7777008
  have hstable : (prefixWord ++ tailWord_7777008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777008).length < 2 ^ (prefixWord ++ tailWord_7777008).sum := by decide
  have hdescent : baseEnd_7777008 < baseStart_7777008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777028 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_7777028 : Nat := 118140960795 + 7777028 * 2 ^ 59
def prefixEnd_7777028 : Nat := 4983230072969 + 3 ^ 40 * 7777028 * 2
def baseEnd_7777028 : Nat := 1331117809158167858628035

theorem tailTrace_7777028 : CollatzResearch.WordTrace tailWord_7777028 prefixEnd_7777028 1331117809158167858628035 := by
  unfold tailWord_7777028
  simp only [CollatzResearch.WordTrace]
  refine ⟨141825757034581620741629869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189101009379442160988839825 141825757034581620741629869)
  ·
    refine ⟨53184658887968107778111201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141825757034581620741629869 53184658887968107778111201)
    ·
      refine ⟨39888494165976080833583401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53184658887968107778111201 39888494165976080833583401)
      ·
        refine ⟨29916370624482060625187551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39888494165976080833583401 29916370624482060625187551)
        ·
          refine ⟨44874555936723090937781327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29916370624482060625187551 44874555936723090937781327)
          ·
            refine ⟨67311833905084636406671991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44874555936723090937781327 67311833905084636406671991)
            ·
              refine ⟨100967750857626954610007987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67311833905084636406671991 100967750857626954610007987)
              ·
                refine ⟨151451626286440431915011981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100967750857626954610007987 151451626286440431915011981)
                ·
                  refine ⟨56794359857415161968129493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151451626286440431915011981 56794359857415161968129493)
                  ·
                    refine ⟨1331117809158167858628035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56794359857415161968129493 1331117809158167858628035)
                    ·
                      rfl

theorem cell23_7777028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_7777028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777028 prefixEnd_7777028 := by exact prefixLift 7777028
  have htrace : WordTrace (prefixWord ++ tailWord_7777028) baseStart_7777028 baseEnd_7777028 := by
    simpa [prefixWord, tailWord_7777028, baseEnd_7777028] using wordTrace_append hprefix tailTrace_7777028
  have hstable : (prefixWord ++ tailWord_7777028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777028).length < 2 ^ (prefixWord ++ tailWord_7777028).sum := by decide
  have hdescent : baseEnd_7777028 < baseStart_7777028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777038 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_7777038 : Nat := 118140960795 + 7777038 * 2 ^ 59
def prefixEnd_7777038 : Nat := 4983230072969 + 3 ^ 40 * 7777038 * 2
def baseEnd_7777038 : Nat := 3993358562281048536759059

theorem tailTrace_7777038 : CollatzResearch.WordTrace tailWord_7777038 prefixEnd_7777038 3993358562281048536759059 := by
  unfold tailWord_7777038
  simp only [CollatzResearch.WordTrace]
  refine ⟨35456484849890876648890471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189101252532751342127415845 35456484849890876648890471)
  ·
    refine ⟨53184727274836314973335707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35456484849890876648890471 53184727274836314973335707)
    ·
      refine ⟨79777090912254472460003561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53184727274836314973335707 79777090912254472460003561)
      ·
        refine ⟨59832818184190854345002671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79777090912254472460003561 59832818184190854345002671)
        ·
          refine ⟨89749227276286281517504007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59832818184190854345002671 89749227276286281517504007)
          ·
            refine ⟨134623840914429422276256011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89749227276286281517504007 134623840914429422276256011)
            ·
              refine ⟨201935761371644133414384017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134623840914429422276256011 201935761371644133414384017)
              ·
                refine ⟨151451821028733100060788013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201935761371644133414384017 151451821028733100060788013)
                ·
                  refine ⟨56794432885774912522795505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151451821028733100060788013 56794432885774912522795505)
                  ·
                    refine ⟨42595824664331184392096629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56794432885774912522795505 42595824664331184392096629)
                    ·
                      refine ⟨3993358562281048536759059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42595824664331184392096629 3993358562281048536759059)
                      ·
                        rfl

theorem cell23_7777038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_7777038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777038 prefixEnd_7777038 := by exact prefixLift 7777038
  have htrace : WordTrace (prefixWord ++ tailWord_7777038) baseStart_7777038 baseEnd_7777038 := by
    simpa [prefixWord, tailWord_7777038, baseEnd_7777038] using wordTrace_append hprefix tailTrace_7777038
  have hstable : (prefixWord ++ tailWord_7777038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777038).length < 2 ^ (prefixWord ++ tailWord_7777038).sum := by decide
  have hdescent : baseEnd_7777038 < baseStart_7777038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777066 : List Nat := [3, 1, 4, 3, 1, 1, 3, 2, 5]
def baseStart_7777066 : Nat := 118140960795 + 7777066 * 2 ^ 59
def prefixEnd_7777066 : Nat := 4983230072969 + 3 ^ 40 * 7777066 * 2
def baseEnd_7777066 : Nat := 443708104415486047467659

theorem tailTrace_7777066 : CollatzResearch.WordTrace tailWord_7777066 prefixEnd_7777066 443708104415486047467659 := by
  unfold tailWord_7777066
  simp only [CollatzResearch.WordTrace]
  refine ⟨70913225010756393493285763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189101933362017049315428701 70913225010756393493285763)
  ·
    refine ⟨106369837516134590239928645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70913225010756393493285763 106369837516134590239928645)
    ·
      refine ⟨19944344534275235669986621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106369837516134590239928645 19944344534275235669986621)
      ·
        refine ⟨7479129200353213376244983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19944344534275235669986621 7479129200353213376244983)
        ·
          refine ⟨11218693800529820064367475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479129200353213376244983 11218693800529820064367475)
          ·
            refine ⟨16828040700794730096551213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11218693800529820064367475 16828040700794730096551213)
            ·
              refine ⟨6310515262798023786206705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16828040700794730096551213 6310515262798023786206705)
              ·
                refine ⟨4732886447098517839655029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6310515262798023786206705 4732886447098517839655029)
                ·
                  refine ⟨443708104415486047467659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4732886447098517839655029 443708104415486047467659)
                  ·
                    rfl

theorem cell23_7777066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_7777066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777066 prefixEnd_7777066 := by exact prefixLift 7777066
  have htrace : WordTrace (prefixWord ++ tailWord_7777066) baseStart_7777066 baseEnd_7777066 := by
    simpa [prefixWord, tailWord_7777066, baseEnd_7777066] using wordTrace_append hprefix tailTrace_7777066
  have hstable : (prefixWord ++ tailWord_7777066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777066).length < 2 ^ (prefixWord ++ tailWord_7777066).sum := by decide
  have hdescent : baseEnd_7777066 < baseStart_7777066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777132 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_7777132 : Nat := 118140960795 + 7777132 * 2 ^ 59
def prefixEnd_7777132 : Nat := 4983230072969 + 3 ^ 40 * 7777132 * 2
def baseEnd_7777132 : Nat := 3993406829462571168983627

theorem tailTrace_7777132 : CollatzResearch.WordTrace tailWord_7777132 prefixEnd_7777132 3993406829462571168983627 := by
  unfold tailWord_7777132
  simp only [CollatzResearch.WordTrace]
  refine ⟨141827653630393233622522825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189103538173857644830030433 141827653630393233622522825)
  ·
    refine ⟨106370740222794925216892119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141827653630393233622522825 106370740222794925216892119)
    ·
      refine ⟨159556110334192387825338179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106370740222794925216892119 159556110334192387825338179)
      ·
        refine ⟨239334165501288581738007269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159556110334192387825338179 239334165501288581738007269)
        ·
          refine ⟨44875156031491609075876363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239334165501288581738007269 44875156031491609075876363)
          ·
            refine ⟨67312734047237413613814545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44875156031491609075876363 67312734047237413613814545)
            ·
              refine ⟨50484550535428060210360909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67312734047237413613814545 50484550535428060210360909)
              ·
                refine ⟨18931706450785522578885341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50484550535428060210360909 18931706450785522578885341)
                ·
                  refine ⟨7099389919044570967082003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18931706450785522578885341 7099389919044570967082003)
                  ·
                    refine ⟨10649084878566856450623005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7099389919044570967082003 10649084878566856450623005)
                    ·
                      refine ⟨3993406829462571168983627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10649084878566856450623005 3993406829462571168983627)
                      ·
                        rfl

theorem cell23_7777132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_7777132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777132 prefixEnd_7777132 := by exact prefixLift 7777132
  have htrace : WordTrace (prefixWord ++ tailWord_7777132) baseStart_7777132 baseEnd_7777132 := by
    simpa [prefixWord, tailWord_7777132, baseEnd_7777132] using wordTrace_append hprefix tailTrace_7777132
  have hstable : (prefixWord ++ tailWord_7777132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777132).length < 2 ^ (prefixWord ++ tailWord_7777132).sum := by decide
  have hdescent : baseEnd_7777132 < baseStart_7777132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777155 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 4]
def baseStart_7777155 : Nat := 118140960795 + 7777155 * 2 ^ 59
def prefixEnd_7777155 : Nat := 4983230072969 + 3 ^ 40 * 7777155 * 2
def baseEnd_7777155 : Nat := 3993418639517624578996021

theorem tailTrace_7777155 : CollatzResearch.WordTrace tailWord_7777155 prefixEnd_7777155 3993418639517624578996021 := by
  unfold tailWord_7777155
  simp only [CollatzResearch.WordTrace]
  refine ⟨283656146139703142173132919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189104097426468761448755279 283656146139703142173132919)
  ·
    refine ⟨425484219209554713259699379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283656146139703142173132919 425484219209554713259699379)
    ·
      refine ⟨638226328814332069889549069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425484219209554713259699379 638226328814332069889549069)
      ·
        refine ⟨239334873305374526208580901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638226328814332069889549069 239334873305374526208580901)
        ·
          refine ⟨44875288744757723664108919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239334873305374526208580901 44875288744757723664108919)
          ·
            refine ⟨67312933117136585496163379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44875288744757723664108919 67312933117136585496163379)
            ·
              refine ⟨100969399675704878244245069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67312933117136585496163379 100969399675704878244245069)
              ·
                refine ⟨37863524878389329341591901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100969399675704878244245069 37863524878389329341591901)
                ·
                  refine ⟨14198821829395998503096963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37863524878389329341591901 14198821829395998503096963)
                  ·
                    refine ⟨21298232744093997754645445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14198821829395998503096963 21298232744093997754645445)
                    ·
                      refine ⟨3993418639517624578996021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21298232744093997754645445 3993418639517624578996021)
                      ·
                        rfl

theorem cell23_7777155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_7777155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777155 prefixEnd_7777155 := by exact prefixLift 7777155
  have htrace : WordTrace (prefixWord ++ tailWord_7777155) baseStart_7777155 baseEnd_7777155 := by
    simpa [prefixWord, tailWord_7777155, baseEnd_7777155] using wordTrace_append hprefix tailTrace_7777155
  have hstable : (prefixWord ++ tailWord_7777155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777155).length < 2 ^ (prefixWord ++ tailWord_7777155).sum := by decide
  have hdescent : baseEnd_7777155 < baseStart_7777155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777159 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_7777159 : Nat := 118140960795 + 7777159 * 2 ^ 59
def prefixEnd_7777159 : Nat := 4983230072969 + 3 ^ 40 * 7777159 * 2
def baseEnd_7777159 : Nat := 3993420693440242563346003

theorem tailTrace_7777159 : CollatzResearch.WordTrace tailWord_7777159 prefixEnd_7777159 3993420693440242563346003 := by
  unfold tailWord_7777159
  simp only [CollatzResearch.WordTrace]
  refine ⟨283656292031688650856278531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189104194687792433904185687 283656292031688650856278531)
  ·
    refine ⟨425484438047532976284417797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283656292031688650856278531 425484438047532976284417797)
    ·
      refine ⟨79778332133912433053328337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425484438047532976284417797 79778332133912433053328337)
      ·
        refine ⟨59833749100434324789996253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79778332133912433053328337 59833749100434324789996253)
        ·
          refine ⟨22437655912662871796248595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59833749100434324789996253 22437655912662871796248595)
          ·
            refine ⟨33656483868994307694372893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22437655912662871796248595 33656483868994307694372893)
            ·
              refine ⟨12621181450872865385389835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33656483868994307694372893 12621181450872865385389835)
              ·
                refine ⟨18931772176309298078084753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12621181450872865385389835 18931772176309298078084753)
                ·
                  refine ⟨14198829132231973558563565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18931772176309298078084753 14198829132231973558563565)
                  ·
                    refine ⟨5324560924586990084461337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14198829132231973558563565 5324560924586990084461337)
                    ·
                      refine ⟨3993420693440242563346003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324560924586990084461337 3993420693440242563346003)
                      ·
                        rfl

theorem cell23_7777159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_7777159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777159 prefixEnd_7777159 := by exact prefixLift 7777159
  have htrace : WordTrace (prefixWord ++ tailWord_7777159) baseStart_7777159 baseEnd_7777159 := by
    simpa [prefixWord, tailWord_7777159, baseEnd_7777159] using wordTrace_append hprefix tailTrace_7777159
  have hstable : (prefixWord ++ tailWord_7777159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777159).length < 2 ^ (prefixWord ++ tailWord_7777159).sum := by decide
  have hdescent : baseEnd_7777159 < baseStart_7777159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777175 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_7777175 : Nat := 118140960795 + 7777175 * 2 ^ 59
def prefixEnd_7777175 : Nat := 4983230072969 + 3 ^ 40 * 7777175 * 2
def baseEnd_7777175 : Nat := 3993428909130714500745929

theorem tailTrace_7777175 : CollatzResearch.WordTrace tailWord_7777175 prefixEnd_7777175 3993428909130714500745929 := by
  unfold tailWord_7777175
  simp only [CollatzResearch.WordTrace]
  refine ⟨283656875599630685588860979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189104583733087123725907319 283656875599630685588860979)
  ·
    refine ⟨425485313399446028383291469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283656875599630685588860979 425485313399446028383291469)
    ·
      refine ⟨159556992524792260643734301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425485313399446028383291469 159556992524792260643734301)
      ·
        refine ⟨59833872196797097741400363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159556992524792260643734301 59833872196797097741400363)
        ·
          refine ⟨89750808295195646612100545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59833872196797097741400363 89750808295195646612100545)
          ·
            refine ⟨67313106221396734959075409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89750808295195646612100545 67313106221396734959075409)
            ·
              refine ⟨50484829666047551219306557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67313106221396734959075409 50484829666047551219306557)
              ·
                refine ⟨18931811124767831707239959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50484829666047551219306557 18931811124767831707239959)
                ·
                  refine ⟨28397716687151747560859939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18931811124767831707239959 28397716687151747560859939)
                  ·
                    refine ⟨42596575030727621341289909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28397716687151747560859939 42596575030727621341289909)
                    ·
                      refine ⟨3993428909130714500745929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42596575030727621341289909 3993428909130714500745929)
                      ·
                        rfl

theorem cell23_7777175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_7777175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777175 prefixEnd_7777175 := by exact prefixLift 7777175
  have htrace : WordTrace (prefixWord ++ tailWord_7777175) baseStart_7777175 baseEnd_7777175 := by
    simpa [prefixWord, tailWord_7777175, baseEnd_7777175] using wordTrace_append hprefix tailTrace_7777175
  have hstable : (prefixWord ++ tailWord_7777175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777175).length < 2 ^ (prefixWord ++ tailWord_7777175).sum := by decide
  have hdescent : baseEnd_7777175 < baseStart_7777175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777209 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 3]
def baseStart_7777209 : Nat := 118140960795 + 7777209 * 2 ^ 59
def prefixEnd_7777209 : Nat := 4983230072969 + 3 ^ 40 * 7777209 * 2
def baseEnd_7777209 : Nat := 3993446367472967367720773

theorem tailTrace_7777209 : CollatzResearch.WordTrace tailWord_7777209 prefixEnd_7777209 3993446367472967367720773 := by
  unfold tailWord_7777209
  simp only [CollatzResearch.WordTrace]
  refine ⟨283658115681507509395598681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189105410454338339597065787 283658115681507509395598681)
  ·
    refine ⟨212743586761130632046699011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283658115681507509395598681 212743586761130632046699011)
    ·
      refine ⟨319115380141695948070048517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212743586761130632046699011 319115380141695948070048517)
      ·
        refine ⟨59834133776567990263134097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319115380141695948070048517 59834133776567990263134097)
        ·
          refine ⟨44875600332425992697350573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59834133776567990263134097 44875600332425992697350573)
          ·
            refine ⟨16828350124659747261506465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44875600332425992697350573 16828350124659747261506465)
            ·
              refine ⟨12621262593494810446129849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16828350124659747261506465 12621262593494810446129849)
              ·
                refine ⟨9465946945121107834597387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12621262593494810446129849 9465946945121107834597387)
                ·
                  refine ⟨14198920417681661751896081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9465946945121107834597387 14198920417681661751896081)
                  ·
                    refine ⟨10649190313261246313922061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14198920417681661751896081 10649190313261246313922061)
                    ·
                      refine ⟨3993446367472967367720773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10649190313261246313922061 3993446367472967367720773)
                      ·
                        rfl

theorem cell23_7777209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_7777209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777209 prefixEnd_7777209 := by exact prefixLift 7777209
  have htrace : WordTrace (prefixWord ++ tailWord_7777209) baseStart_7777209 baseEnd_7777209 := by
    simpa [prefixWord, tailWord_7777209, baseEnd_7777209] using wordTrace_append hprefix tailTrace_7777209
  have hstable : (prefixWord ++ tailWord_7777209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777209).length < 2 ^ (prefixWord ++ tailWord_7777209).sum := by decide
  have hdescent : baseEnd_7777209 < baseStart_7777209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777232 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 5, 3, 2]
def baseStart_7777232 : Nat := 118140960795 + 7777232 * 2 ^ 59
def prefixEnd_7777232 : Nat := 4983230072969 + 3 ^ 40 * 7777232 * 2
def baseEnd_7777232 : Nat := 3993458177528020777733167

theorem tailTrace_7777232 : CollatzResearch.WordTrace tailWord_7777232 prefixEnd_7777232 3993458177528020777733167 := by
  unfold tailWord_7777232
  simp only [CollatzResearch.WordTrace]
  refine ⟨141829477280212092161842975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189105969706949456215790633 141829477280212092161842975)
  ·
    refine ⟨212744215920318138242764463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141829477280212092161842975 212744215920318138242764463)
    ·
      refine ⟨319116323880477207364146695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212744215920318138242764463 319116323880477207364146695)
      ·
        refine ⟨478674485820715811046220043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319116323880477207364146695 478674485820715811046220043)
        ·
          refine ⟨718011728731073716569330065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478674485820715811046220043 718011728731073716569330065)
          ·
            refine ⟨538508796548305287426997549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718011728731073716569330065 538508796548305287426997549)
            ·
              refine ⟨201940798705614482785124081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538508796548305287426997549 201940798705614482785124081)
              ·
                refine ⟨151455599029210862088843061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201940798705614482785124081 151455599029210862088843061)
                ·
                  refine ⟨14198962408988518320829037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151455599029210862088843061 14198962408988518320829037)
                  ·
                    refine ⟨5324610903370694370310889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14198962408988518320829037 5324610903370694370310889)
                    ·
                      refine ⟨3993458177528020777733167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324610903370694370310889 3993458177528020777733167)
                      ·
                        rfl

theorem cell23_7777232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 3, 2].length) (baseStart_7777232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777232 prefixEnd_7777232 := by exact prefixLift 7777232
  have htrace : WordTrace (prefixWord ++ tailWord_7777232) baseStart_7777232 baseEnd_7777232 := by
    simpa [prefixWord, tailWord_7777232, baseEnd_7777232] using wordTrace_append hprefix tailTrace_7777232
  have hstable : (prefixWord ++ tailWord_7777232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777232).length < 2 ^ (prefixWord ++ tailWord_7777232).sum := by decide
  have hdescent : baseEnd_7777232 < baseStart_7777232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777256 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_7777256 : Nat := 118140960795 + 7777256 * 2 ^ 59
def prefixEnd_7777256 : Nat := 4983230072969 + 3 ^ 40 * 7777256 * 2
def baseEnd_7777256 : Nat := 3993470501063728683833057

theorem tailTrace_7777256 : CollatzResearch.WordTrace tailWord_7777256 prefixEnd_7777256 3993470501063728683833057 := by
  unfold tailWord_7777256
  simp only [CollatzResearch.WordTrace]
  refine ⟨141829914956168618211279811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189106553274891490948373081 141829914956168618211279811)
  ·
    refine ⟨212744872434252927316919717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141829914956168618211279811 212744872434252927316919717)
    ·
      refine ⟨39889663581422423871922447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212744872434252927316919717 39889663581422423871922447)
      ·
        refine ⟨59834495372133635807883671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39889663581422423871922447 59834495372133635807883671)
        ·
          refine ⟨89751743058200453711825507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59834495372133635807883671 89751743058200453711825507)
          ·
            refine ⟨134627614587300680567738261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89751743058200453711825507 134627614587300680567738261)
            ·
              refine ⟨6310669433779719401612731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134627614587300680567738261 6310669433779719401612731)
              ·
                refine ⟨9466004150669579102419097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310669433779719401612731 9466004150669579102419097)
                ·
                  refine ⟨7099503113002184326814323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9466004150669579102419097 7099503113002184326814323)
                  ·
                    refine ⟨10649254669503276490221485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7099503113002184326814323 10649254669503276490221485)
                    ·
                      refine ⟨3993470501063728683833057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10649254669503276490221485 3993470501063728683833057)
                      ·
                        rfl

theorem cell23_7777256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_7777256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777256 prefixEnd_7777256 := by exact prefixLift 7777256
  have htrace : WordTrace (prefixWord ++ tailWord_7777256) baseStart_7777256 baseEnd_7777256 := by
    simpa [prefixWord, tailWord_7777256, baseEnd_7777256] using wordTrace_append hprefix tailTrace_7777256
  have hstable : (prefixWord ++ tailWord_7777256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777256).length < 2 ^ (prefixWord ++ tailWord_7777256).sum := by decide
  have hdescent : baseEnd_7777256 < baseStart_7777256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777275 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 4]
def baseStart_7777275 : Nat := 118140960795 + 7777275 * 2 ^ 59
def prefixEnd_7777275 : Nat := 4983230072969 + 3 ^ 40 * 7777275 * 2
def baseEnd_7777275 : Nat := 3993480257196164109495469

theorem tailTrace_7777275 : CollatzResearch.WordTrace tailWord_7777275 prefixEnd_7777275 3993480257196164109495469 := by
  unfold tailWord_7777275
  simp only [CollatzResearch.WordTrace]
  refine ⟨283660522899268402667501279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189107015266178935111667519 283660522899268402667501279)
  ·
    refine ⟨425490784348902604001251919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283660522899268402667501279 425490784348902604001251919)
    ·
      refine ⟨638236176523353906001877879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425490784348902604001251919 638236176523353906001877879)
      ·
        refine ⟨957354264785030859002816819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638236176523353906001877879 957354264785030859002816819)
        ·
          refine ⟨1436031397177546288504225229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957354264785030859002816819 1436031397177546288504225229)
          ·
            refine ⟨538511773941579858189084461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1436031397177546288504225229 538511773941579858189084461)
            ·
              refine ⟨201941915228092446820906673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538511773941579858189084461 201941915228092446820906673)
              ·
                refine ⟨151456436421069335115680005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201941915228092446820906673 151456436421069335115680005)
                ·
                  refine ⟨28398081828950500334190001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151456436421069335115680005 28398081828950500334190001)
                  ·
                    refine ⟨21298561371712875250642501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28398081828950500334190001 21298561371712875250642501)
                    ·
                      refine ⟨3993480257196164109495469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21298561371712875250642501 3993480257196164109495469)
                      ·
                        rfl

theorem cell23_7777275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 4].length) (baseStart_7777275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777275 prefixEnd_7777275 := by exact prefixLift 7777275
  have htrace : WordTrace (prefixWord ++ tailWord_7777275) baseStart_7777275 baseEnd_7777275 := by
    simpa [prefixWord, tailWord_7777275, baseEnd_7777275] using wordTrace_append hprefix tailTrace_7777275
  have hstable : (prefixWord ++ tailWord_7777275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777275).length < 2 ^ (prefixWord ++ tailWord_7777275).sum := by decide
  have hdescent : baseEnd_7777275 < baseStart_7777275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777309 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_7777309 : Nat := 118140960795 + 7777309 * 2 ^ 59
def prefixEnd_7777309 : Nat := 4983230072969 + 3 ^ 40 * 7777309 * 2
def baseEnd_7777309 : Nat := 3993497715538416976470313

theorem tailTrace_7777309 : CollatzResearch.WordTrace tailWord_7777309 prefixEnd_7777309 3993497715538416976470313 := by
  unfold tailWord_7777309
  simp only [CollatzResearch.WordTrace]
  refine ⟨283661762981145226474238981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189107841987430150982825987 283661762981145226474238981)
  ·
    refine ⟨53186580558964729963919809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283661762981145226474238981 53186580558964729963919809)
    ·
      refine ⟨39889935419223547472939857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53186580558964729963919809 39889935419223547472939857)
      ·
        refine ⟨29917451564417660604704893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39889935419223547472939857 29917451564417660604704893)
        ·
          refine ⟨11219044336656622726764335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29917451564417660604704893 11219044336656622726764335)
          ·
            refine ⟨16828566504984934090146503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11219044336656622726764335 16828566504984934090146503)
            ·
              refine ⟨25242849757477401135219755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16828566504984934090146503 25242849757477401135219755)
              ·
                refine ⟨37864274636216101702829633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25242849757477401135219755 37864274636216101702829633)
                ·
                  refine ⟨28398205977162076277122225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37864274636216101702829633 28398205977162076277122225)
                  ·
                    refine ⟨21298654482871557207841669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28398205977162076277122225 21298654482871557207841669)
                    ·
                      refine ⟨3993497715538416976470313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21298654482871557207841669 3993497715538416976470313)
                      ·
                        rfl

theorem cell23_7777309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_7777309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777309 prefixEnd_7777309 := by exact prefixLift 7777309
  have htrace : WordTrace (prefixWord ++ tailWord_7777309) baseStart_7777309 baseEnd_7777309 := by
    simpa [prefixWord, tailWord_7777309, baseEnd_7777309] using wordTrace_append hprefix tailTrace_7777309
  have hstable : (prefixWord ++ tailWord_7777309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777309).length < 2 ^ (prefixWord ++ tailWord_7777309).sum := by decide
  have hdescent : baseEnd_7777309 < baseStart_7777309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777319 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 7]
def baseStart_7777319 : Nat := 118140960795 + 7777319 * 2 ^ 59
def prefixEnd_7777319 : Nat := 4983230072969 + 3 ^ 40 * 7777319 * 2
def baseEnd_7777319 : Nat := 443722538927217993038363

theorem tailTrace_7777319 : CollatzResearch.WordTrace tailWord_7777319 prefixEnd_7777319 443722538927217993038363 := by
  unfold tailWord_7777319
  simp only [CollatzResearch.WordTrace]
  refine ⟨283662127711108998182103011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189108085140739332121402007 283662127711108998182103011)
  ·
    refine ⟨425493191566663497273154517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283662127711108998182103011 425493191566663497273154517)
    ·
      refine ⟨9972496677343675717339559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 425493191566663497273154517 9972496677343675717339559)
      ·
        refine ⟨14958745016015513576009339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9972496677343675717339559 14958745016015513576009339)
        ·
          refine ⟨22438117524023270364014009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14958745016015513576009339 22438117524023270364014009)
          ·
            refine ⟨16828588143017452773010507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22438117524023270364014009 16828588143017452773010507)
            ·
              refine ⟨25242882214526179159515761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16828588143017452773010507 25242882214526179159515761)
              ·
                refine ⟨18932161660894634369636821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25242882214526179159515761 18932161660894634369636821)
                ·
                  refine ⟨443722538927217993038363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18932161660894634369636821 443722538927217993038363)
                  ·
                    rfl

theorem cell23_7777319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 7].length) (baseStart_7777319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777319 prefixEnd_7777319 := by exact prefixLift 7777319
  have htrace : WordTrace (prefixWord ++ tailWord_7777319) baseStart_7777319 baseEnd_7777319 := by
    simpa [prefixWord, tailWord_7777319, baseEnd_7777319] using wordTrace_append hprefix tailTrace_7777319
  have hstable : (prefixWord ++ tailWord_7777319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777319).length < 2 ^ (prefixWord ++ tailWord_7777319).sum := by decide
  have hdescent : baseEnd_7777319 < baseStart_7777319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777352 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_7777352 : Nat := 118140960795 + 7777352 * 2 ^ 59
def prefixEnd_7777352 : Nat := 4983230072969 + 3 ^ 40 * 7777352 * 2
def baseEnd_7777352 : Nat := 3993519795206560308232615

theorem tailTrace_7777352 : CollatzResearch.WordTrace tailWord_7777352 prefixEnd_7777352 3993519795206560308232615 := by
  unfold tailWord_7777352
  simp only [CollatzResearch.WordTrace]
  refine ⟨141831665659994722409027155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189108887546659629878702873 141831665659994722409027155)
  ·
    refine ⟨212747498489992083613540733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141831665659994722409027155 212747498489992083613540733)
    ·
      refine ⟨79780311933747031355077775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212747498489992083613540733 79780311933747031355077775)
      ·
        refine ⟨119670467900620547032616663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79780311933747031355077775 119670467900620547032616663)
        ·
          refine ⟨179505701850930820548924995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119670467900620547032616663 179505701850930820548924995)
          ·
            refine ⟨269258552776396230823387493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179505701850930820548924995 269258552776396230823387493)
            ·
              refine ⟨50485978645574293279385155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269258552776396230823387493 50485978645574293279385155)
              ·
                refine ⟨75728967968361439919077733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50485978645574293279385155 75728967968361439919077733)
                ·
                  refine ⟨14199181494067769984827075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75728967968361439919077733 14199181494067769984827075)
                  ·
                    refine ⟨21298772241101654977240613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14199181494067769984827075 21298772241101654977240613)
                    ·
                      refine ⟨3993519795206560308232615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21298772241101654977240613 3993519795206560308232615)
                      ·
                        rfl

theorem cell23_7777352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_7777352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777352 prefixEnd_7777352 := by exact prefixLift 7777352
  have htrace : WordTrace (prefixWord ++ tailWord_7777352) baseStart_7777352 baseEnd_7777352 := by
    simpa [prefixWord, tailWord_7777352, baseEnd_7777352] using wordTrace_append hprefix tailTrace_7777352
  have hstable : (prefixWord ++ tailWord_7777352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777352).length < 2 ^ (prefixWord ++ tailWord_7777352).sum := by decide
  have hdescent : baseEnd_7777352 < baseStart_7777352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777389 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_7777389 : Nat := 118140960795 + 7777389 * 2 ^ 59
def prefixEnd_7777389 : Nat := 4983230072969 + 3 ^ 40 * 7777389 * 2
def baseEnd_7777389 : Nat := 3993538793990776663469945

theorem tailTrace_7777389 : CollatzResearch.WordTrace tailWord_7777389 prefixEnd_7777389 3993538793990776663469945 := by
  unfold tailWord_7777389
  simp only [CollatzResearch.WordTrace]
  refine ⟨283664680820855400137151221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189109787213903600091434147 283664680820855400137151221)
  ·
    refine ⟨26593563826955193762857927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283664680820855400137151221 26593563826955193762857927)
    ·
      refine ⟨39890345740432790644286891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26593563826955193762857927 39890345740432790644286891)
      ·
        refine ⟨59835518610649185966430337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39890345740432790644286891 59835518610649185966430337)
        ·
          refine ⟨44876638957986889474822753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59835518610649185966430337 44876638957986889474822753)
          ·
            refine ⟨33657479218490167106117065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44876638957986889474822753 33657479218490167106117065)
            ·
              refine ⟨25243109413867625329587799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33657479218490167106117065 25243109413867625329587799)
              ·
                refine ⟨37864664120801437994381699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25243109413867625329587799 37864664120801437994381699)
                ·
                  refine ⟨56796996181202156991572549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37864664120801437994381699 56796996181202156991572549)
                  ·
                    refine ⟨10649436783975404435919853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56796996181202156991572549 10649436783975404435919853)
                    ·
                      refine ⟨3993538793990776663469945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10649436783975404435919853 3993538793990776663469945)
                      ·
                        rfl

theorem cell23_7777389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_7777389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777389 prefixEnd_7777389 := by exact prefixLift 7777389
  have htrace : WordTrace (prefixWord ++ tailWord_7777389) baseStart_7777389 baseEnd_7777389 := by
    simpa [prefixWord, tailWord_7777389, baseEnd_7777389] using wordTrace_append hprefix tailTrace_7777389
  have hstable : (prefixWord ++ tailWord_7777389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777389).length < 2 ^ (prefixWord ++ tailWord_7777389).sum := by decide
  have hdescent : baseEnd_7777389 < baseStart_7777389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777413 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_7777413 : Nat := 118140960795 + 7777413 * 2 ^ 59
def prefixEnd_7777413 : Nat := 4983230072969 + 3 ^ 40 * 7777413 * 2
def baseEnd_7777413 : Nat := 1331183705842161523189945

theorem tailTrace_7777413 : CollatzResearch.WordTrace tailWord_7777413 prefixEnd_7777413 1331183705842161523189945 := by
  unfold tailWord_7777413
  simp only [CollatzResearch.WordTrace]
  refine ⟨283665556172768452236024893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189110370781845634824016595 283665556172768452236024893)
  ·
    refine ⟨106374583564788169588509335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283665556172768452236024893 106374583564788169588509335)
    ·
      refine ⟨159561875347182254382764003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106374583564788169588509335 159561875347182254382764003)
      ·
        refine ⟨239342813020773381574146005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159561875347182254382764003 239342813020773381574146005)
        ·
          refine ⟨5609597180174376130644047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 239342813020773381574146005 5609597180174376130644047)
          ·
            refine ⟨8414395770261564195966071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609597180174376130644047 8414395770261564195966071)
            ·
              refine ⟨12621593655392346293949107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8414395770261564195966071 12621593655392346293949107)
              ·
                refine ⟨18932390483088519440923661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12621593655392346293949107 18932390483088519440923661)
                ·
                  refine ⟨7099646431158194790346373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18932390483088519440923661 7099646431158194790346373)
                  ·
                    refine ⟨1331183705842161523189945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099646431158194790346373 1331183705842161523189945)
                    ·
                      rfl

theorem cell23_7777413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_7777413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777413 prefixEnd_7777413 := by exact prefixLift 7777413
  have htrace : WordTrace (prefixWord ++ tailWord_7777413) baseStart_7777413 baseEnd_7777413 := by
    simpa [prefixWord, tailWord_7777413, baseEnd_7777413] using wordTrace_append hprefix tailTrace_7777413
  have hstable : (prefixWord ++ tailWord_7777413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777413).length < 2 ^ (prefixWord ++ tailWord_7777413).sum := by decide
  have hdescent : baseEnd_7777413 < baseStart_7777413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777426 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 6]
def baseStart_7777426 : Nat := 118140960795 + 7777426 * 2 ^ 59
def prefixEnd_7777426 : Nat := 4983230072969 + 3 ^ 40 * 7777426 * 2
def baseEnd_7777426 : Nat := 443728643641665890967475

theorem tailTrace_7777426 : CollatzResearch.WordTrace tailWord_7777426 prefixEnd_7777426 443728643641665890967475 := by
  unfold tailWord_7777426
  simp only [CollatzResearch.WordTrace]
  refine ⟨70916507580430338864062033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189110686881147570304165421 70916507580430338864062033)
  ·
    refine ⟨53187380685322754148046525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70916507580430338864062033 53187380685322754148046525)
    ·
      refine ⟨19945267756996032805517447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53187380685322754148046525 19945267756996032805517447)
      ·
        refine ⟨29917901635494049208276171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19945267756996032805517447 29917901635494049208276171)
        ·
          refine ⟨44876852453241073812414257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29917901635494049208276171 44876852453241073812414257)
          ·
            refine ⟨33657639339930805359310693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44876852453241073812414257 33657639339930805359310693)
            ·
              refine ⟨6310807376237026004870755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33657639339930805359310693 6310807376237026004870755)
              ·
                refine ⟨9466211064355539007306133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310807376237026004870755 9466211064355539007306133)
                ·
                  refine ⟨443728643641665890967475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9466211064355539007306133 443728643641665890967475)
                  ·
                    rfl

theorem cell23_7777426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_7777426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777426 prefixEnd_7777426 := by exact prefixLift 7777426
  have htrace : WordTrace (prefixWord ++ tailWord_7777426) baseStart_7777426 baseEnd_7777426 := by
    simpa [prefixWord, tailWord_7777426, baseEnd_7777426] using wordTrace_append hprefix tailTrace_7777426
  have hstable : (prefixWord ++ tailWord_7777426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777426).length < 2 ^ (prefixWord ++ tailWord_7777426).sum := by decide
  have hdescent : baseEnd_7777426 < baseStart_7777426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777429 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_7777429 : Nat := 118140960795 + 7777429 * 2 ^ 59
def prefixEnd_7777429 : Nat := 4983230072969 + 3 ^ 40 * 7777429 * 2
def baseEnd_7777429 : Nat := 3993559333216956506969761

theorem tailTrace_7777429 : CollatzResearch.WordTrace tailWord_7777429 prefixEnd_7777429 3993559333216956506969761 := by
  unfold tailWord_7777429
  simp only [CollatzResearch.WordTrace]
  refine ⟨283666139740710486968607341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189110759827140324645738227 283666139740710486968607341)
  ·
    refine ⟨106374802402766432613227753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283666139740710486968607341 106374802402766432613227753)
    ·
      refine ⟨79781101802074824459920815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106374802402766432613227753 79781101802074824459920815)
      ·
        refine ⟨119671652703112236689881223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79781101802074824459920815 119671652703112236689881223)
        ·
          refine ⟨179507479054668355034821835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119671652703112236689881223 179507479054668355034821835)
          ·
            refine ⟨269261218582002532552232753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179507479054668355034821835 269261218582002532552232753)
            ·
              refine ⟨201945913936501899414174565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269261218582002532552232753 201945913936501899414174565)
              ·
                refine ⟨37864858863094106140157731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201945913936501899414174565 37864858863094106140157731)
                ·
                  refine ⟨56797288294641159210236597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37864858863094106140157731 56797288294641159210236597)
                  ·
                    refine ⟨5324745777622608675959681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56797288294641159210236597 5324745777622608675959681)
                    ·
                      refine ⟨3993559333216956506969761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324745777622608675959681 3993559333216956506969761)
                      ·
                        rfl

theorem cell23_7777429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_7777429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777429 prefixEnd_7777429 := by exact prefixLift 7777429
  have htrace : WordTrace (prefixWord ++ tailWord_7777429) baseStart_7777429 baseEnd_7777429 := by
    simpa [prefixWord, tailWord_7777429, baseEnd_7777429] using wordTrace_append hprefix tailTrace_7777429
  have hstable : (prefixWord ++ tailWord_7777429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777429).length < 2 ^ (prefixWord ++ tailWord_7777429).sum := by decide
  have hdescent : baseEnd_7777429 < baseStart_7777429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777459 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 4]
def baseStart_7777459 : Nat := 118140960795 + 7777459 * 2 ^ 59
def prefixEnd_7777459 : Nat := 4983230072969 + 3 ^ 40 * 7777459 * 2
def baseEnd_7777459 : Nat := 3993574737636591389594623

theorem tailTrace_7777459 : CollatzResearch.WordTrace tailWord_7777459 prefixEnd_7777459 3993574737636591389594623 := by
  unfold tailWord_7777459
  simp only [CollatzResearch.WordTrace]
  refine ⟨283667233930601802092199431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189111489287067868061466287 283667233930601802092199431)
  ·
    refine ⟨425500850895902703138299147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283667233930601802092199431 425500850895902703138299147)
    ·
      refine ⟨638251276343854054707448721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425500850895902703138299147 638251276343854054707448721)
      ·
        refine ⟨478688457257890541030586541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638251276343854054707448721 478688457257890541030586541)
        ·
          refine ⟨179508171471708952886469953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478688457257890541030586541 179508171471708952886469953)
          ·
            refine ⟨134631128603781714664852465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179508171471708952886469953 134631128603781714664852465)
            ·
              refine ⟨100973346452836285998639349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134631128603781714664852465 100973346452836285998639349)
              ·
                refine ⟨9466251229953401812372439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100973346452836285998639349 9466251229953401812372439)
                ·
                  refine ⟨14199376844930102718558659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9466251229953401812372439 14199376844930102718558659)
                  ·
                    refine ⟨21299065267395154077837989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14199376844930102718558659 21299065267395154077837989)
                    ·
                      refine ⟨3993574737636591389594623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21299065267395154077837989 3993574737636591389594623)
                      ·
                        rfl

theorem cell23_7777459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 4].length) (baseStart_7777459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777459 prefixEnd_7777459 := by exact prefixLift 7777459
  have htrace : WordTrace (prefixWord ++ tailWord_7777459) baseStart_7777459 baseEnd_7777459 := by
    simpa [prefixWord, tailWord_7777459, baseEnd_7777459] using wordTrace_append hprefix tailTrace_7777459
  have hstable : (prefixWord ++ tailWord_7777459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777459).length < 2 ^ (prefixWord ++ tailWord_7777459).sum := by decide
  have hdescent : baseEnd_7777459 < baseStart_7777459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777469 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_7777469 : Nat := 118140960795 + 7777469 * 2 ^ 59
def prefixEnd_7777469 : Nat := 4983230072969 + 3 ^ 40 * 7777469 * 2
def baseEnd_7777469 : Nat := 1331193290814378783489859

theorem tailTrace_7777469 : CollatzResearch.WordTrace tailWord_7777469 prefixEnd_7777469 1331193290814378783489859 := by
  unfold tailWord_7777469
  simp only [CollatzResearch.WordTrace]
  refine ⟨283667598660565573800063461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189111732440377049200042307 283667598660565573800063461)
  ·
    refine ⟨53187674748856045087511899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283667598660565573800063461 53187674748856045087511899)
    ·
      refine ⟨79781512123284067631267849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53187674748856045087511899 79781512123284067631267849)
      ·
        refine ⟨59836134092463050723450887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79781512123284067631267849 59836134092463050723450887)
        ·
          refine ⟨89754201138694576085176331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59836134092463050723450887 89754201138694576085176331)
          ·
            refine ⟨134631301708041864127764497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89754201138694576085176331 134631301708041864127764497)
            ·
              refine ⟨100973476281031398095823373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134631301708041864127764497 100973476281031398095823373)
              ·
                refine ⟨37865053605386774285933765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100973476281031398095823373 37865053605386774285933765)
                ·
                  refine ⟨7099697551010020178612581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37865053605386774285933765 7099697551010020178612581)
                  ·
                    refine ⟨1331193290814378783489859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099697551010020178612581 1331193290814378783489859)
                    ·
                      rfl

theorem cell23_7777469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_7777469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777469 prefixEnd_7777469 := by exact prefixLift 7777469
  have htrace : WordTrace (prefixWord ++ tailWord_7777469) baseStart_7777469 baseEnd_7777469 := by
    simpa [prefixWord, tailWord_7777469, baseEnd_7777469] using wordTrace_append hprefix tailTrace_7777469
  have hstable : (prefixWord ++ tailWord_7777469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777469).length < 2 ^ (prefixWord ++ tailWord_7777469).sum := by decide
  have hdescent : baseEnd_7777469 < baseStart_7777469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777470 : List Nat := [4, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_7777470 : Nat := 118140960795 + 7777470 * 2 ^ 59
def prefixEnd_7777470 : Nat := 4983230072969 + 3 ^ 40 * 7777470 * 2
def baseEnd_7777470 : Nat := 3993580385923790846557073

theorem tailTrace_7777470 : CollatzResearch.WordTrace tailWord_7777470 prefixEnd_7777470 3993580385923790846557073 := by
  unfold tailWord_7777470
  simp only [CollatzResearch.WordTrace]
  refine ⟨35458454391695243871356233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189111756755707967313899909 35458454391695243871356233)
  ·
    refine ⟨26593840793771432903517175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35458454391695243871356233 26593840793771432903517175)
    ·
      refine ⟨39890761190657149355275763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26593840793771432903517175 39890761190657149355275763)
      ·
        refine ⟨59836141785985724032913645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39890761190657149355275763 59836141785985724032913645)
        ·
          refine ⟨22438553169744646512342617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59836141785985724032913645 22438553169744646512342617)
          ·
            refine ⟨16828914877308484884256963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22438553169744646512342617 16828914877308484884256963)
            ·
              refine ⟨25243372315962727326385445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16828914877308484884256963 25243372315962727326385445)
              ·
                refine ⟨4733132309243011373697271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25243372315962727326385445 4733132309243011373697271)
                ·
                  refine ⟨7099698463864517060545907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733132309243011373697271 7099698463864517060545907)
                  ·
                    refine ⟨10649547695796775590818861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7099698463864517060545907 10649547695796775590818861)
                    ·
                      refine ⟨3993580385923790846557073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10649547695796775590818861 3993580385923790846557073)
                      ·
                        rfl

theorem cell23_7777470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_7777470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777470 prefixEnd_7777470 := by exact prefixLift 7777470
  have htrace : WordTrace (prefixWord ++ tailWord_7777470) baseStart_7777470 baseEnd_7777470 := by
    simpa [prefixWord, tailWord_7777470, baseEnd_7777470] using wordTrace_append hprefix tailTrace_7777470
  have hstable : (prefixWord ++ tailWord_7777470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777470).length < 2 ^ (prefixWord ++ tailWord_7777470).sum := by decide
  have hdescent : baseEnd_7777470 < baseStart_7777470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777486 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_7777486 : Nat := 118140960795 + 7777486 * 2 ^ 59
def prefixEnd_7777486 : Nat := 4983230072969 + 3 ^ 40 * 7777486 * 2
def baseEnd_7777486 : Nat := 1331196200538087594652333

theorem tailTrace_7777486 : CollatzResearch.WordTrace tailWord_7777486 prefixEnd_7777486 1331196200538087594652333 := by
  unfold tailWord_7777486
  simp only [CollatzResearch.WordTrace]
  refine ⟨35458527337687998212929039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189112145801002657135621541 35458527337687998212929039)
  ·
    refine ⟨53187791006531997319393559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35458527337687998212929039 53187791006531997319393559)
    ·
      refine ⟨79781686509797995979090339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53187791006531997319393559 79781686509797995979090339)
      ·
        refine ⟨119672529764696993968635509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79781686509797995979090339 119672529764696993968635509)
        ·
          refine ⟨11219299665440343184559579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119672529764696993968635509 11219299665440343184559579)
          ·
            refine ⟨16828949498160514776839369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11219299665440343184559579 16828949498160514776839369)
            ·
              refine ⟨12621712123620386082629527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16828949498160514776839369 12621712123620386082629527)
              ·
                refine ⟨18932568185430579123944291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12621712123620386082629527 18932568185430579123944291)
                ·
                  refine ⟨28398852278145868685916437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18932568185430579123944291 28398852278145868685916437)
                  ·
                    refine ⟨1331196200538087594652333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28398852278145868685916437 1331196200538087594652333)
                    ·
                      rfl

theorem cell23_7777486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_7777486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777486 prefixEnd_7777486 := by exact prefixLift 7777486
  have htrace : WordTrace (prefixWord ++ tailWord_7777486) baseStart_7777486 baseEnd_7777486 := by
    simpa [prefixWord, tailWord_7777486, baseEnd_7777486] using wordTrace_append hprefix tailTrace_7777486
  have hstable : (prefixWord ++ tailWord_7777486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777486).length < 2 ^ (prefixWord ++ tailWord_7777486).sum := by decide
  have hdescent : baseEnd_7777486 < baseStart_7777486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777493 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7777493 : Nat := 118140960795 + 7777493 * 2 ^ 59
def prefixEnd_7777493 : Nat := 4983230072969 + 3 ^ 40 * 7777493 * 2
def baseEnd_7777493 : Nat := 3993592195978844256569467

theorem tailTrace_7777493 : CollatzResearch.WordTrace tailWord_7777493 prefixEnd_7777493 3993592195978844256569467 := by
  unfold tailWord_7777493
  simp only [CollatzResearch.WordTrace]
  refine ⟨283668474012478625898937133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189112316008319083932624755 283668474012478625898937133)
  ·
    refine ⟨106375677754679484712101425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283668474012478625898937133 106375677754679484712101425)
    ·
      refine ⟨79781758316009613534076069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106375677754679484712101425 79781758316009613534076069)
      ·
        refine ⟨14959079684251802537639263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79781758316009613534076069 14959079684251802537639263)
        ·
          refine ⟨22438619526377703806458895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14959079684251802537639263 22438619526377703806458895)
          ·
            refine ⟨33657929289566555709688343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22438619526377703806458895 33657929289566555709688343)
            ·
              refine ⟨50486893934349833564532515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33657929289566555709688343 50486893934349833564532515)
              ·
                refine ⟨75730340901524750346798773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50486893934349833564532515 75730340901524750346798773)
                ·
                  refine ⟨7099719459517945345012385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75730340901524750346798773 7099719459517945345012385)
                  ·
                    refine ⟨5324789594638459008759289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7099719459517945345012385 5324789594638459008759289)
                    ·
                      refine ⟨3993592195978844256569467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324789594638459008759289 3993592195978844256569467)
                      ·
                        rfl

theorem cell23_7777493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7777493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777493 prefixEnd_7777493 := by exact prefixLift 7777493
  have htrace : WordTrace (prefixWord ++ tailWord_7777493) baseStart_7777493 baseEnd_7777493 := by
    simpa [prefixWord, tailWord_7777493, baseEnd_7777493] using wordTrace_append hprefix tailTrace_7777493
  have hstable : (prefixWord ++ tailWord_7777493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777493).length < 2 ^ (prefixWord ++ tailWord_7777493).sum := by decide
  have hdescent : baseEnd_7777493 < baseStart_7777493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777553 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 1, 3, 2]
def baseStart_7777553 : Nat := 118140960795 + 7777553 * 2 ^ 59
def prefixEnd_7777553 : Nat := 4983230072969 + 3 ^ 40 * 7777553 * 2
def baseEnd_7777553 : Nat := 3993623004818114021819191

theorem tailTrace_7777553 : CollatzResearch.WordTrace tailWord_7777553 prefixEnd_7777553 3993623004818114021819191 := by
  unfold tailWord_7777553
  simp only [CollatzResearch.WordTrace]
  refine ⟨283670662392261256146121313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189113774928174170764080875 283670662392261256146121313)
  ·
    refine ⟨212752996794195942109590985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283670662392261256146121313 212752996794195942109590985)
    ·
      refine ⟨159564747595646956582193239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212752996794195942109590985 159564747595646956582193239)
      ·
        refine ⟨239347121393470434873289859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159564747595646956582193239 239347121393470434873289859)
        ·
          refine ⟨359020682090205652309934789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239347121393470434873289859 359020682090205652309934789)
          ·
            refine ⟨67316377891913559808112773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359020682090205652309934789 67316377891913559808112773)
            ·
              refine ⟨12621820854733792464021145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67316377891913559808112773 12621820854733792464021145)
              ·
                refine ⟨9466365641050344348015859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12621820854733792464021145 9466365641050344348015859)
                ·
                  refine ⟨14199548461575516522023789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9466365641050344348015859 14199548461575516522023789)
                  ·
                    refine ⟨5324830673090818695758921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14199548461575516522023789 5324830673090818695758921)
                    ·
                      refine ⟨3993623004818114021819191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324830673090818695758921 3993623004818114021819191)
                      ·
                        rfl

theorem cell23_7777553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_7777553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777553 prefixEnd_7777553 := by exact prefixLift 7777553
  have htrace : WordTrace (prefixWord ++ tailWord_7777553) baseStart_7777553 baseEnd_7777553 := by
    simpa [prefixWord, tailWord_7777553, baseEnd_7777553] using wordTrace_append hprefix tailTrace_7777553
  have hstable : (prefixWord ++ tailWord_7777553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777553).length < 2 ^ (prefixWord ++ tailWord_7777553).sum := by decide
  have hdescent : baseEnd_7777553 < baseStart_7777553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777569 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_7777569 : Nat := 118140960795 + 7777569 * 2 ^ 59
def prefixEnd_7777569 : Nat := 4983230072969 + 3 ^ 40 * 7777569 * 2
def baseEnd_7777569 : Nat := 3993631220508585959219117

theorem tailTrace_7777569 : CollatzResearch.WordTrace tailWord_7777569 prefixEnd_7777569 3993631220508585959219117 := by
  unfold tailWord_7777569
  simp only [CollatzResearch.WordTrace]
  refine ⟨283671245960203290878703761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189114163973468860585802507 283671245960203290878703761)
  ·
    refine ⟨212753434470152468159027821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283671245960203290878703761 212753434470152468159027821)
    ·
      refine ⟨79782537926307175559635433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212753434470152468159027821 79782537926307175559635433)
      ·
        refine ⟨59836903444730381669726575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79782537926307175559635433 59836903444730381669726575)
        ·
          refine ⟨89755355167095572504589863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59836903444730381669726575 89755355167095572504589863)
          ·
            refine ⟨134633032750643358756884795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89755355167095572504589863 134633032750643358756884795)
            ·
              refine ⟨201949549125965038135327193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134633032750643358756884795 201949549125965038135327193)
              ·
                refine ⟨151462161844473778601495395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201949549125965038135327193 151462161844473778601495395)
                ·
                  refine ⟨227193242766710667902243093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151462161844473778601495395 227193242766710667902243093)
                  ·
                    refine ⟨10649683254689562557917645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 227193242766710667902243093 10649683254689562557917645)
                    ·
                      refine ⟨3993631220508585959219117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10649683254689562557917645 3993631220508585959219117)
                      ·
                        rfl

theorem cell23_7777569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_7777569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777569 prefixEnd_7777569 := by exact prefixLift 7777569
  have htrace : WordTrace (prefixWord ++ tailWord_7777569) baseStart_7777569 baseEnd_7777569 := by
    simpa [prefixWord, tailWord_7777569, baseEnd_7777569] using wordTrace_append hprefix tailTrace_7777569
  have hstable : (prefixWord ++ tailWord_7777569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777569).length < 2 ^ (prefixWord ++ tailWord_7777569).sum := by decide
  have hdescent : baseEnd_7777569 < baseStart_7777569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777583 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 2, 2, 2]
def baseStart_7777583 : Nat := 118140960795 + 7777583 * 2 ^ 59
def prefixEnd_7777583 : Nat := 4983230072969 + 3 ^ 40 * 7777583 * 2
def baseEnd_7777583 : Nat := 3993638409237748904444053

theorem tailTrace_7777583 : CollatzResearch.WordTrace tailWord_7777583 prefixEnd_7777583 3993638409237748904444053 := by
  unfold tailWord_7777583
  simp only [CollatzResearch.WordTrace]
  refine ⟨283671756582152571269713403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189114504388101714179808935 283671756582152571269713403)
  ·
    refine ⟨425507634873228856904570105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283671756582152571269713403 425507634873228856904570105)
    ·
      refine ⟨319130726154921642678427579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425507634873228856904570105 319130726154921642678427579)
      ·
        refine ⟨478696089232382464017641369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319130726154921642678427579 478696089232382464017641369)
        ·
          refine ⟨359022066924286848013231027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478696089232382464017641369 359022066924286848013231027)
          ·
            refine ⟨538533100386430272019846541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359022066924286848013231027 538533100386430272019846541)
            ·
              refine ⟨201949912644911352007442453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538533100386430272019846541 201949912644911352007442453)
              ·
                refine ⟨9466402155230219625348865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201949912644911352007442453 9466402155230219625348865)
                ·
                  refine ⟨7099801616422664719011649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9466402155230219625348865 7099801616422664719011649)
                  ·
                    refine ⟨5324851212316998539258737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7099801616422664719011649 5324851212316998539258737)
                    ·
                      refine ⟨3993638409237748904444053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324851212316998539258737 3993638409237748904444053)
                      ·
                        rfl

theorem cell23_7777583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 2, 2].length) (baseStart_7777583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777583 prefixEnd_7777583 := by exact prefixLift 7777583
  have htrace : WordTrace (prefixWord ++ tailWord_7777583) baseStart_7777583 baseEnd_7777583 := by
    simpa [prefixWord, tailWord_7777583, baseEnd_7777583] using wordTrace_append hprefix tailTrace_7777583
  have hstable : (prefixWord ++ tailWord_7777583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777583).length < 2 ^ (prefixWord ++ tailWord_7777583).sum := by decide
  have hdescent : baseEnd_7777583 < baseStart_7777583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777636 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_7777636 : Nat := 118140960795 + 7777636 * 2 ^ 59
def prefixEnd_7777636 : Nat := 4983230072969 + 3 ^ 40 * 7777636 * 2
def baseEnd_7777636 : Nat := 1331221874570812399027103

theorem tailTrace_7777636 : CollatzResearch.WordTrace tailWord_7777636 prefixEnd_7777636 1331221874570812399027103 := by
  unfold tailWord_7777636
  simp only [CollatzResearch.WordTrace]
  refine ⟨141836844825480280660696381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189115793100640374214261841 141836844825480280660696381)
  ·
    refine ⟨53188816809555105247761143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141836844825480280660696381 53188816809555105247761143)
    ·
      refine ⟨79783225214332657871641715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53188816809555105247761143 79783225214332657871641715)
      ·
        refine ⟨119674837821498986807462573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79783225214332657871641715 119674837821498986807462573)
        ·
          refine ⟨44878064183062120052798465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119674837821498986807462573 44878064183062120052798465)
          ·
            refine ⟨33658548137296590039598849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44878064183062120052798465 33658548137296590039598849)
            ·
              refine ⟨25243911102972442529699137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33658548137296590039598849 25243911102972442529699137)
              ·
                refine ⟨18932933327229331897274353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25243911102972442529699137 18932933327229331897274353)
                ·
                  refine ⟨14199699995421998922955765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18932933327229331897274353 14199699995421998922955765)
                  ·
                    refine ⟨1331221874570812399027103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14199699995421998922955765 1331221874570812399027103)
                    ·
                      rfl

theorem cell23_7777636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_7777636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777636 prefixEnd_7777636 := by exact prefixLift 7777636
  have htrace : WordTrace (prefixWord ++ tailWord_7777636) baseStart_7777636 baseEnd_7777636 := by
    simpa [prefixWord, tailWord_7777636, baseEnd_7777636] using wordTrace_append hprefix tailTrace_7777636
  have hstable : (prefixWord ++ tailWord_7777636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777636).length < 2 ^ (prefixWord ++ tailWord_7777636).sum := by decide
  have hdescent : baseEnd_7777636 < baseStart_7777636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777676 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_7777676 : Nat := 118140960795 + 7777676 * 2 ^ 59
def prefixEnd_7777676 : Nat := 4983230072969 + 3 ^ 40 * 7777676 * 2
def baseEnd_7777676 : Nat := 3993686162938617040581125

theorem tailTrace_7777676 : CollatzResearch.WordTrace tailWord_7777676 prefixEnd_7777676 3993686162938617040581125 := by
  unfold tailWord_7777676
  simp only [CollatzResearch.WordTrace]
  refine ⟨141837574285407824076424441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189116765713877098768565921 141837574285407824076424441)
  ·
    refine ⟨106378180714055868057318331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141837574285407824076424441 106378180714055868057318331)
    ·
      refine ⟨159567271071083802085977497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106378180714055868057318331 159567271071083802085977497)
      ·
        refine ⟨119675453303312851564483123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159567271071083802085977497 119675453303312851564483123)
        ·
          refine ⟨179513179954969277346724685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119675453303312851564483123 179513179954969277346724685)
          ·
            refine ⟨67317442483113479005021757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179513179954969277346724685 67317442483113479005021757)
            ·
              refine ⟨25244040931167554626883159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67317442483113479005021757 25244040931167554626883159)
              ·
                refine ⟨37866061396751331940324739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25244040931167554626883159 37866061396751331940324739)
                ·
                  refine ⟨56799092095126997910487109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37866061396751331940324739 56799092095126997910487109)
                  ·
                    refine ⟨10649829767836312108216333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56799092095126997910487109 10649829767836312108216333)
                    ·
                      refine ⟨3993686162938617040581125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10649829767836312108216333 3993686162938617040581125)
                      ·
                        rfl

theorem cell23_7777676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_7777676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777676 prefixEnd_7777676 := by exact prefixLift 7777676
  have htrace : WordTrace (prefixWord ++ tailWord_7777676) baseStart_7777676 baseEnd_7777676 := by
    simpa [prefixWord, tailWord_7777676, baseEnd_7777676] using wordTrace_append hprefix tailTrace_7777676
  have hstable : (prefixWord ++ tailWord_7777676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777676).length < 2 ^ (prefixWord ++ tailWord_7777676).sum := by decide
  have hdescent : baseEnd_7777676 < baseStart_7777676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777699 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 8]
def baseStart_7777699 : Nat := 118140960795 + 7777699 * 2 ^ 59
def prefixEnd_7777699 : Nat := 4983230072969 + 3 ^ 40 * 7777699 * 2
def baseEnd_7777699 : Nat := 3993697972993670450593519

theorem tailTrace_7777699 : CollatzResearch.WordTrace tailWord_7777699 prefixEnd_7777699 3993697972993670450593519 := by
  unfold tailWord_7777699
  simp only [CollatzResearch.WordTrace]
  refine ⟨283675987449732323080936151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189117324966488215387290767 283675987449732323080936151)
  ·
    refine ⟨425513981174598484621404227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283675987449732323080936151 425513981174598484621404227)
    ·
      refine ⟨638270971761897726932106341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425513981174598484621404227 638270971761897726932106341)
      ·
        refine ⟨119675807205355823799769939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 638270971761897726932106341 119675807205355823799769939)
        ·
          refine ⟨179513710808033735699654909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119675807205355823799769939 179513710808033735699654909)
          ·
            refine ⟨67317641553012650887370591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179513710808033735699654909 67317641553012650887370591)
            ·
              refine ⟨100976462329518976331055887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67317641553012650887370591 100976462329518976331055887)
              ·
                refine ⟨151464693494278464496583831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100976462329518976331055887 151464693494278464496583831)
                ·
                  refine ⟨227197040241417696744875747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151464693494278464496583831 227197040241417696744875747)
                  ·
                    refine ⟨340795560362126545117313621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227197040241417696744875747 340795560362126545117313621)
                    ·
                      refine ⟨3993697972993670450593519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 340795560362126545117313621 3993697972993670450593519)
                      ·
                        rfl

theorem cell23_7777699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_7777699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777699 prefixEnd_7777699 := by exact prefixLift 7777699
  have htrace : WordTrace (prefixWord ++ tailWord_7777699) baseStart_7777699 baseEnd_7777699 := by
    simpa [prefixWord, tailWord_7777699, baseEnd_7777699] using wordTrace_append hprefix tailTrace_7777699
  have hstable : (prefixWord ++ tailWord_7777699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777699).length < 2 ^ (prefixWord ++ tailWord_7777699).sum := by decide
  have hdescent : baseEnd_7777699 < baseStart_7777699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777713 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 6]
def baseStart_7777713 : Nat := 118140960795 + 7777713 * 2 ^ 59
def prefixEnd_7777713 : Nat := 4983230072969 + 3 ^ 40 * 7777713 * 2
def baseEnd_7777713 : Nat := 443745017969203710646495

theorem tailTrace_7777713 : CollatzResearch.WordTrace tailWord_7777713 prefixEnd_7777713 443745017969203710646495 := by
  unfold tailWord_7777713
  simp only [CollatzResearch.WordTrace]
  refine ⟨283676498071681603471945793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189117665381121068981297195 283676498071681603471945793)
  ·
    refine ⟨212757373553761202603959345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283676498071681603471945793 212757373553761202603959345)
    ·
      refine ⟨159568030165320901952969509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212757373553761202603959345 159568030165320901952969509)
      ·
        refine ⟨29919005655997669116181783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159568030165320901952969509 29919005655997669116181783)
        ·
          refine ⟨44878508483996503674272675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29919005655997669116181783 44878508483996503674272675)
          ·
            refine ⟨67317762725994755511409013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44878508483996503674272675 67317762725994755511409013)
            ·
              refine ⟨6311040255562008329194595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67317762725994755511409013 6311040255562008329194595)
              ·
                refine ⟨9466560383343012493791893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311040255562008329194595 9466560383343012493791893)
                ·
                  refine ⟨443745017969203710646495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9466560383343012493791893 443745017969203710646495)
                  ·
                    rfl

theorem cell23_7777713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 6].length) (baseStart_7777713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777713 prefixEnd_7777713 := by exact prefixLift 7777713
  have htrace : WordTrace (prefixWord ++ tailWord_7777713) baseStart_7777713 baseEnd_7777713 := by
    simpa [prefixWord, tailWord_7777713, baseEnd_7777713] using wordTrace_append hprefix tailTrace_7777713
  have hstable : (prefixWord ++ tailWord_7777713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777713).length < 2 ^ (prefixWord ++ tailWord_7777713).sum := by decide
  have hdescent : baseEnd_7777713 < baseStart_7777713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777757 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_7777757 : Nat := 118140960795 + 7777757 * 2 ^ 59
def prefixEnd_7777757 : Nat := 4983230072969 + 3 ^ 40 * 7777757 * 2
def baseEnd_7777757 : Nat := 3993727754871631223668253

theorem tailTrace_7777757 : CollatzResearch.WordTrace tailWord_7777757 prefixEnd_7777757 3993727754871631223668253 := by
  unfold tailWord_7777757
  simp only [CollatzResearch.WordTrace]
  refine ⟨283678102883522198986547525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189118735255681465991031683 283678102883522198986547525)
  ·
    refine ⟨53189644290660412309977661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283678102883522198986547525 53189644290660412309977661)
    ·
      refine ⟨19946116608997654616241623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53189644290660412309977661 19946116608997654616241623)
      ·
        refine ⟨29919174913496481924362435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19946116608997654616241623 29919174913496481924362435)
        ·
          refine ⟨44878762370244722886543653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29919174913496481924362435 44878762370244722886543653)
          ·
            refine ⟨8414767944420885541226935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44878762370244722886543653 8414767944420885541226935)
            ·
              refine ⟨12622151916631328311840403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8414767944420885541226935 12622151916631328311840403)
              ·
                refine ⟨18933227874946992467760605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12622151916631328311840403 18933227874946992467760605)
                ·
                  refine ⟨7099960453105122175410227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18933227874946992467760605 7099960453105122175410227)
                  ·
                    refine ⟨10649940679657683263115341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7099960453105122175410227 10649940679657683263115341)
                    ·
                      refine ⟨3993727754871631223668253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10649940679657683263115341 3993727754871631223668253)
                      ·
                        rfl

theorem cell23_7777757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_7777757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777757 prefixEnd_7777757 := by exact prefixLift 7777757
  have htrace : WordTrace (prefixWord ++ tailWord_7777757) baseStart_7777757 baseEnd_7777757 := by
    simpa [prefixWord, tailWord_7777757, baseEnd_7777757] using wordTrace_append hprefix tailTrace_7777757
  have hstable : (prefixWord ++ tailWord_7777757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777757).length < 2 ^ (prefixWord ++ tailWord_7777757).sum := by decide
  have hdescent : baseEnd_7777757 < baseStart_7777757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777776 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_7777776 : Nat := 118140960795 + 7777776 * 2 ^ 59
def prefixEnd_7777776 : Nat := 4983230072969 + 3 ^ 40 * 7777776 * 2
def baseEnd_7777776 : Nat := 3993737511004066649330665

theorem tailTrace_7777776 : CollatzResearch.WordTrace tailWord_7777776 prefixEnd_7777776 3993737511004066649330665 := by
  unfold tailWord_7777776
  simp only [CollatzResearch.WordTrace]
  refine ⟨141839397935226682615744591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189119197246968910154326121 141839397935226682615744591)
  ·
    refine ⟨212759096902840023923616887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141839397935226682615744591 212759096902840023923616887)
    ·
      refine ⟨319138645354260035885425331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212759096902840023923616887 319138645354260035885425331)
      ·
        refine ⟨478707968031390053828137997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319138645354260035885425331 478707968031390053828137997)
        ·
          refine ⟨179515488011771270185551749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478707968031390053828137997 179515488011771270185551749)
          ·
            refine ⟨33659154002207113159790953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179515488011771270185551749 33659154002207113159790953)
            ·
              refine ⟨25244365501655334869843215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33659154002207113159790953 25244365501655334869843215)
              ·
                refine ⟨37866548252483002304764823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25244365501655334869843215 37866548252483002304764823)
                ·
                  refine ⟨56799822378724503457147235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37866548252483002304764823 56799822378724503457147235)
                  ·
                    refine ⟨85199733568086755185720853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56799822378724503457147235 85199733568086755185720853)
                    ·
                      refine ⟨3993737511004066649330665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85199733568086755185720853 3993737511004066649330665)
                      ·
                        rfl

theorem cell23_7777776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_7777776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777776 prefixEnd_7777776 := by exact prefixLift 7777776
  have htrace : WordTrace (prefixWord ++ tailWord_7777776) baseStart_7777776 baseEnd_7777776 := by
    simpa [prefixWord, tailWord_7777776, baseEnd_7777776] using wordTrace_append hprefix tailTrace_7777776
  have hstable : (prefixWord ++ tailWord_7777776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777776).length < 2 ^ (prefixWord ++ tailWord_7777776).sum := by decide
  have hdescent : baseEnd_7777776 < baseStart_7777776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777783 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_7777783 : Nat := 118140960795 + 7777783 * 2 ^ 59
def prefixEnd_7777783 : Nat := 4983230072969 + 3 ^ 40 * 7777783 * 2
def baseEnd_7777783 : Nat := 3993741105368648121943133

theorem tailTrace_7777783 : CollatzResearch.WordTrace tailWord_7777783 prefixEnd_7777783 3993741105368648121943133 := by
  unfold tailWord_7777783
  simp only [CollatzResearch.WordTrace]
  refine ⟨283679051181428005426994003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189119367454285336951329335 283679051181428005426994003)
  ·
    refine ⟨425518576772142008140491005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283679051181428005426994003 425518576772142008140491005)
    ·
      refine ⟨159569466289553253052684127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425518576772142008140491005 159569466289553253052684127)
      ·
        refine ⟨239354199434329879579026191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159569466289553253052684127 239354199434329879579026191)
        ·
          refine ⟨359031299151494819368539287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239354199434329879579026191 359031299151494819368539287)
          ·
            refine ⟨538546948727242229052808931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359031299151494819368539287 538546948727242229052808931)
            ·
              refine ⟨807820423090863343579213397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538546948727242229052808931 807820423090863343579213397)
              ·
                refine ⟨9466645583096054807568907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 807820423090863343579213397 9466645583096054807568907)
                ·
                  refine ⟨14199968374644082211353361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9466645583096054807568907 14199968374644082211353361)
                  ·
                    refine ⟨10649976280983061658515021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14199968374644082211353361 10649976280983061658515021)
                    ·
                      refine ⟨3993741105368648121943133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10649976280983061658515021 3993741105368648121943133)
                      ·
                        rfl

theorem cell23_7777783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_7777783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777783 prefixEnd_7777783 := by exact prefixLift 7777783
  have htrace : WordTrace (prefixWord ++ tailWord_7777783) baseStart_7777783 baseEnd_7777783 := by
    simpa [prefixWord, tailWord_7777783, baseEnd_7777783] using wordTrace_append hprefix tailTrace_7777783
  have hstable : (prefixWord ++ tailWord_7777783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777783).length < 2 ^ (prefixWord ++ tailWord_7777783).sum := by decide
  have hdescent : baseEnd_7777783 < baseStart_7777783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777797 : List Nat := [1, 3, 1, 1, 2, 2, 1, 7, 1, 2, 2]
def baseStart_7777797 : Nat := 118140960795 + 7777797 * 2 ^ 59
def prefixEnd_7777797 : Nat := 4983230072969 + 3 ^ 40 * 7777797 * 2
def baseEnd_7777797 : Nat := 3993748294097811067168069

theorem tailTrace_7777797 : CollatzResearch.WordTrace tailWord_7777797 prefixEnd_7777797 3993748294097811067168069 := by
  unfold tailWord_7777797
  simp only [CollatzResearch.WordTrace]
  refine ⟨283679561803377285818003645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189119707868918190545335763 283679561803377285818003645)
  ·
    refine ⟨106379835676266482181751367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283679561803377285818003645 106379835676266482181751367)
    ·
      refine ⟨159569753514399723272627051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106379835676266482181751367 159569753514399723272627051)
      ·
        refine ⟨239354630271599584908940577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159569753514399723272627051 239354630271599584908940577)
        ·
          refine ⟨179515972703699688681705433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239354630271599584908940577 179515972703699688681705433)
          ·
            refine ⟨134636979527774766511279075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179515972703699688681705433 134636979527774766511279075)
            ·
              refine ⟨201955469291662149766918613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134636979527774766511279075 201955469291662149766918613)
              ·
                refine ⟨4733331311523331635162155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201955469291662149766918613 4733331311523331635162155)
                ·
                  refine ⟨7099996967284997452743233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733331311523331635162155 7099996967284997452743233)
                  ·
                    refine ⟨5324997725463748089557425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7099996967284997452743233 5324997725463748089557425)
                    ·
                      refine ⟨3993748294097811067168069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5324997725463748089557425 3993748294097811067168069)
                      ·
                        rfl

theorem cell23_7777797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_7777797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777797 prefixEnd_7777797 := by exact prefixLift 7777797
  have htrace : WordTrace (prefixWord ++ tailWord_7777797) baseStart_7777797 baseEnd_7777797 := by
    simpa [prefixWord, tailWord_7777797, baseEnd_7777797] using wordTrace_append hprefix tailTrace_7777797
  have hstable : (prefixWord ++ tailWord_7777797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777797).length < 2 ^ (prefixWord ++ tailWord_7777797).sum := by decide
  have hdescent : baseEnd_7777797 < baseStart_7777797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777840 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 1, 3, 2]
def baseStart_7777840 : Nat := 118140960795 + 7777840 * 2 ^ 59
def prefixEnd_7777840 : Nat := 4983230072969 + 3 ^ 40 * 7777840 * 2
def baseEnd_7777840 : Nat := 3993770373765954398930371

theorem tailTrace_7777840 : CollatzResearch.WordTrace tailWord_7777840 prefixEnd_7777840 3993770373765954398930371 := by
  unfold tailWord_7777840
  simp only [CollatzResearch.WordTrace]
  refine ⟨141840565071110752080909487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189120753428147669441212649 141840565071110752080909487)
  ·
    refine ⟨212760847606666128121364231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141840565071110752080909487 212760847606666128121364231)
    ·
      refine ⟨319141271409999192182046347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212760847606666128121364231 319141271409999192182046347)
      ·
        refine ⟨478711907114998788273069521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319141271409999192182046347 478711907114998788273069521)
        ·
          refine ⟨359033930336249091204802141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478711907114998788273069521 359033930336249091204802141)
          ·
            refine ⟨134637723876093409201800803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359033930336249091204802141 134637723876093409201800803)
            ·
              refine ⟨201956585814140113802701205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134637723876093409201800803 201956585814140113802701205)
              ·
                refine ⟨9466714960037817834501619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201956585814140113802701205 9466714960037817834501619)
                ·
                  refine ⟨14200072440056726751752429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9466714960037817834501619 14200072440056726751752429)
                  ·
                    refine ⟨5325027165021272531907161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14200072440056726751752429 5325027165021272531907161)
                    ·
                      refine ⟨3993770373765954398930371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325027165021272531907161 3993770373765954398930371)
                      ·
                        rfl

theorem cell23_7777840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 3, 2].length) (baseStart_7777840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777840 prefixEnd_7777840 := by exact prefixLift 7777840
  have htrace : WordTrace (prefixWord ++ tailWord_7777840) baseStart_7777840 baseEnd_7777840 := by
    simpa [prefixWord, tailWord_7777840, baseEnd_7777840] using wordTrace_append hprefix tailTrace_7777840
  have hstable : (prefixWord ++ tailWord_7777840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777840).length < 2 ^ (prefixWord ++ tailWord_7777840).sum := by decide
  have hdescent : baseEnd_7777840 < baseStart_7777840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777856 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_7777856 : Nat := 118140960795 + 7777856 * 2 ^ 59
def prefixEnd_7777856 : Nat := 4983230072969 + 3 ^ 40 * 7777856 * 2
def baseEnd_7777856 : Nat := 3993778589456426336330297

theorem tailTrace_7777856 : CollatzResearch.WordTrace tailWord_7777856 prefixEnd_7777856 3993778589456426336330297 := by
  unfold tailWord_7777856
  simp only [CollatzResearch.WordTrace]
  refine ⟨141840856855081769447200711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189121142473442359262934281 141840856855081769447200711)
  ·
    refine ⟨212761285282622654170801067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141840856855081769447200711 212761285282622654170801067)
    ·
      refine ⟨319141927923933981256201601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212761285282622654170801067 319141927923933981256201601)
      ·
        refine ⟨239356445942950485942151201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319141927923933981256201601 239356445942950485942151201)
        ·
          refine ⟨179517334457212864456613401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239356445942950485942151201 179517334457212864456613401)
          ·
            refine ⟨134638000842909648342460051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179517334457212864456613401 134638000842909648342460051)
            ·
              refine ⟨201957001264364472513690077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134638000842909648342460051 201957001264364472513690077)
              ·
                refine ⟨75733875474136677192633779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201957001264364472513690077 75733875474136677192633779)
                ·
                  refine ⟨113600813211205015788950669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75733875474136677192633779 113600813211205015788950669)
                  ·
                    refine ⟨42600304954201880920856501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113600813211205015788950669 42600304954201880920856501)
                    ·
                      refine ⟨3993778589456426336330297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42600304954201880920856501 3993778589456426336330297)
                      ·
                        rfl

theorem cell23_7777856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_7777856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777856 prefixEnd_7777856 := by exact prefixLift 7777856
  have htrace : WordTrace (prefixWord ++ tailWord_7777856) baseStart_7777856 baseEnd_7777856 := by
    simpa [prefixWord, tailWord_7777856, baseEnd_7777856] using wordTrace_append hprefix tailTrace_7777856
  have hstable : (prefixWord ++ tailWord_7777856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777856).length < 2 ^ (prefixWord ++ tailWord_7777856).sum := by decide
  have hdescent : baseEnd_7777856 < baseStart_7777856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777857 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_7777857 : Nat := 118140960795 + 7777857 * 2 ^ 59
def prefixEnd_7777857 : Nat := 4983230072969 + 3 ^ 40 * 7777857 * 2
def baseEnd_7777857 : Nat := 3993779102937080832417793

theorem tailTrace_7777857 : CollatzResearch.WordTrace tailWord_7777857 prefixEnd_7777857 3993779102937080832417793 := by
  unfold tailWord_7777857
  simp only [CollatzResearch.WordTrace]
  refine ⟨283681750183159916065187825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189121166788773277376791883 283681750183159916065187825)
  ·
    refine ⟨212761312637369937048890869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283681750183159916065187825 212761312637369937048890869)
    ·
      refine ⟨19946373059753431598333519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212761312637369937048890869 19946373059753431598333519)
      ·
        refine ⟨29919559589630147397500279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19946373059753431598333519 29919559589630147397500279)
        ·
          refine ⟨44879339384445221096250419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29919559589630147397500279 44879339384445221096250419)
          ·
            refine ⟨67319009076667831644375629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44879339384445221096250419 67319009076667831644375629)
            ·
              refine ⟨25244628403750436866640861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67319009076667831644375629 25244628403750436866640861)
              ·
                refine ⟨9466735651406413824990323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25244628403750436866640861 9466735651406413824990323)
                ·
                  refine ⟨14200103477109620737485485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9466735651406413824990323 14200103477109620737485485)
                  ·
                    refine ⟨5325038803916107776557057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14200103477109620737485485 5325038803916107776557057)
                    ·
                      refine ⟨3993779102937080832417793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325038803916107776557057 3993779102937080832417793)
                      ·
                        rfl

theorem cell23_7777857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_7777857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777857 prefixEnd_7777857 := by exact prefixLift 7777857
  have htrace : WordTrace (prefixWord ++ tailWord_7777857) baseStart_7777857 baseEnd_7777857 := by
    simpa [prefixWord, tailWord_7777857, baseEnd_7777857] using wordTrace_append hprefix tailTrace_7777857
  have hstable : (prefixWord ++ tailWord_7777857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777857).length < 2 ^ (prefixWord ++ tailWord_7777857).sum := by decide
  have hdescent : baseEnd_7777857 < baseStart_7777857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777893 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 7]
def baseStart_7777893 : Nat := 118140960795 + 7777893 * 2 ^ 59
def prefixEnd_7777893 : Nat := 4983230072969 + 3 ^ 40 * 7777893 * 2
def baseEnd_7777893 : Nat := 443755287582293632396403

theorem tailTrace_7777893 : CollatzResearch.WordTrace tailWord_7777893 prefixEnd_7777893 443755287582293632396403 := by
  unfold tailWord_7777893
  simp only [CollatzResearch.WordTrace]
  refine ⟨283683063211029494213498333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189122042140686329475665555 283683063211029494213498333)
  ·
    refine ⟨106381148704136060330061875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283683063211029494213498333 106381148704136060330061875)
    ·
      refine ⟨159571723056204090495092813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106381148704136060330061875 159571723056204090495092813)
      ·
        refine ⟨59839396146076533935659805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159571723056204090495092813 59839396146076533935659805)
        ·
          refine ⟨22439773554778700225872427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59839396146076533935659805 22439773554778700225872427)
          ·
            refine ⟨33659660332168050338808641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22439773554778700225872427 33659660332168050338808641)
            ·
              refine ⟨25244745249126037754106481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33659660332168050338808641 25244745249126037754106481)
              ·
                refine ⟨18933558936844528315579861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25244745249126037754106481 18933558936844528315579861)
                ·
                  refine ⟨443755287582293632396403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18933558936844528315579861 443755287582293632396403)
                  ·
                    rfl

theorem cell23_7777893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_7777893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777893 prefixEnd_7777893 := by exact prefixLift 7777893
  have htrace : WordTrace (prefixWord ++ tailWord_7777893) baseStart_7777893 baseEnd_7777893 := by
    simpa [prefixWord, tailWord_7777893, baseEnd_7777893] using wordTrace_append hprefix tailTrace_7777893
  have hstable : (prefixWord ++ tailWord_7777893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777893).length < 2 ^ (prefixWord ++ tailWord_7777893).sum := by decide
  have hdescent : baseEnd_7777893 < baseStart_7777893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777927 : List Nat := [1, 1, 4, 2, 1, 4, 3, 2, 5]
def baseStart_7777927 : Nat := 118140960795 + 7777927 * 2 ^ 59
def prefixEnd_7777927 : Nat := 4983230072969 + 3 ^ 40 * 7777927 * 2
def baseEnd_7777927 : Nat := 443757227398099506504719

theorem tailTrace_7777927 : CollatzResearch.WordTrace tailWord_7777927 prefixEnd_7777927 443757227398099506504719 := by
  unfold tailWord_7777927
  simp only [CollatzResearch.WordTrace]
  refine ⟨283684303292906318020236035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189122868861937545346824023 283684303292906318020236035)
  ·
    refine ⟨425526454939359477030354053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283684303292906318020236035 425526454939359477030354053)
    ·
      refine ⟨79786210301129901943191385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425526454939359477030354053 79786210301129901943191385)
      ·
        refine ⟨59839657725847426457393539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79786210301129901943191385 59839657725847426457393539)
        ·
          refine ⟨89759486588771139686090309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59839657725847426457393539 89759486588771139686090309)
          ·
            refine ⟨16829903735394588691141933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89759486588771139686090309 16829903735394588691141933)
            ·
              refine ⟨6311213900772970759178225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16829903735394588691141933 6311213900772970759178225)
              ·
                refine ⟨4733410425579728069383669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6311213900772970759178225 4733410425579728069383669)
                ·
                  refine ⟨443757227398099506504719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4733410425579728069383669 443757227398099506504719)
                  ·
                    rfl

theorem cell23_7777927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 5].length) (baseStart_7777927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777927 prefixEnd_7777927 := by exact prefixLift 7777927
  have htrace : WordTrace (prefixWord ++ tailWord_7777927) baseStart_7777927 baseEnd_7777927 := by
    simpa [prefixWord, tailWord_7777927, baseEnd_7777927] using wordTrace_append hprefix tailTrace_7777927
  have hstable : (prefixWord ++ tailWord_7777927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777927).length < 2 ^ (prefixWord ++ tailWord_7777927).sum := by decide
  have hdescent : baseEnd_7777927 < baseStart_7777927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7777938 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_7777938 : Nat := 118140960795 + 7777938 * 2 ^ 59
def prefixEnd_7777938 : Nat := 4983230072969 + 3 ^ 40 * 7777938 * 2
def baseEnd_7777938 : Nat := 3993820694870095015504921

theorem tailTrace_7777938 : CollatzResearch.WordTrace tailWord_7777938 prefixEnd_7777938 3993820694870095015504921 := by
  unfold tailWord_7777938
  simp only [CollatzResearch.WordTrace]
  refine ⟨70921176123966616724721617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189123136330577644599257645 70921176123966616724721617)
  ·
    refine ⟨53190882092974962543541213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70921176123966616724721617 53190882092974962543541213)
    ·
      refine ⟨19946580784865610953827955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53190882092974962543541213 19946580784865610953827955)
      ·
        refine ⟨29919871177298416430741933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19946580784865610953827955 29919871177298416430741933)
        ·
          refine ⟨11219951691486906161528225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29919871177298416430741933 11219951691486906161528225)
          ·
            refine ⟨8414963768615179621146169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11219951691486906161528225 8414963768615179621146169)
            ·
              refine ⟨6311222826461384715859627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8414963768615179621146169 6311222826461384715859627)
              ·
                refine ⟨9466834239692077073789441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311222826461384715859627 9466834239692077073789441)
                ·
                  refine ⟨7100125679769057805342081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9466834239692077073789441 7100125679769057805342081)
                  ·
                    refine ⟨5325094259826793354006561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7100125679769057805342081 5325094259826793354006561)
                    ·
                      refine ⟨3993820694870095015504921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325094259826793354006561 3993820694870095015504921)
                      ·
                        rfl

theorem cell23_7777938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_7777938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7777938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7777938 prefixEnd_7777938 := by exact prefixLift 7777938
  have htrace : WordTrace (prefixWord ++ tailWord_7777938) baseStart_7777938 baseEnd_7777938 := by
    simpa [prefixWord, tailWord_7777938, baseEnd_7777938] using wordTrace_append hprefix tailTrace_7777938
  have hstable : (prefixWord ++ tailWord_7777938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7777938).length < 2 ^ (prefixWord ++ tailWord_7777938).sum := by decide
  have hdescent : baseEnd_7777938 < baseStart_7777938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7777938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778044 : List Nat := [2, 2, 2, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_7778044 : Nat := 118140960795 + 7778044 * 2 ^ 59
def prefixEnd_7778044 : Nat := 4983230072969 + 3 ^ 40 * 7778044 * 2
def baseEnd_7778044 : Nat := 3993875123819471600779433

theorem tailTrace_7778044 : CollatzResearch.WordTrace tailWord_7778044 prefixEnd_7778044 3993875123819471600779433 := by
  unfold tailWord_7778044
  simp only [CollatzResearch.WordTrace]
  refine ⟨141844285316741223501122593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189125713755654964668163457 141844285316741223501122593)
  ·
    refine ⟨106383213987555917625841945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141844285316741223501122593 106383213987555917625841945)
    ·
      refine ⟨79787410490666938219381459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106383213987555917625841945 79787410490666938219381459)
      ·
        refine ⟨119681115736000407329072189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79787410490666938219381459 119681115736000407329072189)
        ·
          refine ⟨44880418401000152748402071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119681115736000407329072189 44880418401000152748402071)
          ·
            refine ⟨67320627601500229122603107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44880418401000152748402071 67320627601500229122603107)
            ·
              refine ⟨100980941402250343683904661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67320627601500229122603107 100980941402250343683904661)
              ·
                refine ⟨4733481628230484860183031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100980941402250343683904661 4733481628230484860183031)
                ·
                  refine ⟨7100222442345727290274547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733481628230484860183031 7100222442345727290274547)
                  ·
                    refine ⟨10650333663518590935411821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7100222442345727290274547 10650333663518590935411821)
                    ·
                      refine ⟨3993875123819471600779433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10650333663518590935411821 3993875123819471600779433)
                      ·
                        rfl

theorem cell23_7778044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_7778044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778044 prefixEnd_7778044 := by exact prefixLift 7778044
  have htrace : WordTrace (prefixWord ++ tailWord_7778044) baseStart_7778044 baseEnd_7778044 := by
    simpa [prefixWord, tailWord_7778044, baseEnd_7778044] using wordTrace_append hprefix tailTrace_7778044
  have hstable : (prefixWord ++ tailWord_7778044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778044).length < 2 ^ (prefixWord ++ tailWord_7778044).sum := by decide
  have hdescent : baseEnd_7778044 < baseStart_7778044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778060 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_7778060 : Nat := 118140960795 + 7778060 * 2 ^ 59
def prefixEnd_7778060 : Nat := 4983230072969 + 3 ^ 40 * 7778060 * 2
def baseEnd_7778060 : Nat := 1331294446503314512726453

theorem tailTrace_7778060 : CollatzResearch.WordTrace tailWord_7778060 prefixEnd_7778060 1331294446503314512726453 := by
  unfold tailWord_7778060
  simp only [CollatzResearch.WordTrace]
  refine ⟨141844577100712240867413817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189126102800949654489885089 141844577100712240867413817)
  ·
    refine ⟨106383432825534180650560363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141844577100712240867413817 106383432825534180650560363)
    ·
      refine ⟨159575149238301270975840545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106383432825534180650560363 159575149238301270975840545)
      ·
        refine ⟨119681361928725953231880409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159575149238301270975840545 119681361928725953231880409)
        ·
          refine ⟨89761021446544464923910307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119681361928725953231880409 89761021446544464923910307)
          ·
            refine ⟨134641532169816697385865461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89761021446544464923910307 134641532169816697385865461)
            ·
              refine ⟨12622643640920315379924887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134641532169816697385865461 12622643640920315379924887)
              ·
                refine ⟨18933965461380473069887331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12622643640920315379924887 18933965461380473069887331)
                ·
                  refine ⟨28400948192070709604830997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18933965461380473069887331 28400948192070709604830997)
                  ·
                    refine ⟨1331294446503314512726453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28400948192070709604830997 1331294446503314512726453)
                    ·
                      rfl

theorem cell23_7778060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_7778060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778060 prefixEnd_7778060 := by exact prefixLift 7778060
  have htrace : WordTrace (prefixWord ++ tailWord_7778060) baseStart_7778060 baseEnd_7778060 := by
    simpa [prefixWord, tailWord_7778060, baseEnd_7778060] using wordTrace_append hprefix tailTrace_7778060
  have hstable : (prefixWord ++ tailWord_7778060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778060).length < 2 ^ (prefixWord ++ tailWord_7778060).sum := by decide
  have hdescent : baseEnd_7778060 < baseStart_7778060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778067 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 5, 2, 2]
def baseStart_7778067 : Nat := 118140960795 + 7778067 * 2 ^ 59
def prefixEnd_7778067 : Nat := 4983230072969 + 3 ^ 40 * 7778067 * 2
def baseEnd_7778067 : Nat := 3993886933874525010791827

theorem tailTrace_7778067 : CollatzResearch.WordTrace tailWord_7778067 prefixEnd_7778067 3993886933874525010791827 := by
  unfold tailWord_7778067
  simp only [CollatzResearch.WordTrace]
  refine ⟨283689409512399121930332455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189126273008266081286888303 283689409512399121930332455)
  ·
    refine ⟨425534114268598682895498683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283689409512399121930332455 425534114268598682895498683)
    ·
      refine ⟨638301171402898024343248025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425534114268598682895498683 638301171402898024343248025)
      ·
        refine ⟨478725878552173518257436019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638301171402898024343248025 478725878552173518257436019)
        ·
          refine ⟨718088817828260277386154029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478725878552173518257436019 718088817828260277386154029)
          ·
            refine ⟨269283306685597604019807761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 718088817828260277386154029 269283306685597604019807761)
            ·
              refine ⟨201962480014198203014855821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269283306685597604019807761 201962480014198203014855821)
              ·
                refine ⟨75735930005324326130570933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201962480014198203014855821 75735930005324326130570933)
                ·
                  refine ⟨7100243437999155574741025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75735930005324326130570933 7100243437999155574741025)
                  ·
                    refine ⟨5325182578499366681055769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7100243437999155574741025 5325182578499366681055769)
                    ·
                      refine ⟨3993886933874525010791827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325182578499366681055769 3993886933874525010791827)
                      ·
                        rfl

theorem cell23_7778067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 2, 2].length) (baseStart_7778067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778067 prefixEnd_7778067 := by exact prefixLift 7778067
  have htrace : WordTrace (prefixWord ++ tailWord_7778067) baseStart_7778067 baseEnd_7778067 := by
    simpa [prefixWord, tailWord_7778067, baseEnd_7778067] using wordTrace_append hprefix tailTrace_7778067
  have hstable : (prefixWord ++ tailWord_7778067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778067).length < 2 ^ (prefixWord ++ tailWord_7778067).sum := by decide
  have hdescent : baseEnd_7778067 < baseStart_7778067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778080 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7778080 : Nat := 118140960795 + 7778080 * 2 ^ 59
def prefixEnd_7778080 : Nat := 4983230072969 + 3 ^ 40 * 7778080 * 2
def baseEnd_7778080 : Nat := 3993893609123033459929267

theorem tailTrace_7778080 : CollatzResearch.WordTrace tailWord_7778080 prefixEnd_7778080 3993893609123033459929267 := by
  unfold tailWord_7778080
  simp only [CollatzResearch.WordTrace]
  refine ⟨141844941830676012575277847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189126589107568016767037129 141844941830676012575277847)
  ·
    refine ⟨212767412746014018862916771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141844941830676012575277847 212767412746014018862916771)
    ·
      refine ⟨319151119119021028294375157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212767412746014018862916771 319151119119021028294375157)
      ·
        refine ⟨29920417417408221402597671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319151119119021028294375157 29920417417408221402597671)
        ·
          refine ⟨44880626126112332103896507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29920417417408221402597671 44880626126112332103896507)
          ·
            refine ⟨67320939189168498155844761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44880626126112332103896507 67320939189168498155844761)
            ·
              refine ⟨50490704391876373616883571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67320939189168498155844761 50490704391876373616883571)
              ·
                refine ⟨75736056587814560425325357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50490704391876373616883571 75736056587814560425325357)
                ·
                  refine ⟨28401021220430460159497009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75736056587814560425325357 28401021220430460159497009)
                  ·
                    refine ⟨21300765915322845119622757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28401021220430460159497009 21300765915322845119622757)
                    ·
                      refine ⟨3993893609123033459929267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21300765915322845119622757 3993893609123033459929267)
                      ·
                        rfl

theorem cell23_7778080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7778080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778080 prefixEnd_7778080 := by exact prefixLift 7778080
  have htrace : WordTrace (prefixWord ++ tailWord_7778080) baseStart_7778080 baseEnd_7778080 := by
    simpa [prefixWord, tailWord_7778080, baseEnd_7778080] using wordTrace_append hprefix tailTrace_7778080
  have hstable : (prefixWord ++ tailWord_7778080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778080).length < 2 ^ (prefixWord ++ tailWord_7778080).sum := by decide
  have hdescent : baseEnd_7778080 < baseStart_7778080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778111 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 2, 4]
def baseStart_7778111 : Nat := 118140960795 + 7778111 * 2 ^ 59
def prefixEnd_7778111 : Nat := 4983230072969 + 3 ^ 40 * 7778111 * 2
def baseEnd_7778111 : Nat := 1331303175674440946213875

theorem tailTrace_7778111 : CollatzResearch.WordTrace tailWord_7778111 prefixEnd_7778111 1331303175674440946213875 := by
  unfold tailWord_7778111
  simp only [CollatzResearch.WordTrace]
  refine ⟨283691014324239717444934187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189127342882826478296622791 283691014324239717444934187)
  ·
    refine ⟨425536521486359576167401281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283691014324239717444934187 425536521486359576167401281)
    ·
      refine ⟨319152391114769682125550961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425536521486359576167401281 319152391114769682125550961)
      ·
        refine ⟨239364293336077261594163221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319152391114769682125550961 239364293336077261594163221)
        ·
          refine ⟨11220201250128621637226401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239364293336077261594163221 11220201250128621637226401)
          ·
            refine ⟨8415150937596466227919801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11220201250128621637226401 8415150937596466227919801)
            ·
              refine ⟨6311363203197349670939851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8415150937596466227919801 6311363203197349670939851)
              ·
                refine ⟨9467044804796024506409777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311363203197349670939851 9467044804796024506409777)
                ·
                  refine ⟨7100283603597018379807333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9467044804796024506409777 7100283603597018379807333)
                  ·
                    refine ⟨1331303175674440946213875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100283603597018379807333 1331303175674440946213875)
                    ·
                      rfl

theorem cell23_7778111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 4].length) (baseStart_7778111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778111 prefixEnd_7778111 := by exact prefixLift 7778111
  have htrace : WordTrace (prefixWord ++ tailWord_7778111) baseStart_7778111 baseEnd_7778111 := by
    simpa [prefixWord, tailWord_7778111, baseEnd_7778111] using wordTrace_append hprefix tailTrace_7778111
  have hstable : (prefixWord ++ tailWord_7778111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778111).length < 2 ^ (prefixWord ++ tailWord_7778111).sum := by decide
  have hdescent : baseEnd_7778111 < baseStart_7778111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778118 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7778118 : Nat := 118140960795 + 7778118 * 2 ^ 59
def prefixEnd_7778118 : Nat := 4983230072969 + 3 ^ 40 * 7778118 * 2
def baseEnd_7778118 : Nat := 3993913121387904311254093

theorem tailTrace_7778118 : CollatzResearch.WordTrace tailWord_7778118 prefixEnd_7778118 3993913121387904311254093 := by
  unfold tailWord_7778118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865352176100448676263719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 189127513090142905093626005 8865352176100448676263719)
  ·
    refine ⟨13298028264150673014395579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8865352176100448676263719 13298028264150673014395579)
    ·
      refine ⟨19947042396226009521593369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13298028264150673014395579 19947042396226009521593369)
      ·
        refine ⟨14960281797169507141195027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19947042396226009521593369 14960281797169507141195027)
        ·
          refine ⟨22440422695754260711792541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14960281797169507141195027 22440422695754260711792541)
          ·
            refine ⟨8415158510907847766922203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22440422695754260711792541 8415158510907847766922203)
            ·
              refine ⟨12622737766361771650383305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8415158510907847766922203 12622737766361771650383305)
              ·
                refine ⟨9467053324771328737787479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12622737766361771650383305 9467053324771328737787479)
                ·
                  refine ⟨14200579987156993106681219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9467053324771328737787479 14200579987156993106681219)
                  ·
                    refine ⟨21300869980735489660021829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14200579987156993106681219 21300869980735489660021829)
                    ·
                      refine ⟨3993913121387904311254093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21300869980735489660021829 3993913121387904311254093)
                      ·
                        rfl

theorem cell23_7778118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7778118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778118 prefixEnd_7778118 := by exact prefixLift 7778118
  have htrace : WordTrace (prefixWord ++ tailWord_7778118) baseStart_7778118 baseEnd_7778118 := by
    simpa [prefixWord, tailWord_7778118, baseEnd_7778118] using wordTrace_append hprefix tailTrace_7778118
  have hstable : (prefixWord ++ tailWord_7778118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778118).length < 2 ^ (prefixWord ++ tailWord_7778118).sum := by decide
  have hdescent : baseEnd_7778118 < baseStart_7778118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778170 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_7778170 : Nat := 118140960795 + 7778170 * 2 ^ 59
def prefixEnd_7778170 : Nat := 4983230072969 + 3 ^ 40 * 7778170 * 2
def baseEnd_7778170 : Nat := 3993939822381938107803853

theorem tailTrace_7778170 : CollatzResearch.WordTrace tailWord_7778170 prefixEnd_7778170 3993939822381938107803853 := by
  unfold tailWord_7778170
  simp only [CollatzResearch.WordTrace]
  refine ⟨70923291557756492630332991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189128777487350647014221309 70923291557756492630332991)
  ·
    refine ⟨106384937336634738945499487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70923291557756492630332991 106384937336634738945499487)
    ·
      refine ⟨159577406004952108418249231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106384937336634738945499487 159577406004952108418249231)
      ·
        refine ⟨239366109007428162627373847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159577406004952108418249231 239366109007428162627373847)
        ·
          refine ⟨359049163511142243941060771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239366109007428162627373847 359049163511142243941060771)
          ·
            refine ⟨538573745266713365911591157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359049163511142243941060771 538573745266713365911591157)
            ·
              refine ⟨50491288618754378054211671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 538573745266713365911591157 50491288618754378054211671)
              ·
                refine ⟨75736932928131567081317507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50491288618754378054211671 75736932928131567081317507)
                ·
                  refine ⟨113605399392197350621976261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75736932928131567081317507 113605399392197350621976261)
                  ·
                    refine ⟨21301012386037003241620549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113605399392197350621976261 21301012386037003241620549)
                    ·
                      refine ⟨3993939822381938107803853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21301012386037003241620549 3993939822381938107803853)
                      ·
                        rfl

theorem cell23_7778170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_7778170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778170 prefixEnd_7778170 := by exact prefixLift 7778170
  have htrace : WordTrace (prefixWord ++ tailWord_7778170) baseStart_7778170 baseEnd_7778170 := by
    simpa [prefixWord, tailWord_7778170, baseEnd_7778170] using wordTrace_append hprefix tailTrace_7778170
  have hstable : (prefixWord ++ tailWord_7778170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778170).length < 2 ^ (prefixWord ++ tailWord_7778170).sum := by decide
  have hdescent : baseEnd_7778170 < baseStart_7778170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778180 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 9]
def baseStart_7778180 : Nat := 118140960795 + 7778180 * 2 ^ 59
def prefixEnd_7778180 : Nat := 4983230072969 + 3 ^ 40 * 7778180 * 2
def baseEnd_7778180 : Nat := 443771661909831452075423

theorem tailTrace_7778180 : CollatzResearch.WordTrace tailWord_7778180 prefixEnd_7778180 443771661909831452075423 := by
  unfold tailWord_7778180
  simp only [CollatzResearch.WordTrace]
  refine ⟨141846765480494871114597997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189129020640659828152797329 141846765480494871114597997)
  ·
    refine ⟨53192537055185576667974249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141846765480494871114597997 53192537055185576667974249)
    ·
      refine ⟨39894402791389182500980687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53192537055185576667974249 39894402791389182500980687)
      ·
        refine ⟨59841604187083773751471031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39894402791389182500980687 59841604187083773751471031)
        ·
          refine ⟨89762406280625660627206547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59841604187083773751471031 89762406280625660627206547)
          ·
            refine ⟨134643609420938490940809821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89762406280625660627206547 134643609420938490940809821)
            ·
              refine ⟨50491353532851934102803683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134643609420938490940809821 50491353532851934102803683)
              ·
                refine ⟨75737030299277901154205525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50491353532851934102803683 75737030299277901154205525)
                ·
                  refine ⟨443771661909831452075423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75737030299277901154205525 443771661909831452075423)
                  ·
                    rfl

theorem cell23_7778180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_7778180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778180 prefixEnd_7778180 := by exact prefixLift 7778180
  have htrace : WordTrace (prefixWord ++ tailWord_7778180) baseStart_7778180 baseEnd_7778180 := by
    simpa [prefixWord, tailWord_7778180, baseEnd_7778180] using wordTrace_append hprefix tailTrace_7778180
  have hstable : (prefixWord ++ tailWord_7778180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778180).length < 2 ^ (prefixWord ++ tailWord_7778180).sum := by decide
  have hdescent : baseEnd_7778180 < baseStart_7778180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778217 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 2, 5, 2]
def baseStart_7778217 : Nat := 118140960795 + 7778217 * 2 ^ 59
def prefixEnd_7778217 : Nat := 4983230072969 + 3 ^ 40 * 7778217 * 2
def baseEnd_7778217 : Nat := 3993963955972699423916137

theorem tailTrace_7778217 : CollatzResearch.WordTrace tailWord_7778217 prefixEnd_7778217 3993963955972699423916137 := by
  unfold tailWord_7778217
  simp only [CollatzResearch.WordTrace]
  refine ⟨283694880461855697548292905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189129920307903798365528603 283694880461855697548292905)
  ·
    refine ⟨212771160346391773161219679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283694880461855697548292905 212771160346391773161219679)
    ·
      refine ⟨319156740519587659741829519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212771160346391773161219679 319156740519587659741829519)
      ·
        refine ⟨478735110779381489612744279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319156740519587659741829519 478735110779381489612744279)
        ·
          refine ⟨718102666169072234419116419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478735110779381489612744279 718102666169072234419116419)
          ·
            refine ⟨1077153999253608351628674629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718102666169072234419116419 1077153999253608351628674629)
            ·
              refine ⟨201966374860051565930376493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1077153999253608351628674629 201966374860051565930376493)
              ·
                refine ⟨75737390572519337223891185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201966374860051565930376493 75737390572519337223891185)
                ·
                  refine ⟨56803042929389502917918389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75737390572519337223891185 56803042929389502917918389)
                  ·
                    refine ⟨5325285274630265898554849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56803042929389502917918389 5325285274630265898554849)
                    ·
                      refine ⟨3993963955972699423916137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325285274630265898554849 3993963955972699423916137)
                      ·
                        rfl

theorem cell23_7778217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 5, 2].length) (baseStart_7778217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778217 prefixEnd_7778217 := by exact prefixLift 7778217
  have htrace : WordTrace (prefixWord ++ tailWord_7778217) baseStart_7778217 baseEnd_7778217 := by
    simpa [prefixWord, tailWord_7778217, baseEnd_7778217] using wordTrace_append hprefix tailTrace_7778217
  have hstable : (prefixWord ++ tailWord_7778217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778217).length < 2 ^ (prefixWord ++ tailWord_7778217).sum := by decide
  have hdescent : baseEnd_7778217 < baseStart_7778217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778240 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 2, 8]
def baseStart_7778240 : Nat := 118140960795 + 7778240 * 2 ^ 59
def prefixEnd_7778240 : Nat := 4983230072969 + 3 ^ 40 * 7778240 * 2
def baseEnd_7778240 : Nat := 1331325255342584277976177

theorem tailTrace_7778240 : CollatzResearch.WordTrace tailWord_7778240 prefixEnd_7778240 1331325255342584277976177 := by
  unfold tailWord_7778240
  simp only [CollatzResearch.WordTrace]
  refine ⟨141847859670386186238190087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189130479560514914984253449 141847859670386186238190087)
  ·
    refine ⟨212771789505579279357285131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141847859670386186238190087 212771789505579279357285131)
    ·
      refine ⟨319157684258368919035927697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212771789505579279357285131 319157684258368919035927697)
      ·
        refine ⟨239368263193776689276945773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319157684258368919035927697 239368263193776689276945773)
        ·
          refine ⟨89763098697666258478854665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239368263193776689276945773 89763098697666258478854665)
          ·
            refine ⟨67322324023249693859140999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89763098697666258478854665 67322324023249693859140999)
            ·
              refine ⟨100983486034874540788711499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67322324023249693859140999 100983486034874540788711499)
              ·
                refine ⟨151475229052311811183067249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100983486034874540788711499 151475229052311811183067249)
                ·
                  refine ⟨113606421789233858387300437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151475229052311811183067249 113606421789233858387300437)
                  ·
                    refine ⟨1331325255342584277976177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113606421789233858387300437 1331325255342584277976177)
                    ·
                      rfl

theorem cell23_7778240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_7778240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778240 prefixEnd_7778240 := by exact prefixLift 7778240
  have htrace : WordTrace (prefixWord ++ tailWord_7778240) baseStart_7778240 baseEnd_7778240 := by
    simpa [prefixWord, tailWord_7778240, baseEnd_7778240] using wordTrace_append hprefix tailTrace_7778240
  have hstable : (prefixWord ++ tailWord_7778240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778240).length < 2 ^ (prefixWord ++ tailWord_7778240).sum := by decide
  have hdescent : baseEnd_7778240 < baseStart_7778240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778247 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_7778247 : Nat := 118140960795 + 7778247 * 2 ^ 59
def prefixEnd_7778247 : Nat := 4983230072969 + 3 ^ 40 * 7778247 * 2
def baseEnd_7778247 : Nat := 3993979360392334306540999

theorem tailTrace_7778247 : CollatzResearch.WordTrace tailWord_7778247 prefixEnd_7778247 3993979360392334306540999 := by
  unfold tailWord_7778247
  simp only [CollatzResearch.WordTrace]
  refine ⟨283695974651747012671884995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189130649767831341781256663 283695974651747012671884995)
  ·
    refine ⟨425543961977620519007827493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283695974651747012671884995 425543961977620519007827493)
    ·
      refine ⟨79789492870803847313967655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425543961977620519007827493 79789492870803847313967655)
      ·
        refine ⟨119684239306205770970951483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79789492870803847313967655 119684239306205770970951483)
        ·
          refine ⟨179526358959308656456427225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119684239306205770970951483 179526358959308656456427225)
          ·
            refine ⟨134644769219481492342320419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179526358959308656456427225 134644769219481492342320419)
            ·
              refine ⟨201967153829222238513480629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134644769219481492342320419 201967153829222238513480629)
              ·
                refine ⟨18934420671489584860638809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201967153829222238513480629 18934420671489584860638809)
                ·
                  refine ⟨14200815503617188645479107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18934420671489584860638809 14200815503617188645479107)
                  ·
                    refine ⟨21301223255425782968218661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14200815503617188645479107 21301223255425782968218661)
                    ·
                      refine ⟨3993979360392334306540999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21301223255425782968218661 3993979360392334306540999)
                      ·
                        rfl

theorem cell23_7778247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_7778247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778247 prefixEnd_7778247 := by exact prefixLift 7778247
  have htrace : WordTrace (prefixWord ++ tailWord_7778247) baseStart_7778247 baseEnd_7778247 := by
    simpa [prefixWord, tailWord_7778247, baseEnd_7778247] using wordTrace_append hprefix tailTrace_7778247
  have hstable : (prefixWord ++ tailWord_7778247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778247).length < 2 ^ (prefixWord ++ tailWord_7778247).sum := by decide
  have hdescent : baseEnd_7778247 < baseStart_7778247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778287 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 6]
def baseStart_7778287 : Nat := 118140960795 + 7778287 * 2 ^ 59
def prefixEnd_7778287 : Nat := 4983230072969 + 3 ^ 40 * 7778287 * 2
def baseEnd_7778287 : Nat := 443777766624279350004535

theorem tailTrace_7778287 : CollatzResearch.WordTrace tailWord_7778287 prefixEnd_7778287 443777766624279350004535 := by
  unfold tailWord_7778287
  simp only [CollatzResearch.WordTrace]
  refine ⟨283697433571602099503341115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189131622381068066335560743 283697433571602099503341115)
  ·
    refine ⟨425546150357403149255011673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283697433571602099503341115 425546150357403149255011673)
    ·
      refine ⟨319159612768052361941258755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425546150357403149255011673 319159612768052361941258755)
      ·
        refine ⟨478739419152078542911888133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319159612768052361941258755 478739419152078542911888133)
        ·
          refine ⟨89763641091014726795979025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 478739419152078542911888133 89763641091014726795979025)
          ·
            refine ⟨67322730818261045096984269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89763641091014726795979025 67322730818261045096984269)
            ·
              refine ⟨25246024056847891911369101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67322730818261045096984269 25246024056847891911369101)
              ·
                refine ⟨9467259021317959466763413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25246024056847891911369101 9467259021317959466763413)
                ·
                  refine ⟨443777766624279350004535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9467259021317959466763413 443777766624279350004535)
                  ·
                    rfl

theorem cell23_7778287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 6].length) (baseStart_7778287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778287 prefixEnd_7778287 := by exact prefixLift 7778287
  have htrace : WordTrace (prefixWord ++ tailWord_7778287) baseStart_7778287 baseEnd_7778287 := by
    simpa [prefixWord, tailWord_7778287, baseEnd_7778287] using wordTrace_append hprefix tailTrace_7778287
  have hstable : (prefixWord ++ tailWord_7778287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778287).length < 2 ^ (prefixWord ++ tailWord_7778287).sum := by decide
  have hdescent : baseEnd_7778287 < baseStart_7778287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778325 : List Nat := [1, 3, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_7778325 : Nat := 118140960795 + 7778325 * 2 ^ 59
def prefixEnd_7778325 : Nat := 4983230072969 + 3 ^ 40 * 7778325 * 2
def baseEnd_7778325 : Nat := 1331339803961128333788547

theorem tailTrace_7778325 : CollatzResearch.WordTrace tailWord_7778325 prefixEnd_7778325 1331339803961128333788547 := by
  unfold tailWord_7778325
  simp only [CollatzResearch.WordTrace]
  refine ⟨283698819545464431993224429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189132546363642954662149619 283698819545464431993224429)
  ·
    refine ⟨106387057329549161997459161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283698819545464431993224429 106387057329549161997459161)
    ·
      refine ⟨79790292997161871498094371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106387057329549161997459161 79790292997161871498094371)
      ·
        refine ⟨119685439495742807247141557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79790292997161871498094371 119685439495742807247141557)
        ·
          refine ⟨11220509952725888179419521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119685439495742807247141557 11220509952725888179419521)
          ·
            refine ⟨8415382464544416134564641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11220509952725888179419521 8415382464544416134564641)
            ·
              refine ⟨6311536848408312100923481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8415382464544416134564641 6311536848408312100923481)
              ·
                refine ⟨4733652636306234075692611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6311536848408312100923481 4733652636306234075692611)
                ·
                  refine ⟨7100478954459351113538917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733652636306234075692611 7100478954459351113538917)
                  ·
                    refine ⟨1331339803961128333788547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100478954459351113538917 1331339803961128333788547)
                    ·
                      rfl

theorem cell23_7778325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_7778325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778325 prefixEnd_7778325 := by exact prefixLift 7778325
  have htrace : WordTrace (prefixWord ++ tailWord_7778325) baseStart_7778325 baseEnd_7778325 := by
    simpa [prefixWord, tailWord_7778325, baseEnd_7778325] using wordTrace_append hprefix tailTrace_7778325
  have hstable : (prefixWord ++ tailWord_7778325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778325).length < 2 ^ (prefixWord ++ tailWord_7778325).sum := by decide
  have hdescent : baseEnd_7778325 < baseStart_7778325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778354 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_7778354 : Nat := 118140960795 + 7778354 * 2 ^ 59
def prefixEnd_7778354 : Nat := 4983230072969 + 3 ^ 40 * 7778354 * 2
def baseEnd_7778354 : Nat := 3994034302822365387903007

theorem tailTrace_7778354 : CollatzResearch.WordTrace tailWord_7778354 prefixEnd_7778354 3994034302822365387903007 := by
  unfold tailWord_7778354
  simp only [CollatzResearch.WordTrace]
  refine ⟨70924969315589842486507529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189133251508239579964020077 70924969315589842486507529)
  ·
    refine ⟨53193726986692381864880647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70924969315589842486507529 53193726986692381864880647)
    ·
      refine ⟨79790590480038572797320971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53193726986692381864880647 79790590480038572797320971)
      ·
        refine ⟨119685885720057859195981457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79790590480038572797320971 119685885720057859195981457)
        ·
          refine ⟨89764414290043394396986093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119685885720057859195981457 89764414290043394396986093)
          ·
            refine ⟨33661655358766272898869785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89764414290043394396986093 33661655358766272898869785)
            ·
              refine ⟨25246241519074704674152339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33661655358766272898869785 25246241519074704674152339)
              ·
                refine ⟨37869362278612057011228509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25246241519074704674152339 37869362278612057011228509)
                ·
                  refine ⟨14201010854479521379210691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37869362278612057011228509 14201010854479521379210691)
                  ·
                    refine ⟨21301516281719282068816037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14201010854479521379210691 21301516281719282068816037)
                    ·
                      refine ⟨3994034302822365387903007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21301516281719282068816037 3994034302822365387903007)
                      ·
                        rfl

theorem cell23_7778354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_7778354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778354 prefixEnd_7778354 := by exact prefixLift 7778354
  have htrace : WordTrace (prefixWord ++ tailWord_7778354) baseStart_7778354 baseEnd_7778354 := by
    simpa [prefixWord, tailWord_7778354, baseEnd_7778354] using wordTrace_append hprefix tailTrace_7778354
  have hstable : (prefixWord ++ tailWord_7778354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778354).length < 2 ^ (prefixWord ++ tailWord_7778354).sum := by decide
  have hdescent : baseEnd_7778354 < baseStart_7778354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778364 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_7778364 : Nat := 118140960795 + 7778364 * 2 ^ 59
def prefixEnd_7778364 : Nat := 4983230072969 + 3 ^ 40 * 7778364 * 2
def baseEnd_7778364 : Nat := 1331346479209636782925987

theorem tailTrace_7778364 : CollatzResearch.WordTrace tailWord_7778364 prefixEnd_7778364 1331346479209636782925987 := by
  unfold tailWord_7778364
  simp only [CollatzResearch.WordTrace]
  refine ⟨141850120996161570826947073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189133494661548761102596097 141850120996161570826947073)
  ·
    refine ⟨106387590747121178120210305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141850120996161570826947073 106387590747121178120210305)
    ·
      refine ⟨79790693060340883590157729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106387590747121178120210305 79790693060340883590157729)
      ·
        refine ⟨59843019795255662692618297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79790693060340883590157729 59843019795255662692618297)
        ·
          refine ⟨44882264846441747019463723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59843019795255662692618297 44882264846441747019463723)
          ·
            refine ⟨67323397269662620529195585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44882264846441747019463723 67323397269662620529195585)
            ·
              refine ⟨50492547952246965396896689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67323397269662620529195585 50492547952246965396896689)
              ·
                refine ⟨37869410964185224047672517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50492547952246965396896689 37869410964185224047672517)
                ·
                  refine ⟨7100514555784729508938597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37869410964185224047672517 7100514555784729508938597)
                  ·
                    refine ⟨1331346479209636782925987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100514555784729508938597 1331346479209636782925987)
                    ·
                      rfl

theorem cell23_7778364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_7778364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778364 prefixEnd_7778364 := by exact prefixLift 7778364
  have htrace : WordTrace (prefixWord ++ tailWord_7778364) baseStart_7778364 baseEnd_7778364 := by
    simpa [prefixWord, tailWord_7778364, baseEnd_7778364] using wordTrace_append hprefix tailTrace_7778364
  have hstable : (prefixWord ++ tailWord_7778364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778364).length < 2 ^ (prefixWord ++ tailWord_7778364).sum := by decide
  have hdescent : baseEnd_7778364 < baseStart_7778364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778381 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_7778381 : Nat := 118140960795 + 7778381 * 2 ^ 59
def prefixEnd_7778381 : Nat := 4983230072969 + 3 ^ 40 * 7778381 * 2
def baseEnd_7778381 : Nat := 1331349388933345594088461

theorem tailTrace_7778381 : CollatzResearch.WordTrace tailWord_7778381 prefixEnd_7778381 1331349388933345594088461 := by
  unfold tailWord_7778381
  simp only [CollatzResearch.WordTrace]
  refine ⟨283700862033261553557262997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189133908022174369038175331 283700862033261553557262997)
  ·
    refine ⟨13298477907809135322996703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 283700862033261553557262997 13298477907809135322996703)
    ·
      refine ⟨19947716861713702984495055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13298477907809135322996703 19947716861713702984495055)
      ·
        refine ⟨29921575292570554476742583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19947716861713702984495055 29921575292570554476742583)
        ·
          refine ⟨44882362938855831715113875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29921575292570554476742583 44882362938855831715113875)
          ·
            refine ⟨67323544408283747572670813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44882362938855831715113875 67323544408283747572670813)
            ·
              refine ⟨25246329153106405339751555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67323544408283747572670813 25246329153106405339751555)
              ·
                refine ⟨37869493729659608009627333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25246329153106405339751555 37869493729659608009627333)
                ·
                  refine ⟨7100530074311176501805125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37869493729659608009627333 7100530074311176501805125)
                  ·
                    refine ⟨1331349388933345594088461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100530074311176501805125 1331349388933345594088461)
                    ·
                      rfl

theorem cell23_7778381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_7778381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778381 prefixEnd_7778381 := by exact prefixLift 7778381
  have htrace : WordTrace (prefixWord ++ tailWord_7778381) baseStart_7778381 baseEnd_7778381 := by
    simpa [prefixWord, tailWord_7778381, baseEnd_7778381] using wordTrace_append hprefix tailTrace_7778381
  have hstable : (prefixWord ++ tailWord_7778381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778381).length < 2 ^ (prefixWord ++ tailWord_7778381).sum := by decide
  have hdescent : baseEnd_7778381 < baseStart_7778381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778417 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_7778417 : Nat := 118140960795 + 7778417 * 2 ^ 59
def prefixEnd_7778417 : Nat := 4983230072969 + 3 ^ 40 * 7778417 * 2
def baseEnd_7778417 : Nat := 3994066652103598641415217

theorem tailTrace_7778417 : CollatzResearch.WordTrace tailWord_7778417 prefixEnd_7778417 3994066652103598641415217 := by
  unfold tailWord_7778417
  simp only [CollatzResearch.WordTrace]
  refine ⟨283702175061131131705573505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189134783374087421137049003 283702175061131131705573505)
  ·
    refine ⟨212776631295848348779180129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283702175061131131705573505 212776631295848348779180129)
    ·
      refine ⟨159582473471886261584385097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212776631295848348779180129 159582473471886261584385097)
      ·
        refine ⟨119686855103914696188288823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159582473471886261584385097 119686855103914696188288823)
        ·
          refine ⟨179530282655872044282433235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119686855103914696188288823 179530282655872044282433235)
          ·
            refine ⟨269295423983808066423649853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179530282655872044282433235 269295423983808066423649853)
            ·
              refine ⟨100985783993928024908868695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269295423983808066423649853 100985783993928024908868695)
              ·
                refine ⟨151478675990892037363303043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100985783993928024908868695 151478675990892037363303043)
                ·
                  refine ⟨227218013986338056044954565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151478675990892037363303043 227218013986338056044954565)
                  ·
                    refine ⟨42603377622438385508428981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227218013986338056044954565 42603377622438385508428981)
                    ·
                      refine ⟨3994066652103598641415217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42603377622438385508428981 3994066652103598641415217)
                      ·
                        rfl

theorem cell23_7778417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_7778417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778417 prefixEnd_7778417 := by exact prefixLift 7778417
  have htrace : WordTrace (prefixWord ++ tailWord_7778417) baseStart_7778417 baseEnd_7778417 := by
    simpa [prefixWord, tailWord_7778417, baseEnd_7778417] using wordTrace_append hprefix tailTrace_7778417
  have hstable : (prefixWord ++ tailWord_7778417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778417).length < 2 ^ (prefixWord ++ tailWord_7778417).sum := by decide
  have hdescent : baseEnd_7778417 < baseStart_7778417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778422 : List Nat := [5, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_7778422 : Nat := 118140960795 + 7778422 * 2 ^ 59
def prefixEnd_7778422 : Nat := 4983230072969 + 3 ^ 40 * 7778422 * 2
def baseEnd_7778422 : Nat := 3994069219506871121852695

theorem tailTrace_7778422 : CollatzResearch.WordTrace tailWord_7778422 prefixEnd_7778422 3994069219506871121852695 := by
  unfold tailWord_7778422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731397339132063597469095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189134904950742011706337013 17731397339132063597469095)
  ·
    refine ⟨26597096008698095396203643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17731397339132063597469095 26597096008698095396203643)
    ·
      refine ⟨39895644013047143094305465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26597096008698095396203643 39895644013047143094305465)
      ·
        refine ⟨29921733009785357320729099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39895644013047143094305465 29921733009785357320729099)
        ·
          refine ⟨44882599514678035981093649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29921733009785357320729099 44882599514678035981093649)
          ·
            refine ⟨33661949636008526985820237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44882599514678035981093649 33661949636008526985820237)
            ·
              refine ⟨12623231113503197619682589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33661949636008526985820237 12623231113503197619682589)
              ·
                refine ⟨4733711667563699107380971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12623231113503197619682589 4733711667563699107380971)
                ·
                  refine ⟨7100567501345548661071457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733711667563699107380971 7100567501345548661071457)
                  ·
                    refine ⟨5325425626009161495803593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7100567501345548661071457 5325425626009161495803593)
                    ·
                      refine ⟨3994069219506871121852695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325425626009161495803593 3994069219506871121852695)
                      ·
                        rfl

theorem cell23_7778422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_7778422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778422 prefixEnd_7778422 := by exact prefixLift 7778422
  have htrace : WordTrace (prefixWord ++ tailWord_7778422) baseStart_7778422 baseEnd_7778422 := by
    simpa [prefixWord, tailWord_7778422, baseEnd_7778422] using wordTrace_append hprefix tailTrace_7778422
  have hstable : (prefixWord ++ tailWord_7778422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778422).length < 2 ^ (prefixWord ++ tailWord_7778422).sum := by decide
  have hdescent : baseEnd_7778422 < baseStart_7778422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778427 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 4]
def baseStart_7778427 : Nat := 118140960795 + 7778427 * 2 ^ 59
def prefixEnd_7778427 : Nat := 4983230072969 + 3 ^ 40 * 7778427 * 2
def baseEnd_7778427 : Nat := 3994071786910143602290171

theorem tailTrace_7778427 : CollatzResearch.WordTrace tailWord_7778427 prefixEnd_7778427 3994071786910143602290171 := by
  unfold tailWord_7778427
  simp only [CollatzResearch.WordTrace]
  refine ⟨283702539791094903413437535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189135026527396602275625023 283702539791094903413437535)
  ·
    refine ⟨425553809686642355120156303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283702539791094903413437535 425553809686642355120156303)
    ·
      refine ⟨638330714529963532680234455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425553809686642355120156303 638330714529963532680234455)
      ·
        refine ⟨957496071794945299020351683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638330714529963532680234455 957496071794945299020351683)
        ·
          refine ⟨1436244107692417948530527525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957496071794945299020351683 1436244107692417948530527525)
          ·
            refine ⟨269295770192328365349473911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1436244107692417948530527525 269295770192328365349473911)
            ·
              refine ⟨403943655288492548024210867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269295770192328365349473911 403943655288492548024210867)
              ·
                refine ⟨605915482932738822036316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403943655288492548024210867 605915482932738822036316301)
                ·
                  refine ⟨227218306099777058263618613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605915482932738822036316301 227218306099777058263618613)
                  ·
                    refine ⟨21301716196854099212214245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 227218306099777058263618613 21301716196854099212214245)
                    ·
                      refine ⟨3994071786910143602290171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21301716196854099212214245 3994071786910143602290171)
                      ·
                        rfl

theorem cell23_7778427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 4].length) (baseStart_7778427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778427 prefixEnd_7778427 := by exact prefixLift 7778427
  have htrace : WordTrace (prefixWord ++ tailWord_7778427) baseStart_7778427 baseEnd_7778427 := by
    simpa [prefixWord, tailWord_7778427, baseEnd_7778427] using wordTrace_append hprefix tailTrace_7778427
  have hstable : (prefixWord ++ tailWord_7778427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778427).length < 2 ^ (prefixWord ++ tailWord_7778427).sum := by decide
  have hdescent : baseEnd_7778427 < baseStart_7778427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778457 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_7778457 : Nat := 118140960795 + 7778457 * 2 ^ 59
def prefixEnd_7778457 : Nat := 4983230072969 + 3 ^ 40 * 7778457 * 2
def baseEnd_7778457 : Nat := 3994087191329778484915033

theorem tailTrace_7778457 : CollatzResearch.WordTrace tailWord_7778457 prefixEnd_7778457 3994087191329778484915033 := by
  unfold tailWord_7778457
  simp only [CollatzResearch.WordTrace]
  refine ⟨283703633980986218537029625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189135755987324145691353083 283703633980986218537029625)
  ·
    refine ⟨212777725485739663902772219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283703633980986218537029625 212777725485739663902772219)
    ·
      refine ⟨319166588228609495854158329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212777725485739663902772219 319166588228609495854158329)
      ·
        refine ⟨239374941171457121890618747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319166588228609495854158329 239374941171457121890618747)
        ·
          refine ⟨359062411757185682835928121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239374941171457121890618747 359062411757185682835928121)
          ·
            refine ⟨269296808817889262126946091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359062411757185682835928121 269296808817889262126946091)
            ·
              refine ⟨403945213226833893190419137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269296808817889262126946091 403945213226833893190419137)
              ·
                refine ⟨302958909920125419892814353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403945213226833893190419137 302958909920125419892814353)
                ·
                  refine ⟨227219182440094064919610765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302958909920125419892814353 227219182440094064919610765)
                  ·
                    refine ⟨85207193415035274344854037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227219182440094064919610765 85207193415035274344854037)
                    ·
                      refine ⟨3994087191329778484915033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85207193415035274344854037 3994087191329778484915033)
                      ·
                        rfl

theorem cell23_7778457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_7778457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778457 prefixEnd_7778457 := by exact prefixLift 7778457
  have htrace : WordTrace (prefixWord ++ tailWord_7778457) baseStart_7778457 baseEnd_7778457 := by
    simpa [prefixWord, tailWord_7778457, baseEnd_7778457] using wordTrace_append hprefix tailTrace_7778457
  have hstable : (prefixWord ++ tailWord_7778457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778457).length < 2 ^ (prefixWord ++ tailWord_7778457).sum := by decide
  have hdescent : baseEnd_7778457 < baseStart_7778457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778464 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_7778464 : Nat := 118140960795 + 7778464 * 2 ^ 59
def prefixEnd_7778464 : Nat := 4983230072969 + 3 ^ 40 * 7778464 * 2
def baseEnd_7778464 : Nat := 3994090785694359957527501

theorem tailTrace_7778464 : CollatzResearch.WordTrace tailWord_7778464 prefixEnd_7778464 3994090785694359957527501 := by
  unfold tailWord_7778464
  simp only [CollatzResearch.WordTrace]
  refine ⟨141851944645980429366267223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189135926194640572488356297 141851944645980429366267223)
  ·
    refine ⟨212777916968970644049400835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141851944645980429366267223 212777916968970644049400835)
    ·
      refine ⟨319166875453455966074101253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212777916968970644049400835 319166875453455966074101253)
      ·
        refine ⟨59843789147522993638893985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319166875453455966074101253 59843789147522993638893985)
        ·
          refine ⟨44882841860642245229170489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59843789147522993638893985 44882841860642245229170489)
          ·
            refine ⟨33662131395481683921877867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44882841860642245229170489 33662131395481683921877867)
            ·
              refine ⟨50493197093222525882816801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33662131395481683921877867 50493197093222525882816801)
              ·
                refine ⟨37869897819916894412112601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50493197093222525882816801 37869897819916894412112601)
                ·
                  refine ⟨28402423364937670809084451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37869897819916894412112601 28402423364937670809084451)
                  ·
                    refine ⟨42603635047406506213626677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28402423364937670809084451 42603635047406506213626677)
                    ·
                      refine ⟨3994090785694359957527501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42603635047406506213626677 3994090785694359957527501)
                      ·
                        rfl

theorem cell23_7778464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_7778464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778464 prefixEnd_7778464 := by exact prefixLift 7778464
  have htrace : WordTrace (prefixWord ++ tailWord_7778464) baseStart_7778464 baseEnd_7778464 := by
    simpa [prefixWord, tailWord_7778464, baseEnd_7778464] using wordTrace_append hprefix tailTrace_7778464
  have hstable : (prefixWord ++ tailWord_7778464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778464).length < 2 ^ (prefixWord ++ tailWord_7778464).sum := by decide
  have hdescent : baseEnd_7778464 < baseStart_7778464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778465 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_7778465 : Nat := 118140960795 + 7778465 * 2 ^ 59
def prefixEnd_7778465 : Nat := 4983230072969 + 3 ^ 40 * 7778465 * 2
def baseEnd_7778465 : Nat := 3994091299175014453614997

theorem tailTrace_7778465 : CollatzResearch.WordTrace tailWord_7778465 prefixEnd_7778465 3994091299175014453614997 := by
  unfold tailWord_7778465
  simp only [CollatzResearch.WordTrace]
  refine ⟨283703925764957235903320849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189135950509971490602213899 283703925764957235903320849)
  ·
    refine ⟨212777944323717926927490637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283703925764957235903320849 212777944323717926927490637)
    ·
      refine ⟨79791729121394222597808989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212777944323717926927490637 79791729121394222597808989)
      ·
        refine ⟨29921898420522833474178371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79791729121394222597808989 29921898420522833474178371)
        ·
          refine ⟨44882847630784250211267557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29921898420522833474178371 44882847630784250211267557)
          ·
            refine ⟨8415533930772046914612667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44882847630784250211267557 8415533930772046914612667)
            ·
              refine ⟨12623300896158070371919001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8415533930772046914612667 12623300896158070371919001)
              ·
                refine ⟨9467475672118552778939251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12623300896158070371919001 9467475672118552778939251)
                ·
                  refine ⟨14201213508177829168408877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9467475672118552778939251 14201213508177829168408877)
                  ·
                    refine ⟨5325455065566685938153329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14201213508177829168408877 5325455065566685938153329)
                    ·
                      refine ⟨3994091299175014453614997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325455065566685938153329 3994091299175014453614997)
                      ·
                        rfl

theorem cell23_7778465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_7778465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778465 prefixEnd_7778465 := by exact prefixLift 7778465
  have htrace : WordTrace (prefixWord ++ tailWord_7778465) baseStart_7778465 baseEnd_7778465 := by
    simpa [prefixWord, tailWord_7778465, baseEnd_7778465] using wordTrace_append hprefix tailTrace_7778465
  have hstable : (prefixWord ++ tailWord_7778465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778465).length < 2 ^ (prefixWord ++ tailWord_7778465).sum := by decide
  have hdescent : baseEnd_7778465 < baseStart_7778465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778508 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7778508 : Nat := 118140960795 + 7778508 * 2 ^ 59
def prefixEnd_7778508 : Nat := 4983230072969 + 3 ^ 40 * 7778508 * 2
def baseEnd_7778508 : Nat := 3994113378843157785377299

theorem tailTrace_7778508 : CollatzResearch.WordTrace tailWord_7778508 prefixEnd_7778508 3994113378843157785377299 := by
  unfold tailWord_7778508
  simp only [CollatzResearch.WordTrace]
  refine ⟨141852747051900727123568089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189136996069200969498090785 141852747051900727123568089)
  ·
    refine ⟨106389560288925545342676067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141852747051900727123568089 106389560288925545342676067)
    ·
      refine ⟨159584340433388318014014101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106389560288925545342676067 159584340433388318014014101)
      ·
        refine ⟨7480515957815077406906911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159584340433388318014014101 7480515957815077406906911)
        ·
          refine ⟨11220773936722616110360367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7480515957815077406906911 11220773936722616110360367)
          ·
            refine ⟨16831160905083924165540551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11220773936722616110360367 16831160905083924165540551)
            ·
              refine ⟨25246741357625886248310827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16831160905083924165540551 25246741357625886248310827)
              ·
                refine ⟨37870112036438829372466241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25246741357625886248310827 37870112036438829372466241)
                ·
                  refine ⟨28402584027329122029349681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37870112036438829372466241 28402584027329122029349681)
                  ·
                    refine ⟨21301938020496841522012261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28402584027329122029349681 21301938020496841522012261)
                    ·
                      refine ⟨3994113378843157785377299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21301938020496841522012261 3994113378843157785377299)
                      ·
                        rfl

theorem cell23_7778508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7778508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778508 prefixEnd_7778508 := by exact prefixLift 7778508
  have htrace : WordTrace (prefixWord ++ tailWord_7778508) baseStart_7778508 baseEnd_7778508 := by
    simpa [prefixWord, tailWord_7778508, baseEnd_7778508] using wordTrace_append hprefix tailTrace_7778508
  have hstable : (prefixWord ++ tailWord_7778508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778508).length < 2 ^ (prefixWord ++ tailWord_7778508).sum := by decide
  have hdescent : baseEnd_7778508 < baseStart_7778508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778518 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_7778518 : Nat := 118140960795 + 7778518 * 2 ^ 59
def prefixEnd_7778518 : Nat := 4983230072969 + 3 ^ 40 * 7778518 * 2
def baseEnd_7778518 : Nat := 443790945961078082916917

theorem tailTrace_7778518 : CollatzResearch.WordTrace tailWord_7778518 prefixEnd_7778518 443790945961078082916917 := by
  unfold tailWord_7778518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731616177110326622187513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189137239222510150636666805 17731616177110326622187513)
  ·
    refine ⟨13298712132832744966640635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17731616177110326622187513 13298712132832744966640635)
    ·
      refine ⟨19948068199249117449960953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13298712132832744966640635 19948068199249117449960953)
      ·
        refine ⟨14961051149436838087470715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19948068199249117449960953 14961051149436838087470715)
        ·
          refine ⟨22441576724155257131206073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14961051149436838087470715 22441576724155257131206073)
          ·
            refine ⟨16831182543116442848404555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22441576724155257131206073 16831182543116442848404555)
            ·
              refine ⟨25246773814674664272606833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16831182543116442848404555 25246773814674664272606833)
              ·
                refine ⟨18935080361005998204455125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25246773814674664272606833 18935080361005998204455125)
                ·
                  refine ⟨443790945961078082916917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18935080361005998204455125 443790945961078082916917)
                  ·
                    rfl

theorem cell23_7778518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_7778518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778518 prefixEnd_7778518 := by exact prefixLift 7778518
  have htrace : WordTrace (prefixWord ++ tailWord_7778518) baseStart_7778518 baseEnd_7778518 := by
    simpa [prefixWord, tailWord_7778518, baseEnd_7778518] using wordTrace_append hprefix tailTrace_7778518
  have hstable : (prefixWord ++ tailWord_7778518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778518).length < 2 ^ (prefixWord ++ tailWord_7778518).sum := by decide
  have hdescent : baseEnd_7778518 < baseStart_7778518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778568 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_7778568 : Nat := 118140960795 + 7778568 * 2 ^ 59
def prefixEnd_7778568 : Nat := 4983230072969 + 3 ^ 40 * 7778568 * 2
def baseEnd_7778568 : Nat := 3994144187682427550627023

theorem tailTrace_7778568 : CollatzResearch.WordTrace tailWord_7778568 prefixEnd_7778568 3994144187682427550627023 := by
  unfold tailWord_7778568
  simp only [CollatzResearch.WordTrace]
  refine ⟨141853841241792042247160179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189138454989056056329546905 141853841241792042247160179)
  ·
    refine ⟨212780761862688063370740269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141853841241792042247160179 212780761862688063370740269)
    ·
      refine ⟨79792785698508023764027601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212780761862688063370740269 79792785698508023764027601)
      ·
        refine ⟨59844589273881017823020701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79792785698508023764027601 59844589273881017823020701)
        ·
          refine ⟨22441720977705381683632763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59844589273881017823020701 22441720977705381683632763)
          ·
            refine ⟨33662581466558072525449145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22441720977705381683632763 33662581466558072525449145)
            ·
              refine ⟨25246936099918554394086859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33662581466558072525449145 25246936099918554394086859)
              ·
                refine ⟨37870404149877831591130289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25246936099918554394086859 37870404149877831591130289)
                ·
                  refine ⟨28402803112408373693347717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37870404149877831591130289 28402803112408373693347717)
                  ·
                    refine ⟨5325525583576570067502697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28402803112408373693347717 5325525583576570067502697)
                    ·
                      refine ⟨3994144187682427550627023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325525583576570067502697 3994144187682427550627023)
                      ·
                        rfl

theorem cell23_7778568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_7778568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778568 prefixEnd_7778568 := by exact prefixLift 7778568
  have htrace : WordTrace (prefixWord ++ tailWord_7778568) baseStart_7778568 baseEnd_7778568 := by
    simpa [prefixWord, tailWord_7778568, baseEnd_7778568] using wordTrace_append hprefix tailTrace_7778568
  have hstable : (prefixWord ++ tailWord_7778568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778568).length < 2 ^ (prefixWord ++ tailWord_7778568).sum := by decide
  have hdescent : baseEnd_7778568 < baseStart_7778568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778712 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 1, 2, 3]
def baseStart_7778712 : Nat := 118140960795 + 7778712 * 2 ^ 59
def prefixEnd_7778712 : Nat := 4983230072969 + 3 ^ 40 * 7778712 * 2
def baseEnd_7778712 : Nat := 3994218128896674987226361

theorem tailTrace_7778712 : CollatzResearch.WordTrace tailWord_7778712 prefixEnd_7778712 3994218128896674987226361 := by
  unfold tailWord_7778712
  simp only [CollatzResearch.WordTrace]
  refine ⟨141856467297531198543781195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189141956396708264725041593 141856467297531198543781195)
  ·
    refine ⟨212784700946296797815671793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141856467297531198543781195 212784700946296797815671793)
    ·
      refine ⟨159588525709722598361753845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212784700946296797815671793 159588525709722598361753845)
      ·
        refine ⟨14961424285286493596414423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159588525709722598361753845 14961424285286493596414423)
        ·
          refine ⟨22442136427929740394621635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14961424285286493596414423 22442136427929740394621635)
          ·
            refine ⟨33663204641894610591932453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22442136427929740394621635 33663204641894610591932453)
            ·
              refine ⟨6311850870355239485987335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33663204641894610591932453 6311850870355239485987335)
              ·
                refine ⟨9467776305532859228981003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311850870355239485987335 9467776305532859228981003)
                ·
                  refine ⟨14201664458299288843471505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9467776305532859228981003 14201664458299288843471505)
                  ·
                    refine ⟨10651248343724466632603629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14201664458299288843471505 10651248343724466632603629)
                    ·
                      refine ⟨3994218128896674987226361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10651248343724466632603629 3994218128896674987226361)
                      ·
                        rfl

theorem cell23_7778712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_7778712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778712 prefixEnd_7778712 := by exact prefixLift 7778712
  have htrace : WordTrace (prefixWord ++ tailWord_7778712) baseStart_7778712 baseEnd_7778712 := by
    simpa [prefixWord, tailWord_7778712, baseEnd_7778712] using wordTrace_append hprefix tailTrace_7778712
  have hstable : (prefixWord ++ tailWord_7778712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778712).length < 2 ^ (prefixWord ++ tailWord_7778712).sum := by decide
  have hdescent : baseEnd_7778712 < baseStart_7778712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778761 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_7778761 : Nat := 118140960795 + 7778761 * 2 ^ 59
def prefixEnd_7778761 : Nat := 4983230072969 + 3 ^ 40 * 7778761 * 2
def baseEnd_7778761 : Nat := 3994243289448745295513635

theorem tailTrace_7778761 : CollatzResearch.WordTrace tailWord_7778761 prefixEnd_7778761 3994243289448745295513635 := by
  unfold tailWord_7778761
  simp only [CollatzResearch.WordTrace]
  refine ⟨283714721771884878456096137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189143147847923252304064091 283714721771884878456096137)
  ·
    refine ⟨212786041328913658842072103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283714721771884878456096137 212786041328913658842072103)
    ·
      refine ⟨319179061993370488263108155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212786041328913658842072103 319179061993370488263108155)
      ·
        refine ⟨478768592990055732394662233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319179061993370488263108155 478768592990055732394662233)
        ·
          refine ⟨359076444742541799295996675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478768592990055732394662233 359076444742541799295996675)
          ·
            refine ⟨538614667113812698943995013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359076444742541799295996675 538614667113812698943995013)
            ·
              refine ⟨100990250083839881051999065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538614667113812698943995013 100990250083839881051999065)
              ·
                refine ⟨75742687562879910788999299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100990250083839881051999065 75742687562879910788999299)
                ·
                  refine ⟨113614031344319866183498949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75742687562879910788999299 113614031344319866183498949)
                  ·
                    refine ⟨21302630877059974909406053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113614031344319866183498949 21302630877059974909406053)
                    ·
                      refine ⟨3994243289448745295513635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21302630877059974909406053 3994243289448745295513635)
                      ·
                        rfl

theorem cell23_7778761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_7778761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778761 prefixEnd_7778761 := by exact prefixLift 7778761
  have htrace : WordTrace (prefixWord ++ tailWord_7778761) baseStart_7778761 baseEnd_7778761 := by
    simpa [prefixWord, tailWord_7778761, baseEnd_7778761] using wordTrace_append hprefix tailTrace_7778761
  have hstable : (prefixWord ++ tailWord_7778761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778761).length < 2 ^ (prefixWord ++ tailWord_7778761).sum := by decide
  have hdescent : baseEnd_7778761 < baseStart_7778761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778811 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 5]
def baseStart_7778811 : Nat := 118140960795 + 7778811 * 2 ^ 59
def prefixEnd_7778811 : Nat := 4983230072969 + 3 ^ 40 * 7778811 * 2
def baseEnd_7778811 : Nat := 3994268963481470099888405

theorem tailTrace_7778811 : CollatzResearch.WordTrace tailWord_7778811 prefixEnd_7778811 3994268963481470099888405 := by
  unfold tailWord_7778811
  simp only [CollatzResearch.WordTrace]
  refine ⟨283716545421703736995416287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189144363614469157996944191 283716545421703736995416287)
  ·
    refine ⟨425574818132555605493124431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283716545421703736995416287 425574818132555605493124431)
    ·
      refine ⟨638362227198833408239686647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425574818132555605493124431 638362227198833408239686647)
      ·
        refine ⟨957543340798250112359529971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638362227198833408239686647 957543340798250112359529971)
        ·
          refine ⟨1436315011197375168539294957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957543340798250112359529971 1436315011197375168539294957)
          ·
            refine ⟨538618129199015688202235609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1436315011197375168539294957 538618129199015688202235609)
            ·
              refine ⟨403963596899261766151676707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538618129199015688202235609 403963596899261766151676707)
              ·
                refine ⟨605945395348892649227515061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403963596899261766151676707 605945395348892649227515061)
                ·
                  refine ⟨56807380813958685865079537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605945395348892649227515061 56807380813958685865079537)
                  ·
                    refine ⟨42605535610469014398809653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56807380813958685865079537 42605535610469014398809653)
                    ·
                      refine ⟨3994268963481470099888405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42605535610469014398809653 3994268963481470099888405)
                      ·
                        rfl

theorem cell23_7778811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_7778811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778811 prefixEnd_7778811 := by exact prefixLift 7778811
  have htrace : WordTrace (prefixWord ++ tailWord_7778811) baseStart_7778811 baseEnd_7778811 := by
    simpa [prefixWord, tailWord_7778811, baseEnd_7778811] using wordTrace_append hprefix tailTrace_7778811
  have hstable : (prefixWord ++ tailWord_7778811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778811).length < 2 ^ (prefixWord ++ tailWord_7778811).sum := by decide
  have hdescent : baseEnd_7778811 < baseStart_7778811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778828 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_7778828 : Nat := 118140960795 + 7778828 * 2 ^ 59
def prefixEnd_7778828 : Nat := 4983230072969 + 3 ^ 40 * 7778828 * 2
def baseEnd_7778828 : Nat := 3994277692652596533375827

theorem tailTrace_7778828 : CollatzResearch.WordTrace tailWord_7778828 prefixEnd_7778828 3994277692652596533375827 := by
  unfold tailWord_7778828
  simp only [CollatzResearch.WordTrace]
  refine ⟨141858582731321074449392569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189144776975094765932523425 141858582731321074449392569)
  ·
    refine ⟨106393937048490805837044427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141858582731321074449392569 106393937048490805837044427)
    ·
      refine ⟨159590905572736208755566641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106393937048490805837044427 159590905572736208755566641)
      ·
        refine ⟨119693179179552156566674981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159590905572736208755566641 119693179179552156566674981)
        ·
          refine ⟨22442471096166029356251559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119693179179552156566674981 22442471096166029356251559)
          ·
            refine ⟨33663706644249044034377339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22442471096166029356251559 33663706644249044034377339)
            ·
              refine ⟨50495559966373566051566009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33663706644249044034377339 50495559966373566051566009)
              ·
                refine ⟨37871669974780174538674507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50495559966373566051566009 37871669974780174538674507)
                ·
                  refine ⟨56807504962170261808011761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37871669974780174538674507 56807504962170261808011761)
                  ·
                    refine ⟨42605628721627696356008821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56807504962170261808011761 42605628721627696356008821)
                    ·
                      refine ⟨3994277692652596533375827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42605628721627696356008821 3994277692652596533375827)
                      ·
                        rfl

theorem cell23_7778828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_7778828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778828 prefixEnd_7778828 := by exact prefixLift 7778828
  have htrace : WordTrace (prefixWord ++ tailWord_7778828) baseStart_7778828 baseEnd_7778828 := by
    simpa [prefixWord, tailWord_7778828, baseEnd_7778828] using wordTrace_append hprefix tailTrace_7778828
  have hstable : (prefixWord ++ tailWord_7778828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778828).length < 2 ^ (prefixWord ++ tailWord_7778828).sum := by decide
  have hdescent : baseEnd_7778828 < baseStart_7778828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778888 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_7778888 : Nat := 118140960795 + 7778888 * 2 ^ 59
def prefixEnd_7778888 : Nat := 4983230072969 + 3 ^ 40 * 7778888 * 2
def baseEnd_7778888 : Nat := 3994308501491866298625551

theorem tailTrace_7778888 : CollatzResearch.WordTrace tailWord_7778888 prefixEnd_7778888 3994308501491866298625551 := by
  unfold tailWord_7778888
  simp only [CollatzResearch.WordTrace]
  refine ⟨141859676921212389572984659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189146235894949852763979545 141859676921212389572984659)
  ·
    refine ⟨212789515381818584359476989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141859676921212389572984659 212789515381818584359476989)
    ·
      refine ⟨79796068268181969134803871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212789515381818584359476989 79796068268181969134803871)
      ·
        refine ⟨119694102402272953702205807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79796068268181969134803871 119694102402272953702205807)
        ·
          refine ⟨179541153603409430553308711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119694102402272953702205807 179541153603409430553308711)
          ·
            refine ⟨269311730405114145829963067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179541153603409430553308711 269311730405114145829963067)
            ·
              refine ⟨403967595607671218744944601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269311730405114145829963067 403967595607671218744944601)
              ·
                refine ⟨302975696705753414058708451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403967595607671218744944601 302975696705753414058708451)
                ·
                  refine ⟨454463545058630121088062677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302975696705753414058708451 454463545058630121088062677)
                  ·
                    refine ⟨10651489337311643463001469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 454463545058630121088062677 10651489337311643463001469)
                    ·
                      refine ⟨3994308501491866298625551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10651489337311643463001469 3994308501491866298625551)
                      ·
                        rfl

theorem cell23_7778888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_7778888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778888 prefixEnd_7778888 := by exact prefixLift 7778888
  have htrace : WordTrace (prefixWord ++ tailWord_7778888) baseStart_7778888 baseEnd_7778888 := by
    simpa [prefixWord, tailWord_7778888, baseEnd_7778888] using wordTrace_append hprefix tailTrace_7778888
  have hstable : (prefixWord ++ tailWord_7778888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778888).length < 2 ^ (prefixWord ++ tailWord_7778888).sum := by decide
  have hdescent : baseEnd_7778888 < baseStart_7778888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778898 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_7778898 : Nat := 118140960795 + 7778898 * 2 ^ 59
def prefixEnd_7778898 : Nat := 4983230072969 + 3 ^ 40 * 7778898 * 2
def baseEnd_7778898 : Nat := 3994313636298411259500505

theorem tailTrace_7778898 : CollatzResearch.WordTrace tailWord_7778898 prefixEnd_7778898 3994313636298411259500505 := by
  unfold tailWord_7778898
  simp only [CollatzResearch.WordTrace]
  refine ⟨70929929643097137713458337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189146479048259033902555565 70929929643097137713458337)
  ·
    refine ⟨53197447232322853285093753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70929929643097137713458337 53197447232322853285093753)
    ·
      refine ⟨39898085424242139963820315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53197447232322853285093753 39898085424242139963820315)
      ·
        refine ⟨59847128136363209945730473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39898085424242139963820315 59847128136363209945730473)
        ·
          refine ⟨44885346102272407459297855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59847128136363209945730473 44885346102272407459297855)
          ·
            refine ⟨67328019153408611188946783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44885346102272407459297855 67328019153408611188946783)
            ·
              refine ⟨100992028730112916783420175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67328019153408611188946783 100992028730112916783420175)
              ·
                refine ⟨151488043095169375175130263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100992028730112916783420175 151488043095169375175130263)
                ·
                  refine ⟨227232064642754062762695395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151488043095169375175130263 227232064642754062762695395)
                  ·
                    refine ⟨340848096964131094144043093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227232064642754062762695395 340848096964131094144043093)
                    ·
                      refine ⟨3994313636298411259500505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 340848096964131094144043093 3994313636298411259500505)
                      ·
                        rfl

theorem cell23_7778898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_7778898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778898 prefixEnd_7778898 := by exact prefixLift 7778898
  have htrace : WordTrace (prefixWord ++ tailWord_7778898) baseStart_7778898 baseEnd_7778898 := by
    simpa [prefixWord, tailWord_7778898, baseEnd_7778898] using wordTrace_append hprefix tailTrace_7778898
  have hstable : (prefixWord ++ tailWord_7778898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778898).length < 2 ^ (prefixWord ++ tailWord_7778898).sum := by decide
  have hdescent : baseEnd_7778898 < baseStart_7778898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778915 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 3, 5, 2]
def baseStart_7778915 : Nat := 118140960795 + 7778915 * 2 ^ 59
def prefixEnd_7778915 : Nat := 4983230072969 + 3 ^ 40 * 7778915 * 2
def baseEnd_7778915 : Nat := 3994322365469537692987927

theorem tailTrace_7778915 : CollatzResearch.WordTrace tailWord_7778915 prefixEnd_7778915 3994322365469537692987927 := by
  unfold tailWord_7778915
  simp only [CollatzResearch.WordTrace]
  refine ⟨283720338613326962757202199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189146892408884641838134799 283720338613326962757202199)
  ·
    refine ⟨425580507919990444135803299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283720338613326962757202199 425580507919990444135803299)
    ·
      refine ⟨638370761879985666203704949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425580507919990444135803299 638370761879985666203704949)
      ·
        refine ⟨59847258926248656206597339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 638370761879985666203704949 59847258926248656206597339)
        ·
          refine ⟨89770888389372984309896009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59847258926248656206597339 89770888389372984309896009)
          ·
            refine ⟨67328166292029738232422007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89770888389372984309896009 67328166292029738232422007)
            ·
              refine ⟨100992249438044607348633011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67328166292029738232422007 100992249438044607348633011)
              ·
                refine ⟨151488374157066911022949517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100992249438044607348633011 151488374157066911022949517)
                ·
                  refine ⟨56808140308900091633606069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151488374157066911022949517 56808140308900091633606069)
                  ·
                    refine ⟨5325763153959383590650569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56808140308900091633606069 5325763153959383590650569)
                    ·
                      refine ⟨3994322365469537692987927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325763153959383590650569 3994322365469537692987927)
                      ·
                        rfl

theorem cell23_7778915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_7778915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778915 prefixEnd_7778915 := by exact prefixLift 7778915
  have htrace : WordTrace (prefixWord ++ tailWord_7778915) baseStart_7778915 baseEnd_7778915 := by
    simpa [prefixWord, tailWord_7778915, baseEnd_7778915] using wordTrace_append hprefix tailTrace_7778915
  have hstable : (prefixWord ++ tailWord_7778915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778915).length < 2 ^ (prefixWord ++ tailWord_7778915).sum := by decide
  have hdescent : baseEnd_7778915 < baseStart_7778915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778922 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_7778922 : Nat := 118140960795 + 7778922 * 2 ^ 59
def prefixEnd_7778922 : Nat := 4983230072969 + 3 ^ 40 * 7778922 * 2
def baseEnd_7778922 : Nat := 3994325959834119165600395

theorem tailTrace_7778922 : CollatzResearch.WordTrace tailWord_7778922 prefixEnd_7778922 3994325959834119165600395 := by
  unfold tailWord_7778922
  simp only [CollatzResearch.WordTrace]
  refine ⟨70930148481075400738176755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189147062616201068635138013 70930148481075400738176755)
  ·
    refine ⟨106395222721613101107265133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70930148481075400738176755 106395222721613101107265133)
    ·
      refine ⟨39898208520604912915224425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106395222721613101107265133 39898208520604912915224425)
      ·
        refine ⟨29923656390453684686418319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39898208520604912915224425 29923656390453684686418319)
        ·
          refine ⟨44885484585680527029627479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29923656390453684686418319 44885484585680527029627479)
          ·
            refine ⟨67328226878520790544441219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44885484585680527029627479 67328226878520790544441219)
            ·
              refine ⟨100992340317781185816661829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67328226878520790544441219 100992340317781185816661829)
              ·
                refine ⟨18936063809583972340624093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100992340317781185816661829 18936063809583972340624093)
                ·
                  refine ⟨7101023928593989627734035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18936063809583972340624093 7101023928593989627734035)
                  ·
                    refine ⟨10651535892890984441601053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7101023928593989627734035 10651535892890984441601053)
                    ·
                      refine ⟨3994325959834119165600395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10651535892890984441601053 3994325959834119165600395)
                      ·
                        rfl

theorem cell23_7778922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_7778922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778922 prefixEnd_7778922 := by exact prefixLift 7778922
  have htrace : WordTrace (prefixWord ++ tailWord_7778922) baseStart_7778922 baseEnd_7778922 := by
    simpa [prefixWord, tailWord_7778922, baseEnd_7778922] using wordTrace_append hprefix tailTrace_7778922
  have hstable : (prefixWord ++ tailWord_7778922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778922).length < 2 ^ (prefixWord ++ tailWord_7778922).sum := by decide
  have hdescent : baseEnd_7778922 < baseStart_7778922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778933 : List Nat := [1, 3, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_7778933 : Nat := 118140960795 + 7778933 * 2 ^ 59
def prefixEnd_7778933 : Nat := 4983230072969 + 3 ^ 40 * 7778933 * 2
def baseEnd_7778933 : Nat := 1331443869373772874187615

theorem tailTrace_7778933 : CollatzResearch.WordTrace tailWord_7778933 prefixEnd_7778933 1331443869373772874187615 := by
  unfold tailWord_7778933
  simp only [CollatzResearch.WordTrace]
  refine ⟨283720995127261751831357453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189147330084841167887571635 283720995127261751831357453)
  ·
    refine ⟨106395373172723156936759045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283720995127261751831357453 106395373172723156936759045)
    ·
      refine ⟨19949132469885591925642321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106395373172723156936759045 19949132469885591925642321)
      ·
        refine ⟨14961849352414193944231741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19949132469885591925642321 14961849352414193944231741)
        ·
          refine ⟨5610693507155322729086903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14961849352414193944231741 5610693507155322729086903)
          ·
            refine ⟨8416040260732984093630355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5610693507155322729086903 8416040260732984093630355)
            ·
              refine ⟨12624060391099476140445533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416040260732984093630355 12624060391099476140445533)
              ·
                refine ⟨4734022646662303552667075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12624060391099476140445533 4734022646662303552667075)
                ·
                  refine ⟨7101033969993455329000613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4734022646662303552667075 7101033969993455329000613)
                  ·
                    refine ⟨1331443869373772874187615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7101033969993455329000613 1331443869373772874187615)
                    ·
                      rfl

theorem cell23_7778933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_7778933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778933 prefixEnd_7778933 := by exact prefixLift 7778933
  have htrace : WordTrace (prefixWord ++ tailWord_7778933) baseStart_7778933 baseEnd_7778933 := by
    simpa [prefixWord, tailWord_7778933, baseEnd_7778933] using wordTrace_append hprefix tailTrace_7778933
  have hstable : (prefixWord ++ tailWord_7778933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778933).length < 2 ^ (prefixWord ++ tailWord_7778933).sum := by decide
  have hdescent : baseEnd_7778933 < baseStart_7778933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778995 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 3]
def baseStart_7778995 : Nat := 118140960795 + 7778995 * 2 ^ 59
def prefixEnd_7778995 : Nat := 4983230072969 + 3 ^ 40 * 7778995 * 2
def baseEnd_7778995 : Nat := 3994363443921897379987559

theorem tailTrace_7778995 : CollatzResearch.WordTrace tailWord_7778995 prefixEnd_7778995 3994363443921897379987559 := by
  unfold tailWord_7778995
  simp only [CollatzResearch.WordTrace]
  refine ⟨283723256453037136420114439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189148837635358090946742959 283723256453037136420114439)
  ·
    refine ⟨425584884679555704630171659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283723256453037136420114439 425584884679555704630171659)
    ·
      refine ⟨638377327019333556945257489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425584884679555704630171659 638377327019333556945257489)
      ·
        refine ⟨478782995264500167708943117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638377327019333556945257489 478782995264500167708943117)
        ·
          refine ⟨179543623224187562890853669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478782995264500167708943117 179543623224187562890853669)
          ·
            refine ⟨33664429354535168042035063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179543623224187562890853669 33664429354535168042035063)
            ·
              refine ⟨50496644031802752063052595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33664429354535168042035063 50496644031802752063052595)
              ·
                refine ⟨75744966047704128094578893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50496644031802752063052595 75744966047704128094578893)
                ·
                  refine ⟨28404362267889048035467085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75744966047704128094578893 28404362267889048035467085)
                  ·
                    refine ⟨10651635850458393013300157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28404362267889048035467085 10651635850458393013300157)
                    ·
                      refine ⟨3994363443921897379987559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10651635850458393013300157 3994363443921897379987559)
                      ·
                        rfl

theorem cell23_7778995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_7778995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778995 prefixEnd_7778995 := by exact prefixLift 7778995
  have htrace : WordTrace (prefixWord ++ tailWord_7778995) baseStart_7778995 baseEnd_7778995 := by
    simpa [prefixWord, tailWord_7778995, baseEnd_7778995] using wordTrace_append hprefix tailTrace_7778995
  have hstable : (prefixWord ++ tailWord_7778995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778995).length < 2 ^ (prefixWord ++ tailWord_7778995).sum := by decide
  have hdescent : baseEnd_7778995 < baseStart_7778995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7778999 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 1, 1, 5]
def baseStart_7778999 : Nat := 118140960795 + 7778999 * 2 ^ 59
def prefixEnd_7778999 : Nat := 4983230072969 + 3 ^ 40 * 7778999 * 2
def baseEnd_7778999 : Nat := 3994365497844515364337541

theorem tailTrace_7778999 : CollatzResearch.WordTrace tailWord_7778999 prefixEnd_7778999 3994365497844515364337541 := by
  unfold tailWord_7778999
  simp only [CollatzResearch.WordTrace]
  refine ⟨283723402345022645103260051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189148934896681763402173367 283723402345022645103260051)
  ·
    refine ⟨425585103517533967654890077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283723402345022645103260051 425585103517533967654890077)
    ·
      refine ⟨159594413819075237870583779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425585103517533967654890077 159594413819075237870583779)
      ·
        refine ⟨239391620728612856805875669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159594413819075237870583779 239391620728612856805875669)
        ·
          refine ⟨5610741110826863831387711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 239391620728612856805875669 5610741110826863831387711)
          ·
            refine ⟨8416111666240295747081567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5610741110826863831387711 8416111666240295747081567)
            ·
              refine ⟨12624167499360443620622351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416111666240295747081567 12624167499360443620622351)
              ·
                refine ⟨18936251249040665430933527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12624167499360443620622351 18936251249040665430933527)
                ·
                  refine ⟨28404376873560998146400291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18936251249040665430933527 28404376873560998146400291)
                  ·
                    refine ⟨42606565310341497219600437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28404376873560998146400291 42606565310341497219600437)
                    ·
                      refine ⟨3994365497844515364337541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42606565310341497219600437 3994365497844515364337541)
                      ·
                        rfl

theorem cell23_7778999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_7778999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7778999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7778999 prefixEnd_7778999 := by exact prefixLift 7778999
  have htrace : WordTrace (prefixWord ++ tailWord_7778999) baseStart_7778999 baseEnd_7778999 := by
    simpa [prefixWord, tailWord_7778999, baseEnd_7778999] using wordTrace_append hprefix tailTrace_7778999
  have hstable : (prefixWord ++ tailWord_7778999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7778999).length < 2 ^ (prefixWord ++ tailWord_7778999).sum := by decide
  have hdescent : baseEnd_7778999 < baseStart_7778999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7778999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779069 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_7779069 : Nat := 118140960795 + 7779069 * 2 ^ 59
def prefixEnd_7779069 : Nat := 4983230072969 + 3 ^ 40 * 7779069 * 2
def baseEnd_7779069 : Nat := 3994401441490330090462219

theorem tailTrace_7779069 : CollatzResearch.WordTrace tailWord_7779069 prefixEnd_7779069 3994401441490330090462219 := by
  unfold tailWord_7779069
  simp only [CollatzResearch.WordTrace]
  refine ⟨283725955454769047058308261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189150636969846031372205507 283725955454769047058308261)
  ·
    refine ⟨53198616647769196323432799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283725955454769047058308261 53198616647769196323432799)
    ·
      refine ⟨79797924971653794485149199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53198616647769196323432799 79797924971653794485149199)
      ·
        refine ⟨119696887457480691727723799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79797924971653794485149199 119696887457480691727723799)
        ·
          refine ⟨179545331186221037591585699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119696887457480691727723799 179545331186221037591585699)
          ·
            refine ⟨269317996779331556387378549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179545331186221037591585699 269317996779331556387378549)
            ·
              refine ⟨25248562198062333411316739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269317996779331556387378549 25248562198062333411316739)
              ·
                refine ⟨37872843297093500116975109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25248562198062333411316739 37872843297093500116975109)
                ·
                  refine ⟨7101158118205031271932833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37872843297093500116975109 7101158118205031271932833)
                  ·
                    refine ⟨5325868588653773453949625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7101158118205031271932833 5325868588653773453949625)
                    ·
                      refine ⟨3994401441490330090462219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325868588653773453949625 3994401441490330090462219)
                      ·
                        rfl

theorem cell23_7779069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_7779069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779069 prefixEnd_7779069 := by exact prefixLift 7779069
  have htrace : WordTrace (prefixWord ++ tailWord_7779069) baseStart_7779069 baseEnd_7779069 := by
    simpa [prefixWord, tailWord_7779069, baseEnd_7779069] using wordTrace_append hprefix tailTrace_7779069
  have hstable : (prefixWord ++ tailWord_7779069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779069).length < 2 ^ (prefixWord ++ tailWord_7779069).sum := by decide
  have hdescent : baseEnd_7779069 < baseStart_7779069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779105 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 1, 7]
def baseStart_7779105 : Nat := 118140960795 + 7779105 * 2 ^ 59
def prefixEnd_7779105 : Nat := 4983230072969 + 3 ^ 40 * 7779105 * 2
def baseEnd_7779105 : Nat := 1331473308931297316537351

theorem tailTrace_7779105 : CollatzResearch.WordTrace tailWord_7779105 prefixEnd_7779105 1331473308931297316537351 := by
  unfold tailWord_7779105
  simp only [CollatzResearch.WordTrace]
  refine ⟨283727268482638625206618769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189151512321759083471079179 283727268482638625206618769)
  ·
    refine ⟨212795451361978968904964077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283727268482638625206618769 212795451361978968904964077)
    ·
      refine ⟨79798294260742113339361529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212795451361978968904964077 79798294260742113339361529)
      ·
        refine ⟨59848720695556585004521147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79798294260742113339361529 59848720695556585004521147)
        ·
          refine ⟨89773081043334877506781721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59848720695556585004521147 89773081043334877506781721)
          ·
            refine ⟨67329810782501158130086291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89773081043334877506781721 67329810782501158130086291)
            ·
              refine ⟨100994716173751737195129437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67329810782501158130086291 100994716173751737195129437)
              ·
                refine ⟨37873018565156901448173539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100994716173751737195129437 37873018565156901448173539)
                ·
                  refine ⟨56809527847735352172260309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37873018565156901448173539 56809527847735352172260309)
                  ·
                    refine ⟨1331473308931297316537351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56809527847735352172260309 1331473308931297316537351)
                    ·
                      rfl

theorem cell23_7779105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_7779105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779105 prefixEnd_7779105 := by exact prefixLift 7779105
  have htrace : WordTrace (prefixWord ++ tailWord_7779105) baseStart_7779105 baseEnd_7779105 := by
    simpa [prefixWord, tailWord_7779105, baseEnd_7779105] using wordTrace_append hprefix tailTrace_7779105
  have hstable : (prefixWord ++ tailWord_7779105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779105).length < 2 ^ (prefixWord ++ tailWord_7779105).sum := by decide
  have hdescent : baseEnd_7779105 < baseStart_7779105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779122 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_7779122 : Nat := 118140960795 + 7779122 * 2 ^ 59
def prefixEnd_7779122 : Nat := 4983230072969 + 3 ^ 40 * 7779122 * 2
def baseEnd_7779122 : Nat := 1331476218655006127699825

theorem tailTrace_7779122 : CollatzResearch.WordTrace tailWord_7779122 prefixEnd_7779122 1331476218655006127699825 := by
  unfold tailWord_7779122
  simp only [CollatzResearch.WordTrace]
  refine ⟨70931972130894259277496905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189151925682384691406658413 70931972130894259277496905)
  ·
    refine ⟨53198979098170694458122679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70931972130894259277496905 53198979098170694458122679)
    ·
      refine ⟨79798468647256041687184019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53198979098170694458122679 79798468647256041687184019)
      ·
        refine ⟨119697702970884062530776029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79798468647256041687184019 119697702970884062530776029)
        ·
          refine ⟨44886638614081523449041011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119697702970884062530776029 44886638614081523449041011)
          ·
            refine ⟨67329957921122285173561517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44886638614081523449041011 67329957921122285173561517)
            ·
              refine ⟨25248734220420856940085569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67329957921122285173561517 25248734220420856940085569)
              ·
                refine ⟨18936550665315642705064177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25248734220420856940085569 18936550665315642705064177)
                ·
                  refine ⟨14202412998986732028798133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18936550665315642705064177 14202412998986732028798133)
                  ·
                    refine ⟨1331476218655006127699825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14202412998986732028798133 1331476218655006127699825)
                    ·
                      rfl

theorem cell23_7779122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_7779122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779122 prefixEnd_7779122 := by exact prefixLift 7779122
  have htrace : WordTrace (prefixWord ++ tailWord_7779122) baseStart_7779122 baseEnd_7779122 := by
    simpa [prefixWord, tailWord_7779122, baseEnd_7779122] using wordTrace_append hprefix tailTrace_7779122
  have hstable : (prefixWord ++ tailWord_7779122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779122).length < 2 ^ (prefixWord ++ tailWord_7779122).sum := by decide
  have hdescent : baseEnd_7779122 < baseStart_7779122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779126 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_7779126 : Nat := 118140960795 + 7779126 * 2 ^ 59
def prefixEnd_7779126 : Nat := 4983230072969 + 3 ^ 40 * 7779126 * 2
def baseEnd_7779126 : Nat := 443825634431959596383273

theorem tailTrace_7779126 : CollatzResearch.WordTrace tailWord_7779126 prefixEnd_7779126 443825634431959596383273 := by
  unfold tailWord_7779126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733002150972659112070827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189152022943708363862088821 17733002150972659112070827)
  ·
    refine ⟨26599503226458988668106241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17733002150972659112070827 26599503226458988668106241)
    ·
      refine ⟨19949627419844241501079681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26599503226458988668106241 19949627419844241501079681)
      ·
        refine ⟨14962220564883181125809761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19949627419844241501079681 14962220564883181125809761)
        ·
          refine ⟨11221665423662385844357321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14962220564883181125809761 11221665423662385844357321)
          ·
            refine ⟨8416249067746789383267991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11221665423662385844357321 8416249067746789383267991)
            ·
              refine ⟨12624373601620184074901987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416249067746789383267991 12624373601620184074901987)
              ·
                refine ⟨18936560402430276112352981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12624373601620184074901987 18936560402430276112352981)
                ·
                  refine ⟨443825634431959596383273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18936560402430276112352981 443825634431959596383273)
                  ·
                    rfl

theorem cell23_7779126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_7779126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779126 prefixEnd_7779126 := by exact prefixLift 7779126
  have htrace : WordTrace (prefixWord ++ tailWord_7779126) baseStart_7779126 baseEnd_7779126 := by
    simpa [prefixWord, tailWord_7779126, baseEnd_7779126] using wordTrace_append hprefix tailTrace_7779126
  have hstable : (prefixWord ++ tailWord_7779126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779126).length < 2 ^ (prefixWord ++ tailWord_7779126).sum := by decide
  have hdescent : baseEnd_7779126 < baseStart_7779126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779137 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7779137 : Nat := 118140960795 + 7779137 * 2 ^ 59
def prefixEnd_7779137 : Nat := 4983230072969 + 3 ^ 40 * 7779137 * 2
def baseEnd_7779137 : Nat := 3994436358174835824411907

theorem tailTrace_7779137 : CollatzResearch.WordTrace tailWord_7779137 prefixEnd_7779137 3994436358174835824411907 := by
  unfold tailWord_7779137
  simp only [CollatzResearch.WordTrace]
  refine ⟨283728435618522694671783665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189152290412348463114522443 283728435618522694671783665)
  ·
    refine ⟨212796326713892021003837749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283728435618522694671783665 212796326713892021003837749)
    ·
      refine ⟨19949655629427376969109789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212796326713892021003837749 19949655629427376969109789)
      ·
        refine ⟨7481120861035266363416171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19949655629427376969109789 7481120861035266363416171)
        ·
          refine ⟨11221681291552899545124257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7481120861035266363416171 11221681291552899545124257)
          ·
            refine ⟨8416260968664674658843193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11221681291552899545124257 8416260968664674658843193)
            ·
              refine ⟨6312195726498505994132395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8416260968664674658843193 6312195726498505994132395)
              ·
                refine ⟨9468293589747758991198593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312195726498505994132395 9468293589747758991198593)
                ·
                  refine ⟨7101220192310819243398945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9468293589747758991198593 7101220192310819243398945)
                  ·
                    refine ⟨5325915144233114432549209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7101220192310819243398945 5325915144233114432549209)
                    ·
                      refine ⟨3994436358174835824411907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325915144233114432549209 3994436358174835824411907)
                      ·
                        rfl

theorem cell23_7779137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7779137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779137 prefixEnd_7779137 := by exact prefixLift 7779137
  have htrace : WordTrace (prefixWord ++ tailWord_7779137) baseStart_7779137 baseEnd_7779137 := by
    simpa [prefixWord, tailWord_7779137, baseEnd_7779137] using wordTrace_append hprefix tailTrace_7779137
  have hstable : (prefixWord ++ tailWord_7779137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779137).length < 2 ^ (prefixWord ++ tailWord_7779137).sum := by decide
  have hdescent : baseEnd_7779137 < baseStart_7779137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779152 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 3, 4]
def baseStart_7779152 : Nat := 118140960795 + 7779152 * 2 ^ 59
def prefixEnd_7779152 : Nat := 4983230072969 + 3 ^ 40 * 7779152 * 2
def baseEnd_7779152 : Nat := 1331481353461551088574779

theorem tailTrace_7779152 : CollatzResearch.WordTrace tailWord_7779152 prefixEnd_7779152 1331481353461551088574779 := by
  unfold tailWord_7779152
  simp only [CollatzResearch.WordTrace]
  refine ⟨141864491356734176116789855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189152655142312234822386473 141864491356734176116789855)
  ·
    refine ⟨212796737035101264175184783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141864491356734176116789855 212796737035101264175184783)
    ·
      refine ⟨319195105552651896262777175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212796737035101264175184783 319195105552651896262777175)
      ·
        refine ⟨478792658328977844394165763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319195105552651896262777175 478792658328977844394165763)
        ·
          refine ⟨718188987493466766591248645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478792658328977844394165763 718188987493466766591248645)
          ·
            refine ⟨134660435155025018735859121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 718188987493466766591248645 134660435155025018735859121)
            ·
              refine ⟨100995326366268764051894341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134660435155025018735859121 100995326366268764051894341)
              ·
                refine ⟨18936623693675393259730189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100995326366268764051894341 18936623693675393259730189)
                ·
                  refine ⟨7101233885128272472398821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18936623693675393259730189 7101233885128272472398821)
                  ·
                    refine ⟨1331481353461551088574779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7101233885128272472398821 1331481353461551088574779)
                    ·
                      rfl

theorem cell23_7779152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 4].length) (baseStart_7779152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779152 prefixEnd_7779152 := by exact prefixLift 7779152
  have htrace : WordTrace (prefixWord ++ tailWord_7779152) baseStart_7779152 baseEnd_7779152 := by
    simpa [prefixWord, tailWord_7779152, baseEnd_7779152] using wordTrace_append hprefix tailTrace_7779152
  have hstable : (prefixWord ++ tailWord_7779152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779152).length < 2 ^ (prefixWord ++ tailWord_7779152).sum := by decide
  have hdescent : baseEnd_7779152 < baseStart_7779152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779155 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 4]
def baseStart_7779155 : Nat := 118140960795 + 7779155 * 2 ^ 59
def prefixEnd_7779155 : Nat := 4983230072969 + 3 ^ 40 * 7779155 * 2
def baseEnd_7779155 : Nat := 3994445600826616753986823

theorem tailTrace_7779155 : CollatzResearch.WordTrace tailWord_7779155 prefixEnd_7779155 3994445600826616753986823 := by
  unfold tailWord_7779155
  simp only [CollatzResearch.WordTrace]
  refine ⟨283729092132457483745938919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189152728088304989163959279 283729092132457483745938919)
  ·
    refine ⟨425593638198686225618908379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283729092132457483745938919 425593638198686225618908379)
    ·
      refine ⟨638390457298029338428362569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425593638198686225618908379 638390457298029338428362569)
      ·
        refine ⟨478792842973522003821271927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638390457298029338428362569 478792842973522003821271927)
        ·
          refine ⟨718189264460283005731907891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478792842973522003821271927 718189264460283005731907891)
          ·
            refine ⟨1077283896690424508597861837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718189264460283005731907891 1077283896690424508597861837)
            ·
              refine ⟨403981461258909190724198189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077283896690424508597861837 403981461258909190724198189)
              ·
                refine ⟨151493047972090946521574321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403981461258909190724198189 151493047972090946521574321)
                ·
                  refine ⟨113619785979068209891180741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151493047972090946521574321 113619785979068209891180741)
                  ·
                    refine ⟨21303709871075289354596389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113619785979068209891180741 21303709871075289354596389)
                    ·
                      refine ⟨3994445600826616753986823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21303709871075289354596389 3994445600826616753986823)
                      ·
                        rfl

theorem cell23_7779155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_7779155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779155 prefixEnd_7779155 := by exact prefixLift 7779155
  have htrace : WordTrace (prefixWord ++ tailWord_7779155) baseStart_7779155 baseEnd_7779155 := by
    simpa [prefixWord, tailWord_7779155, baseEnd_7779155] using wordTrace_append hprefix tailTrace_7779155
  have hstable : (prefixWord ++ tailWord_7779155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779155).length < 2 ^ (prefixWord ++ tailWord_7779155).sum := by decide
  have hdescent : baseEnd_7779155 < baseStart_7779155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779159 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_7779159 : Nat := 118140960795 + 7779159 * 2 ^ 59
def prefixEnd_7779159 : Nat := 4983230072969 + 3 ^ 40 * 7779159 * 2
def baseEnd_7779159 : Nat := 3994447654749234738336805

theorem tailTrace_7779159 : CollatzResearch.WordTrace tailWord_7779159 prefixEnd_7779159 3994447654749234738336805 := by
  unfold tailWord_7779159
  simp only [CollatzResearch.WordTrace]
  refine ⟨283729238024442992429084531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189152825349628661619389687 283729238024442992429084531)
  ·
    refine ⟨425593857036664488643626797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283729238024442992429084531 425593857036664488643626797)
    ·
      refine ⟨159597696388749183241360049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425593857036664488643626797 159597696388749183241360049)
      ·
        refine ⟨119698272291561887431020037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159597696388749183241360049 119698272291561887431020037)
        ·
          refine ⟨22443426054667853893316257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119698272291561887431020037 22443426054667853893316257)
          ·
            refine ⟨16832569541000890419987193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22443426054667853893316257 16832569541000890419987193)
            ·
              refine ⟨12624427155750667814990395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16832569541000890419987193 12624427155750667814990395)
              ·
                refine ⟨18936640733626001722485593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12624427155750667814990395 18936640733626001722485593)
                ·
                  refine ⟨14202480550219501291864195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18936640733626001722485593 14202480550219501291864195)
                  ·
                    refine ⟨21303720825329251937796293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14202480550219501291864195 21303720825329251937796293)
                    ·
                      refine ⟨3994447654749234738336805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21303720825329251937796293 3994447654749234738336805)
                      ·
                        rfl

theorem cell23_7779159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_7779159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779159 prefixEnd_7779159 := by exact prefixLift 7779159
  have htrace : WordTrace (prefixWord ++ tailWord_7779159) baseStart_7779159 baseEnd_7779159 := by
    simpa [prefixWord, tailWord_7779159, baseEnd_7779159] using wordTrace_append hprefix tailTrace_7779159
  have hstable : (prefixWord ++ tailWord_7779159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779159).length < 2 ^ (prefixWord ++ tailWord_7779159).sum := by decide
  have hdescent : baseEnd_7779159 < baseStart_7779159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779209 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 3]
def baseStart_7779209 : Nat := 118140960795 + 7779209 * 2 ^ 59
def prefixEnd_7779209 : Nat := 4983230072969 + 3 ^ 40 * 7779209 * 2
def baseEnd_7779209 : Nat := 3994473328781959542711575

theorem tailTrace_7779209 : CollatzResearch.WordTrace tailWord_7779209 prefixEnd_7779209 3994473328781959542711575 := by
  unfold tailWord_7779209
  simp only [CollatzResearch.WordTrace]
  refine ⟨283731061674261850968404681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189154041116174567312269787 283731061674261850968404681)
  ·
    refine ⟨212798296255696388226303511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283731061674261850968404681 212798296255696388226303511)
    ·
      refine ⟨319197444383544582339455267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212798296255696388226303511 319197444383544582339455267)
      ·
        refine ⟨478796166575316873509182901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319197444383544582339455267 478796166575316873509182901)
        ·
          refine ⟨44887140616435956891485897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 478796166575316873509182901 44887140616435956891485897)
          ·
            refine ⟨33665355462326967668614423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44887140616435956891485897 33665355462326967668614423)
            ·
              refine ⟨50498033193490451502921635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33665355462326967668614423 50498033193490451502921635)
              ·
                refine ⟨75747049790235677254382453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50498033193490451502921635 75747049790235677254382453)
                ·
                  refine ⟨7101285917834594742598355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75747049790235677254382453 7101285917834594742598355)
                  ·
                    refine ⟨10651928876751892113897533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7101285917834594742598355 10651928876751892113897533)
                    ·
                      refine ⟨3994473328781959542711575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10651928876751892113897533 3994473328781959542711575)
                      ·
                        rfl

theorem cell23_7779209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 1, 3].length) (baseStart_7779209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779209 prefixEnd_7779209 := by exact prefixLift 7779209
  have htrace : WordTrace (prefixWord ++ tailWord_7779209) baseStart_7779209 baseEnd_7779209 := by
    simpa [prefixWord, tailWord_7779209, baseEnd_7779209] using wordTrace_append hprefix tailTrace_7779209
  have hstable : (prefixWord ++ tailWord_7779209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779209).length < 2 ^ (prefixWord ++ tailWord_7779209).sum := by decide
  have hdescent : baseEnd_7779209 < baseStart_7779209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779212 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_7779212 : Nat := 118140960795 + 7779212 * 2 ^ 59
def prefixEnd_7779212 : Nat := 4983230072969 + 3 ^ 40 * 7779212 * 2
def baseEnd_7779212 : Nat := 1331491623074641010324687

theorem tailTrace_7779212 : CollatzResearch.WordTrace tailWord_7779212 prefixEnd_7779212 1331491623074641010324687 := by
  unfold tailWord_7779212
  simp only [CollatzResearch.WordTrace]
  refine ⟨141865585546625491240381945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189154114062167321653842593 141865585546625491240381945)
  ·
    refine ⟨106399189159969118430286459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141865585546625491240381945 106399189159969118430286459)
    ·
      refine ⟨159598783739953677645429689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106399189159969118430286459 159598783739953677645429689)
      ·
        refine ⟨119699087804965258234072267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159598783739953677645429689 119699087804965258234072267)
        ·
          refine ⟨179548631707447887351108401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119699087804965258234072267 179548631707447887351108401)
          ·
            refine ⟨134661473780585915513331301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179548631707447887351108401 134661473780585915513331301)
            ·
              refine ⟨25249026333859859158749619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134661473780585915513331301 25249026333859859158749619)
              ·
                refine ⟨37873539500789788738124429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25249026333859859158749619 37873539500789788738124429)
                ·
                  refine ⟨14202577312796170776796661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37873539500789788738124429 14202577312796170776796661)
                  ·
                    refine ⟨1331491623074641010324687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14202577312796170776796661 1331491623074641010324687)
                    ·
                      rfl

theorem cell23_7779212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_7779212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779212 prefixEnd_7779212 := by exact prefixLift 7779212
  have htrace : WordTrace (prefixWord ++ tailWord_7779212) baseStart_7779212 baseEnd_7779212 := by
    simpa [prefixWord, tailWord_7779212, baseEnd_7779212] using wordTrace_append hprefix tailTrace_7779212
  have hstable : (prefixWord ++ tailWord_7779212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779212).length < 2 ^ (prefixWord ++ tailWord_7779212).sum := by decide
  have hdescent : baseEnd_7779212 < baseStart_7779212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779219 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 2, 3, 2]
def baseStart_7779219 : Nat := 118140960795 + 7779219 * 2 ^ 59
def prefixEnd_7779219 : Nat := 4983230072969 + 3 ^ 40 * 7779219 * 2
def baseEnd_7779219 : Nat := 3994478463588504503586529

theorem tailTrace_7779219 : CollatzResearch.WordTrace tailWord_7779219 prefixEnd_7779219 3994478463588504503586529 := by
  unfold tailWord_7779219
  simp only [CollatzResearch.WordTrace]
  refine ⟨283731426404225622676268711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189154284269483748450845807 283731426404225622676268711)
  ·
    refine ⟨425597139606338434014403067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283731426404225622676268711 425597139606338434014403067)
    ·
      refine ⟨638395709409507651021604601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425597139606338434014403067 638395709409507651021604601)
      ·
        refine ⟨478796782057130738266203451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638395709409507651021604601 478796782057130738266203451)
        ·
          refine ⟨718195173085696107399305177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478796782057130738266203451 718195173085696107399305177)
          ·
            refine ⟨538646379814272080549478883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718195173085696107399305177 538646379814272080549478883)
            ·
              refine ⟨807969569721408120824218325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538646379814272080549478883 807969569721408120824218325)
              ·
                refine ⟨18936786790345502831817617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 807969569721408120824218325 18936786790345502831817617)
                ·
                  refine ⟨14202590092759127123863213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18936786790345502831817617 14202590092759127123863213)
                  ·
                    refine ⟨5325971284784672671448705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14202590092759127123863213 5325971284784672671448705)
                    ·
                      refine ⟨3994478463588504503586529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5325971284784672671448705 3994478463588504503586529)
                      ·
                        rfl

theorem cell23_7779219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 3, 2].length) (baseStart_7779219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779219 prefixEnd_7779219 := by exact prefixLift 7779219
  have htrace : WordTrace (prefixWord ++ tailWord_7779219) baseStart_7779219 baseEnd_7779219 := by
    simpa [prefixWord, tailWord_7779219, baseEnd_7779219] using wordTrace_append hprefix tailTrace_7779219
  have hstable : (prefixWord ++ tailWord_7779219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779219).length < 2 ^ (prefixWord ++ tailWord_7779219).sum := by decide
  have hdescent : baseEnd_7779219 < baseStart_7779219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779229 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_7779229 : Nat := 118140960795 + 7779229 * 2 ^ 59
def prefixEnd_7779229 : Nat := 4983230072969 + 3 ^ 40 * 7779229 * 2
def baseEnd_7779229 : Nat := 1331494532798349821487161

theorem tailTrace_7779229 : CollatzResearch.WordTrace tailWord_7779229 prefixEnd_7779229 1331494532798349821487161 := by
  unfold tailWord_7779229
  simp only [CollatzResearch.WordTrace]
  refine ⟨283731791134189394384132741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189154527422792929589421827 283731791134189394384132741)
  ·
    refine ⟨53199710837660511447024889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283731791134189394384132741 53199710837660511447024889)
    ·
      refine ⟨39899783128245383585268667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53199710837660511447024889 39899783128245383585268667)
      ·
        refine ⟨59849674692368075377903001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39899783128245383585268667 59849674692368075377903001)
        ·
          refine ⟨44887256019276056533427251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59849674692368075377903001 44887256019276056533427251)
          ·
            refine ⟨67330884028914084800140877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44887256019276056533427251 67330884028914084800140877)
            ·
              refine ⟨25249081510842781800052829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67330884028914084800140877 25249081510842781800052829)
              ·
                refine ⟨9468405566566043175019811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25249081510842781800052829 9468405566566043175019811)
                ·
                  refine ⟨14202608349849064762529717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9468405566566043175019811 14202608349849064762529717)
                  ·
                    refine ⟨1331494532798349821487161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14202608349849064762529717 1331494532798349821487161)
                    ·
                      rfl

theorem cell23_7779229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_7779229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779229 prefixEnd_7779229 := by exact prefixLift 7779229
  have htrace : WordTrace (prefixWord ++ tailWord_7779229) baseStart_7779229 baseEnd_7779229 := by
    simpa [prefixWord, tailWord_7779229, baseEnd_7779229] using wordTrace_append hprefix tailTrace_7779229
  have hstable : (prefixWord ++ tailWord_7779229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779229).length < 2 ^ (prefixWord ++ tailWord_7779229).sum := by decide
  have hdescent : baseEnd_7779229 < baseStart_7779229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779286 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7779286 : Nat := 118140960795 + 7779286 * 2 ^ 59
def prefixEnd_7779286 : Nat := 4983230072969 + 3 ^ 40 * 7779286 * 2
def baseEnd_7779286 : Nat := 3994512866792355741448721

theorem tailTrace_7779286 : CollatzResearch.WordTrace tailWord_7779286 prefixEnd_7779286 3994512866792355741448721 := by
  unfold tailWord_7779286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733366880936430819934857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189155913396655262079305141 17733366880936430819934857)
  ·
    refine ⟨13300025160702323114951143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17733366880936430819934857 13300025160702323114951143)
    ·
      refine ⟨19950037741053484672426715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13300025160702323114951143 19950037741053484672426715)
      ·
        refine ⟨29925056611580227008640073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19950037741053484672426715 29925056611580227008640073)
        ·
          refine ⟨22443792458685170256480055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29925056611580227008640073 22443792458685170256480055)
          ·
            refine ⟨33665688688027755384720083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22443792458685170256480055 33665688688027755384720083)
            ·
              refine ⟨50498533032041633077080125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33665688688027755384720083 50498533032041633077080125)
              ·
                refine ⟨18936949887015612403905047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50498533032041633077080125 18936949887015612403905047)
                ·
                  refine ⟨28405424830523418605857571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18936949887015612403905047 28405424830523418605857571)
                  ·
                    refine ⟨42608137245785127908786357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28405424830523418605857571 42608137245785127908786357)
                    ·
                      refine ⟨3994512866792355741448721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42608137245785127908786357 3994512866792355741448721)
                      ·
                        rfl

theorem cell23_7779286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7779286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779286 prefixEnd_7779286 := by exact prefixLift 7779286
  have htrace : WordTrace (prefixWord ++ tailWord_7779286) baseStart_7779286 baseEnd_7779286 := by
    simpa [prefixWord, tailWord_7779286, baseEnd_7779286] using wordTrace_append hprefix tailTrace_7779286
  have hstable : (prefixWord ++ tailWord_7779286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779286).length < 2 ^ (prefixWord ++ tailWord_7779286).sum := by decide
  have hdescent : baseEnd_7779286 < baseStart_7779286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779310 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_7779310 : Nat := 118140960795 + 7779310 * 2 ^ 59
def prefixEnd_7779310 : Nat := 4983230072969 + 3 ^ 40 * 7779310 * 2
def baseEnd_7779310 : Nat := 1331508396776021215849537

theorem tailTrace_7779310 : CollatzResearch.WordTrace tailWord_7779310 prefixEnd_7779310 1331508396776021215849537 := by
  unfold tailWord_7779310
  simp only [CollatzResearch.WordTrace]
  refine ⟨35466843180861993152228923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189156496964597296811887589 35466843180861993152228923)
  ·
    refine ⟨53200264771292989728343385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35466843180861993152228923 53200264771292989728343385)
    ·
      refine ⟨39900198578469742296257539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53200264771292989728343385 39900198578469742296257539)
      ·
        refine ⟨59850297867704613444386309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39900198578469742296257539 59850297867704613444386309)
        ·
          refine ⟨11221930850194615020822433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59850297867704613444386309 11221930850194615020822433)
          ·
            refine ⟨8416448137645961265616825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11221930850194615020822433 8416448137645961265616825)
            ·
              refine ⟨6312336103234470949212619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8416448137645961265616825 6312336103234470949212619)
              ·
                refine ⟨9468504154851706423818929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312336103234470949212619 9468504154851706423818929)
                ·
                  refine ⟨7101378116138779817864197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9468504154851706423818929 7101378116138779817864197)
                  ·
                    refine ⟨1331508396776021215849537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7101378116138779817864197 1331508396776021215849537)
                    ·
                      rfl

theorem cell23_7779310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_7779310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779310 prefixEnd_7779310 := by exact prefixLift 7779310
  have htrace : WordTrace (prefixWord ++ tailWord_7779310) baseStart_7779310 baseEnd_7779310 := by
    simpa [prefixWord, tailWord_7779310, baseEnd_7779310] using wordTrace_append hprefix tailTrace_7779310
  have hstable : (prefixWord ++ tailWord_7779310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779310).length < 2 ^ (prefixWord ++ tailWord_7779310).sum := by decide
  have hdescent : baseEnd_7779310 < baseStart_7779310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779317 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7779317 : Nat := 118140960795 + 7779317 * 2 ^ 59
def prefixEnd_7779317 : Nat := 4983230072969 + 3 ^ 40 * 7779317 * 2
def baseEnd_7779317 : Nat := 3994528784692645120161079

theorem tailTrace_7779317 : CollatzResearch.WordTrace tailWord_7779317 prefixEnd_7779317 3994528784692645120161079 := by
  unfold tailWord_7779317
  simp only [CollatzResearch.WordTrace]
  refine ⟨283735000757870585413336205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189156667171913723608890803 283735000757870585413336205)
  ·
    refine ⟨106400625284201469530001077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283735000757870585413336205 106400625284201469530001077)
    ·
      refine ⟨9975058620393887768437601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106400625284201469530001077 9975058620393887768437601)
      ·
        refine ⟨7481293965295415826328201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9975058620393887768437601 7481293965295415826328201)
        ·
          refine ⟨5610970473971561869746151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7481293965295415826328201 5610970473971561869746151)
          ·
            refine ⟨8416455710957342804619227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5610970473971561869746151 8416455710957342804619227)
            ·
              refine ⟨12624683566436014206928841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416455710957342804619227 12624683566436014206928841)
              ·
                refine ⟨9468512674827010655196631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12624683566436014206928841 9468512674827010655196631)
                ·
                  refine ⟨14202769012240515982794947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9468512674827010655196631 14202769012240515982794947)
                  ·
                    refine ⟨21304153518360773974192421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14202769012240515982794947 21304153518360773974192421)
                    ·
                      refine ⟨3994528784692645120161079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21304153518360773974192421 3994528784692645120161079)
                      ·
                        rfl

theorem cell23_7779317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7779317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779317 prefixEnd_7779317 := by exact prefixLift 7779317
  have htrace : WordTrace (prefixWord ++ tailWord_7779317) baseStart_7779317 baseEnd_7779317 := by
    simpa [prefixWord, tailWord_7779317, baseEnd_7779317] using wordTrace_append hprefix tailTrace_7779317
  have hstable : (prefixWord ++ tailWord_7779317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779317).length < 2 ^ (prefixWord ++ tailWord_7779317).sum := by decide
  have hdescent : baseEnd_7779317 < baseStart_7779317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779359 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 3]
def baseStart_7779359 : Nat := 118140960795 + 7779359 * 2 ^ 59
def prefixEnd_7779359 : Nat := 4983230072969 + 3 ^ 40 * 7779359 * 2
def baseEnd_7779359 : Nat := 3994550350880133955835885

theorem tailTrace_7779359 : CollatzResearch.WordTrace tailWord_7779359 prefixEnd_7779359 3994550350880133955835885 := by
  unfold tailWord_7779359
  simp only [CollatzResearch.WordTrace]
  refine ⟨283736532623718426586365131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189157688415812284390910087 283736532623718426586365131)
  ·
    refine ⟨425604798935577639879547697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283736532623718426586365131 425604798935577639879547697)
    ·
      refine ⟨319203599201683229909660773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425604798935577639879547697 319203599201683229909660773)
      ·
        refine ⟨59850674850315605608061395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319203599201683229909660773 59850674850315605608061395)
        ·
          refine ⟨89776012275473408412092093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59850674850315605608061395 89776012275473408412092093)
          ·
            refine ⟨33666004603302528154534535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89776012275473408412092093 33666004603302528154534535)
            ·
              refine ⟨50499006904953792231801803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33666004603302528154534535 50499006904953792231801803)
              ·
                refine ⟨75748510357430688347702705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50499006904953792231801803 75748510357430688347702705)
                ·
                  refine ⟨56811382768073016260777029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75748510357430688347702705 56811382768073016260777029)
                  ·
                    refine ⟨10652134269013690548895693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56811382768073016260777029 10652134269013690548895693)
                    ·
                      refine ⟨3994550350880133955835885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10652134269013690548895693 3994550350880133955835885)
                      ·
                        rfl

theorem cell23_7779359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_7779359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779359 prefixEnd_7779359 := by exact prefixLift 7779359
  have htrace : WordTrace (prefixWord ++ tailWord_7779359) baseStart_7779359 baseEnd_7779359 := by
    simpa [prefixWord, tailWord_7779359, baseEnd_7779359] using wordTrace_append hprefix tailTrace_7779359
  have hstable : (prefixWord ++ tailWord_7779359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779359).length < 2 ^ (prefixWord ++ tailWord_7779359).sum := by decide
  have hdescent : baseEnd_7779359 < baseStart_7779359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779409 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 2, 5]
def baseStart_7779409 : Nat := 118140960795 + 7779409 * 2 ^ 59
def prefixEnd_7779409 : Nat := 4983230072969 + 3 ^ 40 * 7779409 * 2
def baseEnd_7779409 : Nat := 1331525341637619586736885

theorem tailTrace_7779409 : CollatzResearch.WordTrace tailWord_7779409 prefixEnd_7779409 1331525341637619586736885 := by
  unfold tailWord_7779409
  simp only [CollatzResearch.WordTrace]
  refine ⟨283738356273537285125685281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189158904182358190083790187 283738356273537285125685281)
  ·
    refine ⟨212803767205152963844263961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283738356273537285125685281 212803767205152963844263961)
    ·
      refine ⟨159602825403864722883197971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212803767205152963844263961 159602825403864722883197971)
      ·
        refine ⟨239404238105797084324796957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159602825403864722883197971 239404238105797084324796957)
        ·
          refine ⟨89776589289673906621798859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239404238105797084324796957 89776589289673906621798859)
          ·
            refine ⟨134664883934510859932698289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89776589289673906621798859 134664883934510859932698289)
            ·
              refine ⟨100998662950883144949523717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134664883934510859932698289 100998662950883144949523717)
              ·
                refine ⟨18937249303290589678035697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100998662950883144949523717 18937249303290589678035697)
                ·
                  refine ⟨14202936977467942258526773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18937249303290589678035697 14202936977467942258526773)
                  ·
                    refine ⟨1331525341637619586736885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14202936977467942258526773 1331525341637619586736885)
                    ·
                      rfl

theorem cell23_7779409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_7779409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779409 prefixEnd_7779409 := by exact prefixLift 7779409
  have htrace : WordTrace (prefixWord ++ tailWord_7779409) baseStart_7779409 baseEnd_7779409 := by
    simpa [prefixWord, tailWord_7779409, baseEnd_7779409] using wordTrace_append hprefix tailTrace_7779409
  have hstable : (prefixWord ++ tailWord_7779409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779409).length < 2 ^ (prefixWord ++ tailWord_7779409).sum := by decide
  have hdescent : baseEnd_7779409 < baseStart_7779409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779426 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_7779426 : Nat := 118140960795 + 7779426 * 2 ^ 59
def prefixEnd_7779426 : Nat := 4983230072969 + 3 ^ 40 * 7779426 * 2
def baseEnd_7779426 : Nat := 1331528251361328397899359

theorem tailTrace_7779426 : CollatzResearch.WordTrace tailWord_7779426 prefixEnd_7779426 1331528251361328397899359 := by
  unfold tailWord_7779426
  simp only [CollatzResearch.WordTrace]
  refine ⟨70934744078618924257263533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189159317542983798019369421 70934744078618924257263533)
  ·
    refine ⟨26600529029482096596473825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70934744078618924257263533 26600529029482096596473825)
    ·
      refine ⟨19950396772111572447355369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26600529029482096596473825 19950396772111572447355369)
      ·
        refine ⟨14962797579083679335516527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19950396772111572447355369 14962797579083679335516527)
        ·
          refine ⟨22444196368625519003274791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14962797579083679335516527 22444196368625519003274791)
          ·
            refine ⟨33666294552938278504912187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22444196368625519003274791 33666294552938278504912187)
            ·
              refine ⟨50499441829407417757368281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33666294552938278504912187 50499441829407417757368281)
              ·
                refine ⟨37874581372055563318026211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50499441829407417757368281 37874581372055563318026211)
                ·
                  refine ⟨56811872058083344977039317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37874581372055563318026211 56811872058083344977039317)
                  ·
                    refine ⟨1331528251361328397899359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56811872058083344977039317 1331528251361328397899359)
                    ·
                      rfl

theorem cell23_7779426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_7779426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779426 prefixEnd_7779426 := by exact prefixLift 7779426
  have htrace : WordTrace (prefixWord ++ tailWord_7779426) baseStart_7779426 baseEnd_7779426 := by
    simpa [prefixWord, tailWord_7779426, baseEnd_7779426] using wordTrace_append hprefix tailTrace_7779426
  have hstable : (prefixWord ++ tailWord_7779426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779426).length < 2 ^ (prefixWord ++ tailWord_7779426).sum := by decide
  have hdescent : baseEnd_7779426 < baseStart_7779426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779429 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_7779429 : Nat := 118140960795 + 7779429 * 2 ^ 59
def prefixEnd_7779429 : Nat := 4983230072969 + 3 ^ 40 * 7779429 * 2
def baseEnd_7779429 : Nat := 3994586294525948681960563

theorem tailTrace_7779429 : CollatzResearch.WordTrace tailWord_7779429 prefixEnd_7779429 3994586294525948681960563 := by
  unfold tailWord_7779429
  simp only [CollatzResearch.WordTrace]
  refine ⟨283739085733464828541413341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189159390488976552360942227 283739085733464828541413341)
  ·
    refine ⟨106402157150049310703030003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283739085733464828541413341 106402157150049310703030003)
    ·
      refine ⟨159603235725073966054545005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106402157150049310703030003 159603235725073966054545005)
      ·
        refine ⟨59851213396902737270454377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159603235725073966054545005 59851213396902737270454377)
        ·
          refine ⟨44888410047677052952840783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59851213396902737270454377 44888410047677052952840783)
          ·
            refine ⟨67332615071515579429261175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44888410047677052952840783 67332615071515579429261175)
            ·
              refine ⟨100998922607273369143891763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67332615071515579429261175 100998922607273369143891763)
              ·
                refine ⟨151498383910910053715837645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100998922607273369143891763 151498383910910053715837645)
                ·
                  refine ⟨56811893966591270143439117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151498383910910053715837645 56811893966591270143439117)
                  ·
                    refine ⟨21304460237471726303789669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56811893966591270143439117 21304460237471726303789669)
                    ·
                      refine ⟨3994586294525948681960563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21304460237471726303789669 3994586294525948681960563)
                      ·
                        rfl

theorem cell23_7779429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_7779429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779429 prefixEnd_7779429 := by exact prefixLift 7779429
  have htrace : WordTrace (prefixWord ++ tailWord_7779429) baseStart_7779429 baseEnd_7779429 := by
    simpa [prefixWord, tailWord_7779429, baseEnd_7779429] using wordTrace_append hprefix tailTrace_7779429
  have hstable : (prefixWord ++ tailWord_7779429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779429).length < 2 ^ (prefixWord ++ tailWord_7779429).sum := by decide
  have hdescent : baseEnd_7779429 < baseStart_7779429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779446 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7779446 : Nat := 118140960795 + 7779446 * 2 ^ 59
def prefixEnd_7779446 : Nat := 4983230072969 + 3 ^ 40 * 7779446 * 2
def baseEnd_7779446 : Nat := 3994595023697075115447985

theorem tailTrace_7779446 : CollatzResearch.WordTrace tailWord_7779446 prefixEnd_7779446 3994595023697075115447985 := by
  unfold tailWord_7779446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733731610900202527798887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189159803849602160296521461 17733731610900202527798887)
  ·
    refine ⟨26600597416350303791698331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17733731610900202527798887 26600597416350303791698331)
    ·
      refine ⟨39900896124525455687547497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26600597416350303791698331 39900896124525455687547497)
      ·
        refine ⟨29925672093394091765660623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39900896124525455687547497 29925672093394091765660623)
        ·
          refine ⟨44888508140091137648490935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29925672093394091765660623 44888508140091137648490935)
          ·
            refine ⟨67332762210136706472736403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44888508140091137648490935 67332762210136706472736403)
            ·
              refine ⟨100999143315205059709104605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67332762210136706472736403 100999143315205059709104605)
              ·
                refine ⟨37874678743201897390914227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100999143315205059709104605 37874678743201897390914227)
                ·
                  refine ⟨56812018114802846086371341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37874678743201897390914227 56812018114802846086371341)
                  ·
                    refine ⟨21304506793051067282389253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56812018114802846086371341 21304506793051067282389253)
                    ·
                      refine ⟨3994595023697075115447985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21304506793051067282389253 3994595023697075115447985)
                      ·
                        rfl

theorem cell23_7779446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7779446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779446 prefixEnd_7779446 := by exact prefixLift 7779446
  have htrace : WordTrace (prefixWord ++ tailWord_7779446) baseStart_7779446 baseEnd_7779446 := by
    simpa [prefixWord, tailWord_7779446, baseEnd_7779446] using wordTrace_append hprefix tailTrace_7779446
  have hstable : (prefixWord ++ tailWord_7779446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779446).length < 2 ^ (prefixWord ++ tailWord_7779446).sum := by decide
  have hdescent : baseEnd_7779446 < baseStart_7779446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779524 : List Nat := [2, 3, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7779524 : Nat := 118140960795 + 7779524 * 2 ^ 59
def prefixEnd_7779524 : Nat := 4983230072969 + 3 ^ 40 * 7779524 * 2
def baseEnd_7779524 : Nat := 1331545025062708603424209

theorem tailTrace_7779524 : CollatzResearch.WordTrace tailWord_7779524 prefixEnd_7779524 1331545025062708603424209 := by
  unfold tailWord_7779524
  simp only [CollatzResearch.WordTrace]
  refine ⟨141871275334060329883060813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189161700445413773177414417 141871275334060329883060813)
  ·
    refine ⟨53201728250272623706147805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141871275334060329883060813 53201728250272623706147805)
    ·
      refine ⟨19950648093852233889805427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53201728250272623706147805 19950648093852233889805427)
      ·
        refine ⟨29925972140778350834708141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19950648093852233889805427 29925972140778350834708141)
        ·
          refine ⟨11222239552791881563015553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29925972140778350834708141 11222239552791881563015553)
          ·
            refine ⟨8416679664593911172261665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11222239552791881563015553 8416679664593911172261665)
            ·
              refine ⟨6312509748445433379196249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8416679664593911172261665 6312509748445433379196249)
              ·
                refine ⟨4734382311334075034397187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6312509748445433379196249 4734382311334075034397187)
                ·
                  refine ⟨7101573467001112551595781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4734382311334075034397187 7101573467001112551595781)
                  ·
                    refine ⟨1331545025062708603424209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7101573467001112551595781 1331545025062708603424209)
                    ·
                      rfl

theorem cell23_7779524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7779524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779524 prefixEnd_7779524 := by exact prefixLift 7779524
  have htrace : WordTrace (prefixWord ++ tailWord_7779524) baseStart_7779524 baseEnd_7779524 := by
    simpa [prefixWord, tailWord_7779524, baseEnd_7779524] using wordTrace_append hprefix tailTrace_7779524
  have hstable : (prefixWord ++ tailWord_7779524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779524).length < 2 ^ (prefixWord ++ tailWord_7779524).sum := by decide
  have hdescent : baseEnd_7779524 < baseStart_7779524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779546 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_7779546 : Nat := 118140960795 + 7779546 * 2 ^ 59
def prefixEnd_7779546 : Nat := 4983230072969 + 3 ^ 40 * 7779546 * 2
def baseEnd_7779546 : Nat := 1331548790587508241399175

theorem tailTrace_7779546 : CollatzResearch.WordTrace tailWord_7779546 prefixEnd_7779546 1331548790587508241399175 := by
  unfold tailWord_7779546
  simp only [CollatzResearch.WordTrace]
  refine ⟨70935838268510239380855623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189162235382693971682281661 70935838268510239380855623)
  ·
    refine ⟨106403757402765359071283435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70935838268510239380855623 106403757402765359071283435)
    ·
      refine ⟨159605636104148038606925153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106403757402765359071283435 159605636104148038606925153)
      ·
        refine ⟨119704227078111028955193865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159605636104148038606925153 119704227078111028955193865)
        ·
          refine ⟨89778170308583271716395399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119704227078111028955193865 89778170308583271716395399)
          ·
            refine ⟨134667255462874907574593099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89778170308583271716395399 134667255462874907574593099)
            ·
              refine ⟨202000883194312361361889649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134667255462874907574593099 202000883194312361361889649)
              ·
                refine ⟨151500662395734271021417237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202000883194312361361889649 151500662395734271021417237)
                ·
                  refine ⟨7101593549800043954128933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151500662395734271021417237 7101593549800043954128933)
                  ·
                    refine ⟨1331548790587508241399175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7101593549800043954128933 1331548790587508241399175)
                    ·
                      rfl

theorem cell23_7779546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_7779546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779546 prefixEnd_7779546 := by exact prefixLift 7779546
  have htrace : WordTrace (prefixWord ++ tailWord_7779546) baseStart_7779546 baseEnd_7779546 := by
    simpa [prefixWord, tailWord_7779546, baseEnd_7779546] using wordTrace_append hprefix tailTrace_7779546
  have hstable : (prefixWord ++ tailWord_7779546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779546).length < 2 ^ (prefixWord ++ tailWord_7779546).sum := by decide
  have hdescent : baseEnd_7779546 < baseStart_7779546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779557 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 2, 3, 2]
def baseStart_7779557 : Nat := 118140960795 + 7779557 * 2 ^ 59
def prefixEnd_7779557 : Nat := 4983230072969 + 3 ^ 40 * 7779557 * 2
def baseEnd_7779557 : Nat := 3994652020049724181159975

theorem tailTrace_7779557 : CollatzResearch.WordTrace tailWord_7779557 prefixEnd_7779557 3994652020049724181159975 := by
  unfold tailWord_7779557
  simp only [CollatzResearch.WordTrace]
  refine ⟨283743754277001106402072925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189162502851334070934715283 283743754277001106402072925)
  ·
    refine ⟨106403907853875414900777347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283743754277001106402072925 106403907853875414900777347)
    ·
      refine ⟨159605861780813122351166021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106403907853875414900777347 159605861780813122351166021)
      ·
        refine ⟨29926099083902460440843629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159605861780813122351166021 29926099083902460440843629)
        ·
          refine ⟨11222287156463422665316361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29926099083902460440843629 11222287156463422665316361)
          ·
            refine ⟨8416715367347566998987271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11222287156463422665316361 8416715367347566998987271)
            ·
              refine ⟨12625073051021350498480907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416715367347566998987271 12625073051021350498480907)
              ·
                refine ⟨18937609576532025747721361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625073051021350498480907 18937609576532025747721361)
                ·
                  refine ⟨14203207182399019310791021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18937609576532025747721361 14203207182399019310791021)
                  ·
                    refine ⟨5326202693399632241546633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14203207182399019310791021 5326202693399632241546633)
                    ·
                      refine ⟨3994652020049724181159975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5326202693399632241546633 3994652020049724181159975)
                      ·
                        rfl

theorem cell23_7779557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_7779557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779557 prefixEnd_7779557 := by exact prefixLift 7779557
  have htrace : WordTrace (prefixWord ++ tailWord_7779557) baseStart_7779557 baseEnd_7779557 := by
    simpa [prefixWord, tailWord_7779557, baseEnd_7779557] using wordTrace_append hprefix tailTrace_7779557
  have hstable : (prefixWord ++ tailWord_7779557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779557).length < 2 ^ (prefixWord ++ tailWord_7779557).sum := by decide
  have hdescent : baseEnd_7779557 < baseStart_7779557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779567 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 1, 5]
def baseStart_7779567 : Nat := 118140960795 + 7779567 * 2 ^ 59
def prefixEnd_7779567 : Nat := 4983230072969 + 3 ^ 40 * 7779567 * 2
def baseEnd_7779567 : Nat := 1331552384952089714011643

theorem tailTrace_7779567 : CollatzResearch.WordTrace tailWord_7779567 prefixEnd_7779567 1331552384952089714011643 := by
  unfold tailWord_7779567
  simp only [CollatzResearch.WordTrace]
  refine ⟨283744119006964878109936955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189162746004643252073291303 283744119006964878109936955)
  ·
    refine ⟨425616178510447317164905433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283744119006964878109936955 425616178510447317164905433)
    ·
      refine ⟨319212133882835487873679075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425616178510447317164905433 319212133882835487873679075)
      ·
        refine ⟨478818200824253231810518613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319212133882835487873679075 478818200824253231810518613)
        ·
          refine ⟨5611150790909217560279515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 478818200824253231810518613 5611150790909217560279515)
          ·
            refine ⟨8416726186363826340419273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611150790909217560279515 8416726186363826340419273)
            ·
              refine ⟨6312544639772869755314455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8416726186363826340419273 6312544639772869755314455)
              ·
                refine ⟨9468816959659304632971683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312544639772869755314455 9468816959659304632971683)
                ·
                  refine ⟨14203225439488956949457525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9468816959659304632971683 14203225439488956949457525)
                  ·
                    refine ⟨1331552384952089714011643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14203225439488956949457525 1331552384952089714011643)
                    ·
                      rfl

theorem cell23_7779567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 5].length) (baseStart_7779567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779567 prefixEnd_7779567 := by exact prefixLift 7779567
  have htrace : WordTrace (prefixWord ++ tailWord_7779567) baseStart_7779567 baseEnd_7779567 := by
    simpa [prefixWord, tailWord_7779567, baseEnd_7779567] using wordTrace_append hprefix tailTrace_7779567
  have hstable : (prefixWord ++ tailWord_7779567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779567).length < 2 ^ (prefixWord ++ tailWord_7779567).sum := by decide
  have hdescent : baseEnd_7779567 < baseStart_7779567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779570 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_7779570 : Nat := 118140960795 + 7779570 * 2 ^ 59
def prefixEnd_7779570 : Nat := 4983230072969 + 3 ^ 40 * 7779570 * 2
def baseEnd_7779570 : Nat := 3994658695298232630297415

theorem tailTrace_7779570 : CollatzResearch.WordTrace tailWord_7779570 prefixEnd_7779570 3994658695298232630297415 := by
  unfold tailWord_7779570
  simp only [CollatzResearch.WordTrace]
  refine ⟨70936057106488502405574041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189162818950636006414864109 70936057106488502405574041)
  ·
    refine ⟨53202042829866376804180531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70936057106488502405574041 53202042829866376804180531)
    ·
      refine ⟨79803064244799565206270797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53202042829866376804180531 79803064244799565206270797)
      ·
        refine ⟨29926149091799836952351549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79803064244799565206270797 29926149091799836952351549)
        ·
          refine ⟨11222305909424938857131831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29926149091799836952351549 11222305909424938857131831)
          ·
            refine ⟨16833458864137408285697747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11222305909424938857131831 16833458864137408285697747)
            ·
              refine ⟨25250188296206112428546621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16833458864137408285697747 25250188296206112428546621)
              ·
                refine ⟨9468820611077292160704983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25250188296206112428546621 9468820611077292160704983)
                ·
                  refine ⟨14203230916615938241057475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9468820611077292160704983 14203230916615938241057475)
                  ·
                    refine ⟨21304846374923907361586213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14203230916615938241057475 21304846374923907361586213)
                    ·
                      refine ⟨3994658695298232630297415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21304846374923907361586213 3994658695298232630297415)
                      ·
                        rfl

theorem cell23_7779570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_7779570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779570 prefixEnd_7779570 := by exact prefixLift 7779570
  have htrace : WordTrace (prefixWord ++ tailWord_7779570) baseStart_7779570 baseEnd_7779570 := by
    simpa [prefixWord, tailWord_7779570, baseEnd_7779570] using wordTrace_append hprefix tailTrace_7779570
  have hstable : (prefixWord ++ tailWord_7779570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779570).length < 2 ^ (prefixWord ++ tailWord_7779570).sum := by decide
  have hdescent : baseEnd_7779570 < baseStart_7779570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779587 : List Nat := [1, 1, 1, 3, 2, 4, 2, 4, 1, 2, 2]
def baseStart_7779587 : Nat := 118140960795 + 7779587 * 2 ^ 59
def prefixEnd_7779587 : Nat := 4983230072969 + 3 ^ 40 * 7779587 * 2
def baseEnd_7779587 : Nat := 3994667424469359063784837

theorem tailTrace_7779587 : CollatzResearch.WordTrace tailWord_7779587 prefixEnd_7779587 3994667424469359063784837 := by
  unfold tailWord_7779587
  simp only [CollatzResearch.WordTrace]
  refine ⟨283744848466892421525665015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189163232311261614350443343 283744848466892421525665015)
  ·
    refine ⟨425617272700338632288497523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283744848466892421525665015 425617272700338632288497523)
    ·
      refine ⟨638425909050507948432746285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425617272700338632288497523 638425909050507948432746285)
      ·
        refine ⟨239409715893940480662279857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638425909050507948432746285 239409715893940480662279857)
        ·
          refine ⟨179557286920455360496709893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239409715893940480662279857 179557286920455360496709893)
          ·
            refine ⟨33666991297585380093133105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179557286920455360496709893 33666991297585380093133105)
            ·
              refine ⟨25250243473189035069849829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33666991297585380093133105 25250243473189035069849829)
              ·
                refine ⟨4734420651222944075596843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25250243473189035069849829 4734420651222944075596843)
                ·
                  refine ⟨7101630976834416113395265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4734420651222944075596843 7101630976834416113395265)
                  ·
                    refine ⟨5326223232625812085046449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7101630976834416113395265 5326223232625812085046449)
                    ·
                      refine ⟨3994667424469359063784837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5326223232625812085046449 3994667424469359063784837)
                      ·
                        rfl

theorem cell23_7779587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_7779587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779587 prefixEnd_7779587 := by exact prefixLift 7779587
  have htrace : WordTrace (prefixWord ++ tailWord_7779587) baseStart_7779587 baseEnd_7779587 := by
    simpa [prefixWord, tailWord_7779587, baseEnd_7779587] using wordTrace_append hprefix tailTrace_7779587
  have hstable : (prefixWord ++ tailWord_7779587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779587).length < 2 ^ (prefixWord ++ tailWord_7779587).sum := by decide
  have hdescent : baseEnd_7779587 < baseStart_7779587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779638 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7779638 : Nat := 118140960795 + 7779638 * 2 ^ 59
def prefixEnd_7779638 : Nat := 4983230072969 + 3 ^ 40 * 7779638 * 2
def baseEnd_7779638 : Nat := 3994693611982738364247103

theorem tailTrace_7779638 : CollatzResearch.WordTrace tailWord_7779638 prefixEnd_7779638 3994693611982738364247103 := by
  unfold tailWord_7779638
  simp only [CollatzResearch.WordTrace]
  refine ⟨17734169286856728577235723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189164472393138438157181045 17734169286856728577235723)
  ·
    refine ⟨26601253930285092865853585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17734169286856728577235723 26601253930285092865853585)
    ·
      refine ⟨19950940447713819649390189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26601253930285092865853585 19950940447713819649390189)
      ·
        refine ⟨7481602667892682368521321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19950940447713819649390189 7481602667892682368521321)
        ·
          refine ⟨5611202000919511776390991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7481602667892682368521321 5611202000919511776390991)
          ·
            refine ⟨8416803001379267664586487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611202000919511776390991 8416803001379267664586487)
            ·
              refine ⟨12625204502068901496879731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416803001379267664586487 12625204502068901496879731)
              ·
                refine ⟨18937806753103352245319597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625204502068901496879731 18937806753103352245319597)
                ·
                  refine ⟨7101677532413757091994849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18937806753103352245319597 7101677532413757091994849)
                  ·
                    refine ⟨5326258149310317818996137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7101677532413757091994849 5326258149310317818996137)
                    ·
                      refine ⟨3994693611982738364247103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5326258149310317818996137 3994693611982738364247103)
                      ·
                        rfl

theorem cell23_7779638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7779638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779638 prefixEnd_7779638 := by exact prefixLift 7779638
  have htrace : WordTrace (prefixWord ++ tailWord_7779638) baseStart_7779638 baseEnd_7779638 := by
    simpa [prefixWord, tailWord_7779638, baseEnd_7779638] using wordTrace_append hprefix tailTrace_7779638
  have hstable : (prefixWord ++ tailWord_7779638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779638).length < 2 ^ (prefixWord ++ tailWord_7779638).sum := by decide
  have hdescent : baseEnd_7779638 < baseStart_7779638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779656 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_7779656 : Nat := 118140960795 + 7779656 * 2 ^ 59
def prefixEnd_7779656 : Nat := 4983230072969 + 3 ^ 40 * 7779656 * 2
def baseEnd_7779656 : Nat := 3994702854634519293822019

theorem tailTrace_7779656 : CollatzResearch.WordTrace tailWord_7779656 prefixEnd_7779656 3994702854634519293822019 := by
  unfold tailWord_7779656
  simp only [CollatzResearch.WordTrace]
  refine ⟨141873682551821223154963411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189164910069094964206617881 141873682551821223154963411)
  ·
    refine ⟨212810523827731834732445117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141873682551821223154963411 212810523827731834732445117)
    ·
      refine ⟨79803946435399438024666919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212810523827731834732445117 79803946435399438024666919)
      ·
        refine ⟨119705919653099157037000379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79803946435399438024666919 119705919653099157037000379)
        ·
          refine ⟨179558879479648735555500569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119705919653099157037000379 179558879479648735555500569)
          ·
            refine ⟨134669159609736551666625427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179558879479648735555500569 134669159609736551666625427)
            ·
              refine ⟨202003739414604827499938141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134669159609736551666625427 202003739414604827499938141)
              ·
                refine ⟨75751402280476810312476803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202003739414604827499938141 75751402280476810312476803)
                ·
                  refine ⟨113627103420715215468715205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75751402280476810312476803 113627103420715215468715205)
                  ·
                    refine ⟨21305081891384102900384101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113627103420715215468715205 21305081891384102900384101)
                    ·
                      refine ⟨3994702854634519293822019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21305081891384102900384101 3994702854634519293822019)
                      ·
                        rfl

theorem cell23_7779656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_7779656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779656 prefixEnd_7779656 := by exact prefixLift 7779656
  have htrace : WordTrace (prefixWord ++ tailWord_7779656) baseStart_7779656 baseEnd_7779656 := by
    simpa [prefixWord, tailWord_7779656, baseEnd_7779656] using wordTrace_append hprefix tailTrace_7779656
  have hstable : (prefixWord ++ tailWord_7779656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779656).length < 2 ^ (prefixWord ++ tailWord_7779656).sum := by decide
  have hdescent : baseEnd_7779656 < baseStart_7779656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779666 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 9]
def baseStart_7779666 : Nat := 118140960795 + 7779666 * 2 ^ 59
def prefixEnd_7779666 : Nat := 4983230072969 + 3 ^ 40 * 7779666 * 2
def baseEnd_7779666 : Nat := 443856443271229361632997

theorem tailTrace_7779666 : CollatzResearch.WordTrace tailWord_7779666 prefixEnd_7779666 443856443271229361632997 := by
  unfold tailWord_7779666
  simp only [CollatzResearch.WordTrace]
  refine ⟨70936932458401554504447713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189165153222404145345193901 70936932458401554504447713)
  ·
    refine ⟨53202699343801165878335785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70936932458401554504447713 53202699343801165878335785)
    ·
      refine ⟨39902024507850874408751839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53202699343801165878335785 39902024507850874408751839)
      ·
        refine ⟨59853036761776311613127759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39902024507850874408751839 59853036761776311613127759)
        ·
          refine ⟨89779555142664467419691639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59853036761776311613127759 89779555142664467419691639)
          ·
            refine ⟨134669332713996701129537459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89779555142664467419691639 134669332713996701129537459)
            ·
              refine ⟨202003999070995051694306189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134669332713996701129537459 202003999070995051694306189)
              ·
                refine ⟨75751499651623144385364821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202003999070995051694306189 75751499651623144385364821)
                ·
                  refine ⟨443856443271229361632997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75751499651623144385364821 443856443271229361632997)
                  ·
                    rfl

theorem cell23_7779666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_7779666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779666 prefixEnd_7779666 := by exact prefixLift 7779666
  have htrace : WordTrace (prefixWord ++ tailWord_7779666) baseStart_7779666 baseEnd_7779666 := by
    simpa [prefixWord, tailWord_7779666, baseEnd_7779666] using wordTrace_append hprefix tailTrace_7779666
  have hstable : (prefixWord ++ tailWord_7779666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779666).length < 2 ^ (prefixWord ++ tailWord_7779666).sum := by decide
  have hdescent : baseEnd_7779666 < baseStart_7779666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779703 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 1, 7, 2]
def baseStart_7779703 : Nat := 118140960795 + 7779703 * 2 ^ 59
def prefixEnd_7779703 : Nat := 4983230072969 + 3 ^ 40 * 7779703 * 2
def baseEnd_7779703 : Nat := 3994726988225280609934303

theorem tailTrace_7779703 : CollatzResearch.WordTrace tailWord_7779703 prefixEnd_7779703 3994726988225280609934303 := by
  unfold tailWord_7779703
  simp only [CollatzResearch.WordTrace]
  refine ⟨283749079334472173336887763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189166052889648115557925175 283749079334472173336887763)
  ·
    refine ⟨425623619001708260005331645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283749079334472173336887763 425623619001708260005331645)
    ·
      refine ⟨159608857125640597501999367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425623619001708260005331645 159608857125640597501999367)
      ·
        refine ⟨239413285688460896252999051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159608857125640597501999367 239413285688460896252999051)
        ·
          refine ⟨359119928532691344379498577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239413285688460896252999051 359119928532691344379498577)
          ·
            refine ⟨269339946399518508284623933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359119928532691344379498577 269339946399518508284623933)
            ·
              refine ⟨101002479899819440606733975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269339946399518508284623933 101002479899819440606733975)
              ·
                refine ⟨151503719849729160910100963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101002479899819440606733975 151503719849729160910100963)
                ·
                  refine ⟨227255579774593741365151445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151503719849729160910100963 227255579774593741365151445)
                  ·
                    refine ⟨5326302650967040813245737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 227255579774593741365151445 5326302650967040813245737)
                    ·
                      refine ⟨3994726988225280609934303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5326302650967040813245737 3994726988225280609934303)
                      ·
                        rfl

theorem cell23_7779703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_7779703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779703 prefixEnd_7779703 := by exact prefixLift 7779703
  have htrace : WordTrace (prefixWord ++ tailWord_7779703) baseStart_7779703 baseEnd_7779703 := by
    simpa [prefixWord, tailWord_7779703, baseEnd_7779703] using wordTrace_append hprefix tailTrace_7779703
  have hstable : (prefixWord ++ tailWord_7779703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779703).length < 2 ^ (prefixWord ++ tailWord_7779703).sum := by decide
  have hdescent : baseEnd_7779703 < baseStart_7779703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779783 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_7779783 : Nat := 118140960795 + 7779783 * 2 ^ 59
def prefixEnd_7779783 : Nat := 4983230072969 + 3 ^ 40 * 7779783 * 2
def baseEnd_7779783 : Nat := 3994768066677640296933935

theorem tailTrace_7779783 : CollatzResearch.WordTrace tailWord_7779783 prefixEnd_7779783 3994768066677640296933935 := by
  unfold tailWord_7779783
  simp only [CollatzResearch.WordTrace]
  refine ⟨283751997174182346999800003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189167998116121564666533335 283751997174182346999800003)
  ·
    refine ⟨425627995761273520499700005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283751997174182346999800003 425627995761273520499700005)
    ·
      refine ⟨79805249205238785093693751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425627995761273520499700005 79805249205238785093693751)
      ·
        refine ⟨119707873807858177640540627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79805249205238785093693751 119707873807858177640540627)
        ·
          refine ⟨179561810711787266460810941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119707873807858177640540627 179561810711787266460810941)
          ·
            refine ⟨67335679016920224922804103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179561810711787266460810941 67335679016920224922804103)
            ·
              refine ⟨101003518525380337384206155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67335679016920224922804103 101003518525380337384206155)
              ·
                refine ⟨151505277788070506076309233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101003518525380337384206155 151505277788070506076309233)
                ·
                  refine ⟨113628958341052879557231925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151505277788070506076309233 113628958341052879557231925)
                  ·
                    refine ⟨10652714844473707458490493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113628958341052879557231925 10652714844473707458490493)
                    ·
                      refine ⟨3994768066677640296933935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10652714844473707458490493 3994768066677640296933935)
                      ·
                        rfl

theorem cell23_7779783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_7779783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779783 prefixEnd_7779783 := by exact prefixLift 7779783
  have htrace : WordTrace (prefixWord ++ tailWord_7779783) baseStart_7779783 baseEnd_7779783 := by
    simpa [prefixWord, tailWord_7779783, baseEnd_7779783] using wordTrace_append hprefix tailTrace_7779783
  have hstable : (prefixWord ++ tailWord_7779783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779783).length < 2 ^ (prefixWord ++ tailWord_7779783).sum := by decide
  have hdescent : baseEnd_7779783 < baseStart_7779783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779800 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_7779800 : Nat := 118140960795 + 7779800 * 2 ^ 59
def prefixEnd_7779800 : Nat := 4983230072969 + 3 ^ 40 * 7779800 * 2
def baseEnd_7779800 : Nat := 3994776795848766730421357

theorem tailTrace_7779800 : CollatzResearch.WordTrace tailWord_7779800 prefixEnd_7779800 3994776795848766730421357 := by
  unfold tailWord_7779800
  simp only [CollatzResearch.WordTrace]
  refine ⟨141876308607560379451584427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189168411476747172602112569 141876308607560379451584427)
  ·
    refine ⟨212814462911340569177376641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141876308607560379451584427 212814462911340569177376641)
    ·
      refine ⟨159610847183505426883032481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212814462911340569177376641 159610847183505426883032481)
      ·
        refine ⟨119708135387629070162274361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159610847183505426883032481 119708135387629070162274361)
        ·
          refine ⟨89781101540721802621705771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119708135387629070162274361 89781101540721802621705771)
          ·
            refine ⟨134671652311082703932558657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89781101540721802621705771 134671652311082703932558657)
            ·
              refine ⟨101003739233312027949418993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134671652311082703932558657 101003739233312027949418993)
              ·
                refine ⟨75752804424984020962064245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101003739233312027949418993 75752804424984020962064245)
                ·
                  refine ⟨7101825414842251965193523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75752804424984020962064245 7101825414842251965193523)
                  ·
                    refine ⟨10652738122263377947790285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7101825414842251965193523 10652738122263377947790285)
                    ·
                      refine ⟨3994776795848766730421357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10652738122263377947790285 3994776795848766730421357)
                      ·
                        rfl

theorem cell23_7779800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_7779800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779800 prefixEnd_7779800 := by exact prefixLift 7779800
  have htrace : WordTrace (prefixWord ++ tailWord_7779800) baseStart_7779800 baseEnd_7779800 := by
    simpa [prefixWord, tailWord_7779800, baseEnd_7779800] using wordTrace_append hprefix tailTrace_7779800
  have hstable : (prefixWord ++ tailWord_7779800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779800).length < 2 ^ (prefixWord ++ tailWord_7779800).sum := by decide
  have hdescent : baseEnd_7779800 < baseStart_7779800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779833 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 1, 6]
def baseStart_7779833 : Nat := 118140960795 + 7779833 * 2 ^ 59
def prefixEnd_7779833 : Nat := 4983230072969 + 3 ^ 40 * 7779833 * 2
def baseEnd_7779833 : Nat := 1331597913570121700436235

theorem tailTrace_7779833 : CollatzResearch.WordTrace tailWord_7779833 prefixEnd_7779833 1331597913570121700436235 := by
  unfold tailWord_7779833
  simp only [CollatzResearch.WordTrace]
  refine ⟨283753820824001205539120153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189169213882667470359413435 283753820824001205539120153)
  ·
    refine ⟨212815365618000904154340115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283753820824001205539120153 212815365618000904154340115)
    ·
      refine ⟨319223048427001356231510173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212815365618000904154340115 319223048427001356231510173)
      ·
        refine ⟨119708643160125508586816315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319223048427001356231510173 119708643160125508586816315)
        ·
          refine ⟨179562964740188262880224473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119708643160125508586816315 179562964740188262880224473)
          ·
            refine ⟨134672223555141197160168355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179562964740188262880224473 134672223555141197160168355)
            ·
              refine ⟨202008335332711795740252533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134672223555141197160168355 202008335332711795740252533)
              ·
                refine ⟨18938281437441730850648675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202008335332711795740252533 18938281437441730850648675)
                ·
                  refine ⟨28407422156162596275973013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18938281437441730850648675 28407422156162596275973013)
                  ·
                    refine ⟨1331597913570121700436235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28407422156162596275973013 1331597913570121700436235)
                    ·
                      rfl

theorem cell23_7779833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_7779833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779833 prefixEnd_7779833 := by exact prefixLift 7779833
  have htrace : WordTrace (prefixWord ++ tailWord_7779833) baseStart_7779833 baseEnd_7779833 := by
    simpa [prefixWord, tailWord_7779833, baseEnd_7779833] using wordTrace_append hprefix tailTrace_7779833
  have hstable : (prefixWord ++ tailWord_7779833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779833).length < 2 ^ (prefixWord ++ tailWord_7779833).sum := by decide
  have hdescent : baseEnd_7779833 < baseStart_7779833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779837 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_7779837 : Nat := 118140960795 + 7779837 * 2 ^ 59
def prefixEnd_7779837 : Nat := 4983230072969 + 3 ^ 40 * 7779837 * 2
def baseEnd_7779837 : Nat := 1331598598210994361886229

theorem tailTrace_7779837 : CollatzResearch.WordTrace tailWord_7779837 prefixEnd_7779837 1331598598210994361886229 := by
  unfold tailWord_7779837
  simp only [CollatzResearch.WordTrace]
  refine ⟨283753966715986714222265765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189169311143991142814843843 283753966715986714222265765)
  ·
    refine ⟨53203868759247508916674831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283753966715986714222265765 53203868759247508916674831)
    ·
      refine ⟨79805803138871263375012247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53203868759247508916674831 79805803138871263375012247)
      ·
        refine ⟨119708704708306895062518371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79805803138871263375012247 119708704708306895062518371)
        ·
          refine ⟨179563057062460342593777557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119708704708306895062518371 179563057062460342593777557)
          ·
            refine ⟨8417018299802828559083323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179563057062460342593777557 8417018299802828559083323)
            ·
              refine ⟨12625527449704242838624985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8417018299802828559083323 12625527449704242838624985)
              ·
                refine ⟨9469145587278182128968739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12625527449704242838624985 9469145587278182128968739)
                ·
                  refine ⟨14203718380917273193453109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469145587278182128968739 14203718380917273193453109)
                  ·
                    refine ⟨1331598598210994361886229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14203718380917273193453109 1331598598210994361886229)
                    ·
                      rfl

theorem cell23_7779837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_7779837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779837 prefixEnd_7779837 := by exact prefixLift 7779837
  have htrace : WordTrace (prefixWord ++ tailWord_7779837) baseStart_7779837 baseEnd_7779837 := by
    simpa [prefixWord, tailWord_7779837, baseEnd_7779837] using wordTrace_append hprefix tailTrace_7779837
  have hstable : (prefixWord ++ tailWord_7779837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779837).length < 2 ^ (prefixWord ++ tailWord_7779837).sum := by decide
  have hdescent : baseEnd_7779837 < baseStart_7779837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779850 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_7779850 : Nat := 118140960795 + 7779850 * 2 ^ 59
def prefixEnd_7779850 : Nat := 4983230072969 + 3 ^ 40 * 7779850 * 2
def baseEnd_7779850 : Nat := 1331600823293830511598709

theorem tailTrace_7779850 : CollatzResearch.WordTrace tailWord_7779850 prefixEnd_7779850 1331600823293830511598709 := by
  unfold tailWord_7779850
  simp only [CollatzResearch.WordTrace]
  refine ⟨70938610216234904360622251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189169627243293078294992669 70938610216234904360622251)
  ·
    refine ⟨106407915324352356540933377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70938610216234904360622251 106407915324352356540933377)
    ·
      refine ⟨79805936493264267405700033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106407915324352356540933377 79805936493264267405700033)
      ·
        refine ⟨59854452369948200554275025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79805936493264267405700033 59854452369948200554275025)
        ·
          refine ⟨44890839277461150415706269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59854452369948200554275025 44890839277461150415706269)
          ·
            refine ⟨16834064729047931405889851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44890839277461150415706269 16834064729047931405889851)
            ·
              refine ⟨25251097093571897108834777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16834064729047931405889851 25251097093571897108834777)
              ·
                refine ⟨18938322820178922831626083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25251097093571897108834777 18938322820178922831626083)
                ·
                  refine ⟨28407484230268384247439125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18938322820178922831626083 28407484230268384247439125)
                  ·
                    refine ⟨1331600823293830511598709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28407484230268384247439125 1331600823293830511598709)
                    ·
                      rfl

theorem cell23_7779850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_7779850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779850 prefixEnd_7779850 := by exact prefixLift 7779850
  have htrace : WordTrace (prefixWord ++ tailWord_7779850) baseStart_7779850 baseEnd_7779850 := by
    simpa [prefixWord, tailWord_7779850, baseEnd_7779850] using wordTrace_append hprefix tailTrace_7779850
  have hstable : (prefixWord ++ tailWord_7779850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779850).length < 2 ^ (prefixWord ++ tailWord_7779850).sum := by decide
  have hdescent : baseEnd_7779850 < baseStart_7779850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779854 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_7779854 : Nat := 118140960795 + 7779854 * 2 ^ 59
def prefixEnd_7779854 : Nat := 4983230072969 + 3 ^ 40 * 7779854 * 2
def baseEnd_7779854 : Nat := 1331601507934703173048703

theorem tailTrace_7779854 : CollatzResearch.WordTrace tailWord_7779854 prefixEnd_7779854 1331601507934703173048703 := by
  unfold tailWord_7779854
  simp only [CollatzResearch.WordTrace]
  refine ⟨35469323344615640765704327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189169724504616750750423077 35469323344615640765704327)
  ·
    refine ⟨53203985016923461148556491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35469323344615640765704327 53203985016923461148556491)
    ·
      refine ⟨79805977525385191722834737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53203985016923461148556491 79805977525385191722834737)
      ·
        refine ⟨59854483144038893792126053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79805977525385191722834737 59854483144038893792126053)
        ·
          refine ⟨11222715589507292586023635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59854483144038893792126053 11222715589507292586023635)
          ·
            refine ⟨16834073384260938879035453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11222715589507292586023635 16834073384260938879035453)
            ·
              refine ⟨6312777519097852079638295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16834073384260938879035453 6312777519097852079638295)
              ·
                refine ⟨9469166278646778119457443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312777519097852079638295 9469166278646778119457443)
                ·
                  refine ⟨14203749417970167179186165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469166278646778119457443 14203749417970167179186165)
                  ·
                    refine ⟨1331601507934703173048703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14203749417970167179186165 1331601507934703173048703)
                    ·
                      rfl

theorem cell23_7779854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_7779854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779854 prefixEnd_7779854 := by exact prefixLift 7779854
  have htrace : WordTrace (prefixWord ++ tailWord_7779854) baseStart_7779854 baseEnd_7779854 := by
    simpa [prefixWord, tailWord_7779854, baseEnd_7779854] using wordTrace_append hprefix tailTrace_7779854
  have hstable : (prefixWord ++ tailWord_7779854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779854).length < 2 ^ (prefixWord ++ tailWord_7779854).sum := by decide
  have hdescent : baseEnd_7779854 < baseStart_7779854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779857 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 1, 1, 4]
def baseStart_7779857 : Nat := 118140960795 + 7779857 * 2 ^ 59
def prefixEnd_7779857 : Nat := 4983230072969 + 3 ^ 40 * 7779857 * 2
def baseEnd_7779857 : Nat := 3994806064246073007408595

theorem tailTrace_7779857 : CollatzResearch.WordTrace tailWord_7779857 prefixEnd_7779857 3994806064246073007408595 := by
  unfold tailWord_7779857
  simp only [CollatzResearch.WordTrace]
  refine ⟨283754696175914257637993825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189169797450609505091995883 283754696175914257637993825)
  ·
    refine ⟨212816022131935693228495369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283754696175914257637993825 212816022131935693228495369)
    ·
      refine ⟨159612016598951769921371527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212816022131935693228495369 159612016598951769921371527)
      ·
        refine ⟨239418024898427654882057291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159612016598951769921371527 239418024898427654882057291)
        ·
          refine ⟨359127037347641482323085937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239418024898427654882057291 359127037347641482323085937)
          ·
            refine ⟨269345278010731111742314453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359127037347641482323085937 269345278010731111742314453)
            ·
              refine ⟨6312779953376510431460495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 269345278010731111742314453 6312779953376510431460495)
              ·
                refine ⟨9469169930064765647190743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312779953376510431460495 9469169930064765647190743)
                ·
                  refine ⟨14203754895097148470786115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469169930064765647190743 14203754895097148470786115)
                  ·
                    refine ⟨21305632342645722706179173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14203754895097148470786115 21305632342645722706179173)
                    ·
                      refine ⟨3994806064246073007408595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21305632342645722706179173 3994806064246073007408595)
                      ·
                        rfl

theorem cell23_7779857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_7779857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779857 prefixEnd_7779857 := by exact prefixLift 7779857
  have htrace : WordTrace (prefixWord ++ tailWord_7779857) baseStart_7779857 baseEnd_7779857 := by
    simpa [prefixWord, tailWord_7779857, baseEnd_7779857] using wordTrace_append hprefix tailTrace_7779857
  have hstable : (prefixWord ++ tailWord_7779857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779857).length < 2 ^ (prefixWord ++ tailWord_7779857).sum := by decide
  have hdescent : baseEnd_7779857 < baseStart_7779857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779911 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_7779911 : Nat := 118140960795 + 7779911 * 2 ^ 59
def prefixEnd_7779911 : Nat := 4983230072969 + 3 ^ 40 * 7779911 * 2
def baseEnd_7779911 : Nat := 3994833792201415796133347

theorem tailTrace_7779911 : CollatzResearch.WordTrace tailWord_7779911 prefixEnd_7779911 3994833792201415796133347 := by
  unfold tailWord_7779911
  simp only [CollatzResearch.WordTrace]
  refine ⟨283756665717718624860459587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189171110478479083240306391 283756665717718624860459587)
  ·
    refine ⟨425634998576577937290689381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283756665717718624860459587 425634998576577937290689381)
    ·
      refine ⟨79806562233108363242004259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425634998576577937290689381 79806562233108363242004259)
      ·
        refine ⟨119709843349662544863006389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79806562233108363242004259 119709843349662544863006389)
        ·
          refine ⟨11222797814030863580906849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119709843349662544863006389 11222797814030863580906849)
          ·
            refine ⟨8417098360523147685680137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11222797814030863580906849 8417098360523147685680137)
            ·
              refine ⟨6312823770392360764260103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8417098360523147685680137 6312823770392360764260103)
              ·
                refine ⟨9469235655588541146390155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312823770392360764260103 9469235655588541146390155)
                ·
                  refine ⟨14203853483382811719585233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469235655588541146390155 14203853483382811719585233)
                  ·
                    refine ⟨10652890112537108789688925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14203853483382811719585233 10652890112537108789688925)
                    ·
                      refine ⟨3994833792201415796133347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10652890112537108789688925 3994833792201415796133347)
                      ·
                        rfl

theorem cell23_7779911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_7779911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779911 prefixEnd_7779911 := by exact prefixLift 7779911
  have htrace : WordTrace (prefixWord ++ tailWord_7779911) baseStart_7779911 baseEnd_7779911 := by
    simpa [prefixWord, tailWord_7779911, baseEnd_7779911] using wordTrace_append hprefix tailTrace_7779911
  have hstable : (prefixWord ++ tailWord_7779911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779911).length < 2 ^ (prefixWord ++ tailWord_7779911).sum := by decide
  have hdescent : baseEnd_7779911 < baseStart_7779911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779940 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_7779940 : Nat := 118140960795 + 7779940 * 2 ^ 59
def prefixEnd_7779940 : Nat := 4983230072969 + 3 ^ 40 * 7779940 * 2
def baseEnd_7779940 : Nat := 1331616227713465394223571

theorem tailTrace_7779940 : CollatzResearch.WordTrace tailWord_7779940 prefixEnd_7779940 1331616227713465394223571 := by
  unfold tailWord_7779940
  simp only [CollatzResearch.WordTrace]
  refine ⟨141878861717306781406632637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189171815623075708542176849 141878861717306781406632637)
  ·
    refine ⟨53204573143990043027487239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141878861717306781406632637 53204573143990043027487239)
    ·
      refine ⟨79806859715985064541230859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53204573143990043027487239 79806859715985064541230859)
      ·
        refine ⟨119710289573977596811846289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79806859715985064541230859 119710289573977596811846289)
        ·
          refine ⟨89782717180483197608884717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119710289573977596811846289 89782717180483197608884717)
          ·
            refine ⟨33668518942681199103331769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89782717180483197608884717 33668518942681199103331769)
            ·
              refine ⟨25251389207010899327498827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33668518942681199103331769 25251389207010899327498827)
              ·
                refine ⟨37877083810516348991248241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25251389207010899327498827 37877083810516348991248241)
                ·
                  refine ⟨28407812857887261743436181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37877083810516348991248241 28407812857887261743436181)
                  ·
                    refine ⟨1331616227713465394223571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28407812857887261743436181 1331616227713465394223571)
                    ·
                      rfl

theorem cell23_7779940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_7779940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779940 prefixEnd_7779940 := by exact prefixLift 7779940
  have htrace : WordTrace (prefixWord ++ tailWord_7779940) baseStart_7779940 baseEnd_7779940 := by
    simpa [prefixWord, tailWord_7779940, baseEnd_7779940] using wordTrace_append hprefix tailTrace_7779940
  have hstable : (prefixWord ++ tailWord_7779940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779940).length < 2 ^ (prefixWord ++ tailWord_7779940).sum := by decide
  have hdescent : baseEnd_7779940 < baseStart_7779940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779941 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 2, 1, 3]
def baseStart_7779941 : Nat := 118140960795 + 7779941 * 2 ^ 59
def prefixEnd_7779941 : Nat := 4983230072969 + 3 ^ 40 * 7779941 * 2
def baseEnd_7779941 : Nat := 3994849196621050678758209

theorem tailTrace_7779941 : CollatzResearch.WordTrace tailWord_7779941 prefixEnd_7779941 3994849196621050678758209 := by
  unfold tailWord_7779941
  simp only [CollatzResearch.WordTrace]
  refine ⟨283757759907609939984051677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189171839938406626656034451 283757759907609939984051677)
  ·
    refine ⟨106409159965353727494019379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283757759907609939984051677 106409159965353727494019379)
    ·
      refine ⟨159613739948030591241029069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106409159965353727494019379 159613739948030591241029069)
      ·
        refine ⟨59855152480511471715385901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159613739948030591241029069 59855152480511471715385901)
        ·
          refine ⟨22445682180191801893269713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59855152480511471715385901 22445682180191801893269713)
          ·
            refine ⟨16834261635143851419952285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22445682180191801893269713 16834261635143851419952285)
            ·
              refine ⟨6312848113178944282482107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16834261635143851419952285 6312848113178944282482107)
              ·
                refine ⟨9469272169768416423723161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312848113178944282482107 9469272169768416423723161)
                ·
                  refine ⟨7101954127326312317792371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9469272169768416423723161 7101954127326312317792371)
                  ·
                    refine ⟨10652931190989468476688557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7101954127326312317792371 10652931190989468476688557)
                    ·
                      refine ⟨3994849196621050678758209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10652931190989468476688557 3994849196621050678758209)
                      ·
                        rfl

theorem cell23_7779941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_7779941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779941 prefixEnd_7779941 := by exact prefixLift 7779941
  have htrace : WordTrace (prefixWord ++ tailWord_7779941) baseStart_7779941 baseEnd_7779941 := by
    simpa [prefixWord, tailWord_7779941, baseEnd_7779941] using wordTrace_append hprefix tailTrace_7779941
  have hstable : (prefixWord ++ tailWord_7779941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779941).length < 2 ^ (prefixWord ++ tailWord_7779941).sum := by decide
  have hdescent : baseEnd_7779941 < baseStart_7779941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7779998 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_7779998 : Nat := 118140960795 + 7779998 * 2 ^ 59
def prefixEnd_7779998 : Nat := 4983230072969 + 3 ^ 40 * 7779998 * 2
def baseEnd_7779998 : Nat := 3994878465018356955745447

theorem tailTrace_7779998 : CollatzResearch.WordTrace tailWord_7779998 prefixEnd_7779998 3994878465018356955745447 := by
  unfold tailWord_7779998
  simp only [CollatzResearch.WordTrace]
  refine ⟨35469979858550429839859581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189173225912268959145917765 35469979858550429839859581)
  ·
    refine ⟨13301242446956411189947343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35469979858550429839859581 13301242446956411189947343)
    ·
      refine ⟨19951863670434616784921015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13301242446956411189947343 19951863670434616784921015)
      ·
        refine ⟨29927795505651925177381523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19951863670434616784921015 29927795505651925177381523)
        ·
          refine ⟨44891693258477887766072285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29927795505651925177381523 44891693258477887766072285)
          ·
            refine ⟨16834384971929207912277107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44891693258477887766072285 16834384971929207912277107)
            ·
              refine ⟨25251577457893811868415661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16834384971929207912277107 25251577457893811868415661)
              ·
                refine ⟨9469341546710179450655873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25251577457893811868415661 9469341546710179450655873)
                ·
                  refine ⟨7102006160032634587991905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9469341546710179450655873 7102006160032634587991905)
                  ·
                    refine ⟨5326504620024475940993929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7102006160032634587991905 5326504620024475940993929)
                    ·
                      refine ⟨3994878465018356955745447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5326504620024475940993929 3994878465018356955745447)
                      ·
                        rfl

theorem cell23_7779998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_7779998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7779998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7779998 prefixEnd_7779998 := by exact prefixLift 7779998
  have htrace : WordTrace (prefixWord ++ tailWord_7779998) baseStart_7779998 baseEnd_7779998 := by
    simpa [prefixWord, tailWord_7779998, baseEnd_7779998] using wordTrace_append hprefix tailTrace_7779998
  have hstable : (prefixWord ++ tailWord_7779998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7779998).length < 2 ^ (prefixWord ++ tailWord_7779998).sum := by decide
  have hdescent : baseEnd_7779998 < baseStart_7779998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7779998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780037 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 4, 4, 2]
def baseStart_7780037 : Nat := 118140960795 + 7780037 * 2 ^ 59
def prefixEnd_7780037 : Nat := 4983230072969 + 3 ^ 40 * 7780037 * 2
def baseEnd_7780037 : Nat := 3994898490763882303157767

theorem tailTrace_7780037 : CollatzResearch.WordTrace tailWord_7780037 prefixEnd_7780037 3994898490763882303157767 := by
  unfold tailWord_7780037
  simp only [CollatzResearch.WordTrace]
  refine ⟨283761261315262148379546365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189174174210174765586364243 283761261315262148379546365)
  ·
    refine ⟨106410472993223305642329887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283761261315262148379546365 106410472993223305642329887)
    ·
      refine ⟨159615709489834958463494831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106410472993223305642329887 159615709489834958463494831)
      ·
        refine ⟨239423564234752437695242247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159615709489834958463494831 239423564234752437695242247)
        ·
          refine ⟨359135346352128656542863371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239423564234752437695242247 359135346352128656542863371)
          ·
            refine ⟨538703019528192984814295057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359135346352128656542863371 538703019528192984814295057)
            ·
              refine ⟨404027264646144738610721293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538703019528192984814295057 404027264646144738610721293)
              ·
                refine ⟨151510224242304276979020485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404027264646144738610721293 151510224242304276979020485)
                ·
                  refine ⟨28408167045432051933566341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151510224242304276979020485 28408167045432051933566341)
                  ·
                    refine ⟨5326531321018509737543689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28408167045432051933566341 5326531321018509737543689)
                    ·
                      refine ⟨3994898490763882303157767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5326531321018509737543689 3994898490763882303157767)
                      ·
                        rfl

theorem cell23_7780037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_7780037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780037 prefixEnd_7780037 := by exact prefixLift 7780037
  have htrace : WordTrace (prefixWord ++ tailWord_7780037) baseStart_7780037 baseEnd_7780037 := by
    simpa [prefixWord, tailWord_7780037, baseEnd_7780037] using wordTrace_append hprefix tailTrace_7780037
  have hstable : (prefixWord ++ tailWord_7780037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780037).length < 2 ^ (prefixWord ++ tailWord_7780037).sum := by decide
  have hdescent : baseEnd_7780037 < baseStart_7780037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780038 : List Nat := [6, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_7780038 : Nat := 118140960795 + 7780038 * 2 ^ 59
def prefixEnd_7780038 : Nat := 4983230072969 + 3 ^ 40 * 7780038 * 2
def baseEnd_7780038 : Nat := 443877667138281866582807

theorem tailTrace_7780038 : CollatzResearch.WordTrace tailWord_7780038 prefixEnd_7780038 443877667138281866582807 := by
  unfold tailWord_7780038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8867540555883078923447899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 189174198525505683700221845 8867540555883078923447899)
  ·
    refine ⟨13301310833824618385171849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8867540555883078923447899 13301310833824618385171849)
    ·
      refine ⟨9975983125368463788878887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13301310833824618385171849 9975983125368463788878887)
      ·
        refine ⟨14963974688052695683318331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9975983125368463788878887 14963974688052695683318331)
        ·
          refine ⟨22445962032079043524977497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14963974688052695683318331 22445962032079043524977497)
          ·
            refine ⟨16834471524059282643733123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22445962032079043524977497 16834471524059282643733123)
            ·
              refine ⟨25251707286088923965599685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16834471524059282643733123 25251707286088923965599685)
              ·
                refine ⟨4734695116141673243549941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25251707286088923965599685 4734695116141673243549941)
                ·
                  refine ⟨443877667138281866582807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4734695116141673243549941 443877667138281866582807)
                  ·
                    rfl

theorem cell23_7780038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_7780038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780038 prefixEnd_7780038 := by exact prefixLift 7780038
  have htrace : WordTrace (prefixWord ++ tailWord_7780038) baseStart_7780038 baseEnd_7780038 := by
    simpa [prefixWord, tailWord_7780038, baseEnd_7780038] using wordTrace_append hprefix tailTrace_7780038
  have hstable : (prefixWord ++ tailWord_7780038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780038).length < 2 ^ (prefixWord ++ tailWord_7780038).sum := by decide
  have hdescent : baseEnd_7780038 < baseStart_7780038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780040 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_7780040 : Nat := 118140960795 + 7780040 * 2 ^ 59
def prefixEnd_7780040 : Nat := 4983230072969 + 3 ^ 40 * 7780040 * 2
def baseEnd_7780040 : Nat := 3994900031205845791420253

theorem tailTrace_7780040 : CollatzResearch.WordTrace tailWord_7780040 prefixEnd_7780040 3994900031205845791420253 := by
  unfold tailWord_7780040
  simp only [CollatzResearch.WordTrace]
  refine ⟨141880685367125639945952787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189174247156167519927937049 141880685367125639945952787)
  ·
    refine ⟨212821028050688459918929181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141880685367125639945952787 212821028050688459918929181)
    ·
      refine ⟨79807885519008172469598443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212821028050688459918929181 79807885519008172469598443)
      ·
        refine ⟨119711828278512258704397665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79807885519008172469598443 119711828278512258704397665)
        ·
          refine ⟨89783871208884194028298249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119711828278512258704397665 89783871208884194028298249)
          ·
            refine ⟨67337903406663145521223687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89783871208884194028298249 67337903406663145521223687)
            ·
              refine ⟨101006855109994718281835531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67337903406663145521223687 101006855109994718281835531)
              ·
                refine ⟨151510282664992077422753297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101006855109994718281835531 151510282664992077422753297)
                ·
                  refine ⟨113632711998744058067064973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151510282664992077422753297 113632711998744058067064973)
                  ·
                    refine ⟨42612266999529021775149365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113632711998744058067064973 42612266999529021775149365)
                    ·
                      refine ⟨3994900031205845791420253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42612266999529021775149365 3994900031205845791420253)
                      ·
                        rfl

theorem cell23_7780040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_7780040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780040 prefixEnd_7780040 := by exact prefixLift 7780040
  have htrace : WordTrace (prefixWord ++ tailWord_7780040) baseStart_7780040 baseEnd_7780040 := by
    simpa [prefixWord, tailWord_7780040, baseEnd_7780040] using wordTrace_append hprefix tailTrace_7780040
  have hstable : (prefixWord ++ tailWord_7780040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780040).length < 2 ^ (prefixWord ++ tailWord_7780040).sum := by decide
  have hdescent : baseEnd_7780040 < baseStart_7780040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780074 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_7780074 : Nat := 118140960795 + 7780074 * 2 ^ 59
def prefixEnd_7780074 : Nat := 4983230072969 + 3 ^ 40 * 7780074 * 2
def baseEnd_7780074 : Nat := 3994917489548098658395097

theorem tailTrace_7780074 : CollatzResearch.WordTrace tailWord_7780074 prefixEnd_7780074 3994917489548098658395097 := by
  unfold tailWord_7780074
  simp only [CollatzResearch.WordTrace]
  refine ⟨70940652704032025924660819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189175073877418735799095517 70940652704032025924660819)
  ·
    refine ⟨106410979056048038886991229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70940652704032025924660819 106410979056048038886991229)
    ·
      refine ⟨39904117146018014582621711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106410979056048038886991229 39904117146018014582621711)
      ·
        refine ⟨59856175719027021873932567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39904117146018014582621711 59856175719027021873932567)
        ·
          refine ⟨89784263578540532810898851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59856175719027021873932567 89784263578540532810898851)
          ·
            refine ⟨134676395367810799216348277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89784263578540532810898851 134676395367810799216348277)
            ·
              refine ⟨12625912065732262426532651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134676395367810799216348277 12625912065732262426532651)
              ·
                refine ⟨18938868098598393639798977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625912065732262426532651 18938868098598393639798977)
                ·
                  refine ⟨14204151073948795229849233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18938868098598393639798977 14204151073948795229849233)
                  ·
                    refine ⟨10653113305461596422386925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14204151073948795229849233 10653113305461596422386925)
                    ·
                      refine ⟨3994917489548098658395097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653113305461596422386925 3994917489548098658395097)
                      ·
                        rfl

theorem cell23_7780074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_7780074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780074 prefixEnd_7780074 := by exact prefixLift 7780074
  have htrace : WordTrace (prefixWord ++ tailWord_7780074) baseStart_7780074 baseEnd_7780074 := by
    simpa [prefixWord, tailWord_7780074, baseEnd_7780074] using wordTrace_append hprefix tailTrace_7780074
  have hstable : (prefixWord ++ tailWord_7780074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780074).length < 2 ^ (prefixWord ++ tailWord_7780074).sum := by decide
  have hdescent : baseEnd_7780074 < baseStart_7780074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780081 : List Nat := [1, 2, 2, 2, 2, 4, 2, 3, 1, 4]
def baseStart_7780081 : Nat := 118140960795 + 7780081 * 2 ^ 59
def prefixEnd_7780081 : Nat := 4983230072969 + 3 ^ 40 * 7780081 * 2
def baseEnd_7780081 : Nat := 1331640361304226710335855

theorem tailTrace_7780081 : CollatzResearch.WordTrace tailWord_7780081 prefixEnd_7780081 1331640361304226710335855 := by
  unfold tailWord_7780081
  simp only [CollatzResearch.WordTrace]
  refine ⟨283762866127102743894148097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189175244084735162596098731 283762866127102743894148097)
  ·
    refine ⟨212822149595327057920611073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283762866127102743894148097 212822149595327057920611073)
    ·
      refine ⟨159616612196495293440458305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212822149595327057920611073 159616612196495293440458305)
      ·
        refine ⟨119712459147371470080343729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159616612196495293440458305 119712459147371470080343729)
        ·
          refine ⟨89784344360528602560257797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119712459147371470080343729 89784344360528602560257797)
          ·
            refine ⟨16834564567599112980048337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89784344360528602560257797 16834564567599112980048337)
            ·
              refine ⟨12625923425699334735036253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16834564567599112980048337 12625923425699334735036253)
              ·
                refine ⟨4734721284637250525638595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12625923425699334735036253 4734721284637250525638595)
                ·
                  refine ⟨7102081926955875788457893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4734721284637250525638595 7102081926955875788457893)
                  ·
                    refine ⟨1331640361304226710335855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7102081926955875788457893 1331640361304226710335855)
                    ·
                      rfl

theorem cell23_7780081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_7780081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780081 prefixEnd_7780081 := by exact prefixLift 7780081
  have htrace : WordTrace (prefixWord ++ tailWord_7780081) baseStart_7780081 baseEnd_7780081 := by
    simpa [prefixWord, tailWord_7780081, baseEnd_7780081] using wordTrace_append hprefix tailTrace_7780081
  have hstable : (prefixWord ++ tailWord_7780081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780081).length < 2 ^ (prefixWord ++ tailWord_7780081).sum := by decide
  have hdescent : baseEnd_7780081 < baseStart_7780081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780094 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_7780094 : Nat := 118140960795 + 7780094 * 2 ^ 59
def prefixEnd_7780094 : Nat := 4983230072969 + 3 ^ 40 * 7780094 * 2
def baseEnd_7780094 : Nat := 443880862129020953349445

theorem tailTrace_7780094 : CollatzResearch.WordTrace tailWord_7780094 prefixEnd_7780094 443880862129020953349445 := by
  unfold tailWord_7780094
  simp only [CollatzResearch.WordTrace]
  refine ⟨35470417534506955889296417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189175560184037098076247557 35470417534506955889296417)
  ·
    refine ⟨26602813150880216916972313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35470417534506955889296417 26602813150880216916972313)
    ·
      refine ⟨19952109863160162687729235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26602813150880216916972313 19952109863160162687729235)
      ·
        refine ⟨29928164794740244031593853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19952109863160162687729235 29928164794740244031593853)
        ·
          refine ⟨11223061798027591511847695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29928164794740244031593853 11223061798027591511847695)
          ·
            refine ⟨16834592697041387267771543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223061798027591511847695 16834592697041387267771543)
            ·
              refine ⟨25251889045562080901657315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16834592697041387267771543 25251889045562080901657315)
              ·
                refine ⟨37877833568343121352485973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25251889045562080901657315 37877833568343121352485973)
                ·
                  refine ⟨443880862129020953349445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37877833568343121352485973 443880862129020953349445)
                  ·
                    rfl

theorem cell23_7780094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_7780094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780094 prefixEnd_7780094 := by exact prefixLift 7780094
  have htrace : WordTrace (prefixWord ++ tailWord_7780094) baseStart_7780094 baseEnd_7780094 := by
    simpa [prefixWord, tailWord_7780094, baseEnd_7780094] using wordTrace_append hprefix tailTrace_7780094
  have hstable : (prefixWord ++ tailWord_7780094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780094).length < 2 ^ (prefixWord ++ tailWord_7780094).sum := by decide
  have hdescent : baseEnd_7780094 < baseStart_7780094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780124 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_7780124 : Nat := 118140960795 + 7780124 * 2 ^ 59
def prefixEnd_7780124 : Nat := 4983230072969 + 3 ^ 40 * 7780124 * 2
def baseEnd_7780124 : Nat := 1331647721193607820923289

theorem tailTrace_7780124 : CollatzResearch.WordTrace tailWord_7780124 prefixEnd_7780124 1331647721193607820923289 := by
  unfold tailWord_7780124
  simp only [CollatzResearch.WordTrace]
  refine ⟨141882217232973481118981713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189176289643964641491975617 141882217232973481118981713)
  ·
    refine ⟨106411662924730110839236285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141882217232973481118981713 106411662924730110839236285)
    ·
      refine ⟨39904373596773791564713607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106411662924730110839236285 39904373596773791564713607)
      ·
        refine ⟨59856560395160687347070411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39904373596773791564713607 59856560395160687347070411)
        ·
          refine ⟨89784840592741031020605617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59856560395160687347070411 89784840592741031020605617)
          ·
            refine ⟨67338630444555773265454213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89784840592741031020605617 67338630444555773265454213)
            ·
              refine ⟨12625993208354207487272665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67338630444555773265454213 12625993208354207487272665)
              ·
                refine ⟨9469494906265655615454499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12625993208354207487272665 9469494906265655615454499)
                ·
                  refine ⟨14204242359398483423181749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469494906265655615454499 14204242359398483423181749)
                  ·
                    refine ⟨1331647721193607820923289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14204242359398483423181749 1331647721193607820923289)
                    ·
                      rfl

theorem cell23_7780124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_7780124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780124 prefixEnd_7780124 := by exact prefixLift 7780124
  have htrace : WordTrace (prefixWord ++ tailWord_7780124) baseStart_7780124 baseEnd_7780124 := by
    simpa [prefixWord, tailWord_7780124, baseEnd_7780124] using wordTrace_append hprefix tailTrace_7780124
  have hstable : (prefixWord ++ tailWord_7780124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780124).length < 2 ^ (prefixWord ++ tailWord_7780124).sum := by decide
  have hdescent : baseEnd_7780124 < baseStart_7780124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780148 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_7780148 : Nat := 118140960795 + 7780148 * 2 ^ 59
def prefixEnd_7780148 : Nat := 4983230072969 + 3 ^ 40 * 7780148 * 2
def baseEnd_7780148 : Nat := 3994955487116531368869757

theorem tailTrace_7780148 : CollatzResearch.WordTrace tailWord_7780148 prefixEnd_7780148 3994955487116531368869757 := by
  unfold tailWord_7780148
  simp only [CollatzResearch.WordTrace]
  refine ⟨141882654908930007168418549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189176873211906676224558065 141882654908930007168418549)
  ·
    refine ⟨13301498897712188172039239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141882654908930007168418549 13301498897712188172039239)
    ·
      refine ⟨19952248346568282258058859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13301498897712188172039239 19952248346568282258058859)
      ·
        refine ⟨29928372519852423387088289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19952248346568282258058859 29928372519852423387088289)
        ·
          refine ⟨22446279389889317540316217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29928372519852423387088289 22446279389889317540316217)
          ·
            refine ⟨16834709542416988155237163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22446279389889317540316217 16834709542416988155237163)
            ·
              refine ⟨25252064313625482232855745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16834709542416988155237163 25252064313625482232855745)
              ·
                refine ⟨18939048235219111674641809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25252064313625482232855745 18939048235219111674641809)
                ·
                  refine ⟨14204286176414333755981357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18939048235219111674641809 14204286176414333755981357)
                  ·
                    refine ⟨5326607316155375158493009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14204286176414333755981357 5326607316155375158493009)
                    ·
                      refine ⟨3994955487116531368869757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5326607316155375158493009 3994955487116531368869757)
                      ·
                        rfl

theorem cell23_7780148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_7780148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780148 prefixEnd_7780148 := by exact prefixLift 7780148
  have htrace : WordTrace (prefixWord ++ tailWord_7780148) baseStart_7780148 baseEnd_7780148 := by
    simpa [prefixWord, tailWord_7780148, baseEnd_7780148] using wordTrace_append hprefix tailTrace_7780148
  have hstable : (prefixWord ++ tailWord_7780148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780148).length < 2 ^ (prefixWord ++ tailWord_7780148).sum := by decide
  have hdescent : baseEnd_7780148 < baseStart_7780148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780154 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_7780154 : Nat := 118140960795 + 7780154 * 2 ^ 59
def prefixEnd_7780154 : Nat := 4983230072969 + 3 ^ 40 * 7780154 * 2
def baseEnd_7780154 : Nat := 1331652856000152781798243

theorem tailTrace_7780154 : CollatzResearch.WordTrace tailWord_7780154 prefixEnd_7780154 1331652856000152781798243 := by
  unfold tailWord_7780154
  simp only [CollatzResearch.WordTrace]
  refine ⟨70941382163959569340388879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189177019103892184907703677 70941382163959569340388879)
  ·
    refine ⟨106412073245939354010583319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70941382163959569340388879 106412073245939354010583319)
    ·
      refine ⟨159618109868909031015874979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106412073245939354010583319 159618109868909031015874979)
      ·
        refine ⟨239427164803363546523812469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159618109868909031015874979 239427164803363546523812469)
        ·
          refine ⟨22446296700315332486607419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239427164803363546523812469 22446296700315332486607419)
          ·
            refine ⟨33669445050472998729911129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22446296700315332486607419 33669445050472998729911129)
            ·
              refine ⟨25252083787854749047433347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33669445050472998729911129 25252083787854749047433347)
              ·
                refine ⟨37878125681782123571150021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25252083787854749047433347 37878125681782123571150021)
                ·
                  refine ⟨7102148565334148169590629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37878125681782123571150021 7102148565334148169590629)
                  ·
                    refine ⟨1331652856000152781798243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7102148565334148169590629 1331652856000152781798243)
                    ·
                      rfl

theorem cell23_7780154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_7780154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780154 prefixEnd_7780154 := by exact prefixLift 7780154
  have htrace : WordTrace (prefixWord ++ tailWord_7780154) baseStart_7780154 baseEnd_7780154 := by
    simpa [prefixWord, tailWord_7780154, baseEnd_7780154] using wordTrace_append hprefix tailTrace_7780154
  have hstable : (prefixWord ++ tailWord_7780154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780154).length < 2 ^ (prefixWord ++ tailWord_7780154).sum := by decide
  have hdescent : baseEnd_7780154 < baseStart_7780154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780181 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_7780181 : Nat := 118140960795 + 7780181 * 2 ^ 59
def prefixEnd_7780181 : Nat := 4983230072969 + 3 ^ 40 * 7780181 * 2
def baseEnd_7780181 : Nat := 3994972431978129739757105

theorem tailTrace_7780181 : CollatzResearch.WordTrace tailWord_7780181 prefixEnd_7780181 3994972431978129739757105 := by
  unfold tailWord_7780181
  simp only [CollatzResearch.WordTrace]
  refine ⟨283766513426740460972788397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189177675617826973981858931 283766513426740460972788397)
  ·
    refine ⟨106412442535027672864795649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283766513426740460972788397 106412442535027672864795649)
    ·
      refine ⟨79809331901270754648596737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106412442535027672864795649 79809331901270754648596737)
      ·
        refine ⟨59856998925953065986447553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79809331901270754648596737 59856998925953065986447553)
        ·
          refine ⟨44892749194464799489835665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59856998925953065986447553 44892749194464799489835665)
          ·
            refine ⟨33669561895848599617376749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44892749194464799489835665 33669561895848599617376749)
            ·
              refine ⟨12626085710943224856516281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33669561895848599617376749 12626085710943224856516281)
              ·
                refine ⟨9469564283207418642387211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12626085710943224856516281 9469564283207418642387211)
                ·
                  refine ⟨14204346424811127963580817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469564283207418642387211 14204346424811127963580817)
                  ·
                    refine ⟨10653259818608345972685613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14204346424811127963580817 10653259818608345972685613)
                    ·
                      refine ⟨3994972431978129739757105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653259818608345972685613 3994972431978129739757105)
                      ·
                        rfl

theorem cell23_7780181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_7780181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780181 prefixEnd_7780181 := by exact prefixLift 7780181
  have htrace : WordTrace (prefixWord ++ tailWord_7780181) baseStart_7780181 baseEnd_7780181 := by
    simpa [prefixWord, tailWord_7780181, baseEnd_7780181] using wordTrace_append hprefix tailTrace_7780181
  have hstable : (prefixWord ++ tailWord_7780181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780181).length < 2 ^ (prefixWord ++ tailWord_7780181).sum := by decide
  have hdescent : baseEnd_7780181 < baseStart_7780181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780217 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_7780217 : Nat := 118140960795 + 7780217 * 2 ^ 59
def prefixEnd_7780217 : Nat := 4983230072969 + 3 ^ 40 * 7780217 * 2
def baseEnd_7780217 : Nat := 3994990917281691598906939

theorem tailTrace_7780217 : CollatzResearch.WordTrace tailWord_7780217 prefixEnd_7780217 3994990917281691598906939 := by
  unfold tailWord_7780217
  simp only [CollatzResearch.WordTrace]
  refine ⟨283767826454610039121098905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189178550969740026080732603 283767826454610039121098905)
  ·
    refine ⟨212825869840957529340824179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283767826454610039121098905 212825869840957529340824179)
    ·
      refine ⟨319238804761436294011236269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212825869840957529340824179 319238804761436294011236269)
      ·
        refine ⟨119714551785538610254213601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319238804761436294011236269 119714551785538610254213601)
        ·
          refine ⟨89785913839153957690660201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119714551785538610254213601 89785913839153957690660201)
          ·
            refine ⟨67339435379365468267995151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89785913839153957690660201 67339435379365468267995151)
            ·
              refine ⟨101009153069048202401992727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67339435379365468267995151 101009153069048202401992727)
              ·
                refine ⟨151513729603572303602989091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101009153069048202401992727 151513729603572303602989091)
                ·
                  refine ⟨227270594405358455404483637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151513729603572303602989091 227270594405358455404483637)
                  ·
                    refine ⟨21306618225502355194170341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 227270594405358455404483637 21306618225502355194170341)
                    ·
                      refine ⟨3994990917281691598906939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21306618225502355194170341 3994990917281691598906939)
                      ·
                        rfl

theorem cell23_7780217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_7780217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780217 prefixEnd_7780217 := by exact prefixLift 7780217
  have htrace : WordTrace (prefixWord ++ tailWord_7780217) baseStart_7780217 baseEnd_7780217 := by
    simpa [prefixWord, tailWord_7780217, baseEnd_7780217] using wordTrace_append hprefix tailTrace_7780217
  have hstable : (prefixWord ++ tailWord_7780217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780217).length < 2 ^ (prefixWord ++ tailWord_7780217).sum := by decide
  have hdescent : baseEnd_7780217 < baseStart_7780217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780227 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 1, 8]
def baseStart_7780227 : Nat := 118140960795 + 7780227 * 2 ^ 59
def prefixEnd_7780227 : Nat := 4983230072969 + 3 ^ 40 * 7780227 * 2
def baseEnd_7780227 : Nat := 1331665350696078853260631

theorem tailTrace_7780227 : CollatzResearch.WordTrace tailWord_7780227 prefixEnd_7780227 1331665350696078853260631 := by
  unfold tailWord_7780227
  simp only [CollatzResearch.WordTrace]
  refine ⟨283768191184573810828962935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189178794123049207219308623 283768191184573810828962935)
  ·
    refine ⟨425652286776860716243444403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283768191184573810828962935 425652286776860716243444403)
    ·
      refine ⟨638478430165291074365166605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425652286776860716243444403 638478430165291074365166605)
      ·
        refine ⟨239429411311984152886937477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638478430165291074365166605 239429411311984152886937477)
        ·
          refine ⟨44893014620997028666300777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239429411311984152886937477 44893014620997028666300777)
          ·
            refine ⟨33669760965747771499725583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44893014620997028666300777 33669760965747771499725583)
            ·
              refine ⟨50504641448621657249588375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33669760965747771499725583 50504641448621657249588375)
              ·
                refine ⟨75756962172932485874382563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50504641448621657249588375 75756962172932485874382563)
                ·
                  refine ⟨113635443259398728811573845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75756962172932485874382563 113635443259398728811573845)
                  ·
                    refine ⟨1331665350696078853260631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113635443259398728811573845 1331665350696078853260631)
                    ·
                      rfl

theorem cell23_7780227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 8].length) (baseStart_7780227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780227 prefixEnd_7780227 := by exact prefixLift 7780227
  have htrace : WordTrace (prefixWord ++ tailWord_7780227) baseStart_7780227 baseEnd_7780227 := by
    simpa [prefixWord, tailWord_7780227, baseEnd_7780227] using wordTrace_append hprefix tailTrace_7780227
  have hstable : (prefixWord ++ tailWord_7780227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780227).length < 2 ^ (prefixWord ++ tailWord_7780227).sum := by decide
  have hdescent : baseEnd_7780227 < baseStart_7780227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780246 : List Nat := [5, 3, 1, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7780246 : Nat := 118140960795 + 7780246 * 2 ^ 59
def prefixEnd_7780246 : Nat := 4983230072969 + 3 ^ 40 * 7780246 * 2
def baseEnd_7780246 : Nat := 3995005808220671985444307

theorem tailTrace_7780246 : CollatzResearch.WordTrace tailWord_7780246 prefixEnd_7780246 3995005808220671985444307 := by
  unfold tailWord_7780246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17735555260719061067119037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189179256114336651382603061 17735555260719061067119037)
  ·
    refine ⟨6650833222769647900169639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17735555260719061067119037 6650833222769647900169639)
    ·
      refine ⟨9976249834154471850254459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6650833222769647900169639 9976249834154471850254459)
      ·
        refine ⟨14964374751231707775381689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9976249834154471850254459 14964374751231707775381689)
        ·
          refine ⟨11223281063423780831536267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14964374751231707775381689 11223281063423780831536267)
          ·
            refine ⟨16834921595135671247304401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223281063423780831536267 16834921595135671247304401)
            ·
              refine ⟨12626191196351753435478301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16834921595135671247304401 12626191196351753435478301)
              ·
                refine ⟨4734821698631907538304363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12626191196351753435478301 4734821698631907538304363)
                ·
                  refine ⟨7102232547947861307456545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4734821698631907538304363 7102232547947861307456545)
                  ·
                    refine ⟨5326674410960895980592409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7102232547947861307456545 5326674410960895980592409)
                    ·
                      refine ⟨3995005808220671985444307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5326674410960895980592409 3995005808220671985444307)
                      ·
                        rfl

theorem cell23_7780246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7780246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780246 prefixEnd_7780246 := by exact prefixLift 7780246
  have htrace : WordTrace (prefixWord ++ tailWord_7780246) baseStart_7780246 baseEnd_7780246 := by
    simpa [prefixWord, tailWord_7780246, baseEnd_7780246] using wordTrace_append hprefix tailTrace_7780246
  have hstable : (prefixWord ++ tailWord_7780246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780246).length < 2 ^ (prefixWord ++ tailWord_7780246).sum := by decide
  have hdescent : baseEnd_7780246 < baseStart_7780246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780287 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 3, 7]
def baseStart_7780287 : Nat := 118140960795 + 7780287 * 2 ^ 59
def prefixEnd_7780287 : Nat := 4983230072969 + 3 ^ 40 * 7780287 * 2
def baseEnd_7780287 : Nat := 1331675620309168775010539

theorem tailTrace_7780287 : CollatzResearch.WordTrace tailWord_7780287 prefixEnd_7780287 1331675620309168775010539 := by
  unfold tailWord_7780287
  simp only [CollatzResearch.WordTrace]
  refine ⟨283770379564356441076147115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189180253042904294050764743 283770379564356441076147115)
  ·
    refine ⟨425655569346534661614220673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283770379564356441076147115 425655569346534661614220673)
    ·
      refine ⟨319241677009900996210665505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425655569346534661614220673 319241677009900996210665505)
      ·
        refine ⟨239431257757425747157999129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319241677009900996210665505 239431257757425747157999129)
        ·
          refine ⟨179573443318069310368499347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239431257757425747157999129 179573443318069310368499347)
          ·
            refine ⟨269360164977103965552749021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179573443318069310368499347 269360164977103965552749021)
            ·
              refine ⟨101010061866413987082280883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269360164977103965552749021 101010061866413987082280883)
              ·
                refine ⟨151515092799620980623421325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101010061866413987082280883 151515092799620980623421325)
                ·
                  refine ⟨56818159799857867733782997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151515092799620980623421325 56818159799857867733782997)
                  ·
                    refine ⟨1331675620309168775010539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56818159799857867733782997 1331675620309168775010539)
                    ·
                      rfl

theorem cell23_7780287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_7780287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780287 prefixEnd_7780287 := by exact prefixLift 7780287
  have htrace : WordTrace (prefixWord ++ tailWord_7780287) baseStart_7780287 baseEnd_7780287 := by
    simpa [prefixWord, tailWord_7780287, baseEnd_7780287] using wordTrace_append hprefix tailTrace_7780287
  have hstable : (prefixWord ++ tailWord_7780287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780287).length < 2 ^ (prefixWord ++ tailWord_7780287).sum := by decide
  have hdescent : baseEnd_7780287 < baseStart_7780287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780297 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_7780297 : Nat := 118140960795 + 7780297 * 2 ^ 59
def prefixEnd_7780297 : Nat := 4983230072969 + 3 ^ 40 * 7780297 * 2
def baseEnd_7780297 : Nat := 3995031995734051285906571

theorem tailTrace_7780297 : CollatzResearch.WordTrace tailWord_7780297 prefixEnd_7780297 3995031995734051285906571 := by
  unfold tailWord_7780297
  simp only [CollatzResearch.WordTrace]
  refine ⟨283770744294320212784011145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189180496196213475189340763 283770744294320212784011145)
  ·
    refine ⟨212828058220740159588008359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283770744294320212784011145 212828058220740159588008359)
    ·
      refine ⟨319242087331110239382012539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212828058220740159588008359 319242087331110239382012539)
      ·
        refine ⟨478863130996665359073018809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319242087331110239382012539 478863130996665359073018809)
        ·
          refine ⟨359147348247499019304764107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478863130996665359073018809 359147348247499019304764107)
          ·
            refine ⟨538721022371248528957146161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359147348247499019304764107 538721022371248528957146161)
            ·
              refine ⟨404040766778436396717859621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538721022371248528957146161 404040766778436396717859621)
              ·
                refine ⟨75757643770956824384598679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404040766778436396717859621 75757643770956824384598679)
                ·
                  refine ⟨113636465656435236576898019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75757643770956824384598679 113636465656435236576898019)
                  ·
                    refine ⟨170454698484652854865347029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113636465656435236576898019 170454698484652854865347029)
                    ·
                      refine ⟨3995031995734051285906571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170454698484652854865347029 3995031995734051285906571)
                      ·
                        rfl

theorem cell23_7780297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_7780297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780297 prefixEnd_7780297 := by exact prefixLift 7780297
  have htrace : WordTrace (prefixWord ++ tailWord_7780297) baseStart_7780297 baseEnd_7780297 := by
    simpa [prefixWord, tailWord_7780297, baseEnd_7780297] using wordTrace_append hprefix tailTrace_7780297
  have hstable : (prefixWord ++ tailWord_7780297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780297).length < 2 ^ (prefixWord ++ tailWord_7780297).sum := by decide
  have hdescent : baseEnd_7780297 < baseStart_7780297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780344 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_7780344 : Nat := 118140960795 + 7780344 * 2 ^ 59
def prefixEnd_7780344 : Nat := 4983230072969 + 3 ^ 40 * 7780344 * 2
def baseEnd_7780344 : Nat := 3995056129324812602018855

theorem tailTrace_7780344 : CollatzResearch.WordTrace tailWord_7780344 prefixEnd_7780344 3995056129324812602018855 := by
  unfold tailWord_7780344
  simp only [CollatzResearch.WordTrace]
  refine ⟨141886229262574969905486043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189181639016766626540648057 141886229262574969905486043)
  ·
    refine ⟨212829343893862454858229065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141886229262574969905486043 212829343893862454858229065)
    ·
      refine ⟨159622007920396841143671799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212829343893862454858229065 159622007920396841143671799)
      ·
        refine ⟨239433011880595261715507699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159622007920396841143671799 239433011880595261715507699)
        ·
          refine ⟨359149517820892892573261549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239433011880595261715507699 359149517820892892573261549)
          ·
            refine ⟨134681069182834834714973081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359149517820892892573261549 134681069182834834714973081)
            ·
              refine ⟨101010801887126126036229811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134681069182834834714973081 101010801887126126036229811)
              ·
                refine ⟨151516202830689189054344717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101010801887126126036229811 151516202830689189054344717)
                ·
                  refine ⟨56818576061508445895379269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151516202830689189054344717 56818576061508445895379269)
                  ·
                    refine ⟨10653483011532833605383613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56818576061508445895379269 10653483011532833605383613)
                    ·
                      refine ⟨3995056129324812602018855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653483011532833605383613 3995056129324812602018855)
                      ·
                        rfl

theorem cell23_7780344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_7780344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780344 prefixEnd_7780344 := by exact prefixLift 7780344
  have htrace : WordTrace (prefixWord ++ tailWord_7780344) baseStart_7780344 baseEnd_7780344 := by
    simpa [prefixWord, tailWord_7780344, baseEnd_7780344] using wordTrace_append hprefix tailTrace_7780344
  have hstable : (prefixWord ++ tailWord_7780344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780344).length < 2 ^ (prefixWord ++ tailWord_7780344).sum := by decide
  have hdescent : baseEnd_7780344 < baseStart_7780344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780381 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 6]
def baseStart_7780381 : Nat := 118140960795 + 7780381 * 2 ^ 59
def prefixEnd_7780381 : Nat := 4983230072969 + 3 ^ 40 * 7780381 * 2
def baseEnd_7780381 : Nat := 443897236456558773028465

theorem tailTrace_7780381 : CollatzResearch.WordTrace tailWord_7780381 prefixEnd_7780381 443897236456558773028465 := by
  unfold tailWord_7780381
  simp only [CollatzResearch.WordTrace]
  refine ⟨283773808026015895130068997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189182538684010596753379331 283773808026015895130068997)
  ·
    refine ⟨53207589004877980336887937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283773808026015895130068997 53207589004877980336887937)
    ·
      refine ⟨39905691753658485252665953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53207589004877980336887937 39905691753658485252665953)
      ·
        refine ⟨29929268815243863939499465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39905691753658485252665953 29929268815243863939499465)
        ·
          refine ⟨22446951611432897954624599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29929268815243863939499465 22446951611432897954624599)
          ·
            refine ⟨33670427417149346931936899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22446951611432897954624599 33670427417149346931936899)
            ·
              refine ⟨50505641125724020397905349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33670427417149346931936899 50505641125724020397905349)
              ·
                refine ⟨9469807711073253824607253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50505641125724020397905349 9469807711073253824607253)
                ·
                  refine ⟨443897236456558773028465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9469807711073253824607253 443897236456558773028465)
                  ·
                    rfl

theorem cell23_7780381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_7780381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780381 prefixEnd_7780381 := by exact prefixLift 7780381
  have htrace : WordTrace (prefixWord ++ tailWord_7780381) baseStart_7780381 baseEnd_7780381 := by
    simpa [prefixWord, tailWord_7780381, baseEnd_7780381] using wordTrace_append hprefix tailTrace_7780381
  have hstable : (prefixWord ++ tailWord_7780381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780381).length < 2 ^ (prefixWord ++ tailWord_7780381).sum := by decide
  have hdescent : baseEnd_7780381 < baseStart_7780381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780385 : List Nat := [1, 2, 3, 2, 4, 1, 1, 4, 1, 4]
def baseStart_7780385 : Nat := 118140960795 + 7780385 * 2 ^ 59
def prefixEnd_7780385 : Nat := 4983230072969 + 3 ^ 40 * 7780385 * 2
def baseEnd_7780385 : Nat := 1331692394010548980535389

theorem tailTrace_7780385 : CollatzResearch.WordTrace tailWord_7780385 prefixEnd_7780385 1331692394010548980535389 := by
  unfold tailWord_7780385
  simp only [CollatzResearch.WordTrace]
  refine ⟨283773953918001403813214609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189182635945334269208809739 283773953918001403813214609)
  ·
    refine ⟨212830465438501052859910957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283773953918001403813214609 212830465438501052859910957)
    ·
      refine ⟨79811424539437894822466609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212830465438501052859910957 79811424539437894822466609)
      ·
        refine ⟨59858568404578421116849957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79811424539437894822466609 59858568404578421116849957)
        ·
          refine ⟨11223481575858453959409367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59858568404578421116849957 11223481575858453959409367)
          ·
            refine ⟨16835222363787680939114051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223481575858453959409367 16835222363787680939114051)
            ·
              refine ⟨25252833545681521408671077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16835222363787680939114051 25252833545681521408671077)
              ·
                refine ⟨4734906289815285264125827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25252833545681521408671077 4734906289815285264125827)
                ·
                  refine ⟨7102359434722927896188741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4734906289815285264125827 7102359434722927896188741)
                  ·
                    refine ⟨1331692394010548980535389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7102359434722927896188741 1331692394010548980535389)
                    ·
                      rfl

theorem cell23_7780385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_7780385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780385 prefixEnd_7780385 := by exact prefixLift 7780385
  have htrace : WordTrace (prefixWord ++ tailWord_7780385) baseStart_7780385 baseEnd_7780385 := by
    simpa [prefixWord, tailWord_7780385, baseEnd_7780385] using wordTrace_append hprefix tailTrace_7780385
  have hstable : (prefixWord ++ tailWord_7780385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780385).length < 2 ^ (prefixWord ++ tailWord_7780385).sum := by decide
  have hdescent : baseEnd_7780385 < baseStart_7780385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780424 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 3, 6]
def baseStart_7780424 : Nat := 118140960795 + 7780424 * 2 ^ 59
def prefixEnd_7780424 : Nat := 4983230072969 + 3 ^ 40 * 7780424 * 2
def baseEnd_7780424 : Nat := 1331699069259057429672829

theorem tailTrace_7780424 : CollatzResearch.WordTrace tailWord_7780424 prefixEnd_7780424 1331699069259057429672829 := by
  unfold tailWord_7780424
  simp only [CollatzResearch.WordTrace]
  refine ⟨141887688182430056736942163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189183584243240075649256217 141887688182430056736942163)
  ·
    refine ⟨212831532273645085105413245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141887688182430056736942163 212831532273645085105413245)
    ·
      refine ⟨79811824602616906914529967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212831532273645085105413245 79811824602616906914529967)
      ·
        refine ⟨119717736903925360371794951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79811824602616906914529967 119717736903925360371794951)
        ·
          refine ⟨179576605355888040557692427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119717736903925360371794951 179576605355888040557692427)
          ·
            refine ⟨269364908033832060836538641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179576605355888040557692427 269364908033832060836538641)
            ·
              refine ⟨202023681025374045627403981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269364908033832060836538641 202023681025374045627403981)
              ·
                refine ⟨75758880384515267110276493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202023681025374045627403981 75758880384515267110276493)
                ·
                  refine ⟨28409580144193225166353685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75758880384515267110276493 28409580144193225166353685)
                  ·
                    refine ⟨1331699069259057429672829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28409580144193225166353685 1331699069259057429672829)
                    ·
                      rfl

theorem cell23_7780424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_7780424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780424 prefixEnd_7780424 := by exact prefixLift 7780424
  have htrace : WordTrace (prefixWord ++ tailWord_7780424) baseStart_7780424 baseEnd_7780424 := by
    simpa [prefixWord, tailWord_7780424, baseEnd_7780424] using wordTrace_append hprefix tailTrace_7780424
  have hstable : (prefixWord ++ tailWord_7780424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780424).length < 2 ^ (prefixWord ++ tailWord_7780424).sum := by decide
  have hdescent : baseEnd_7780424 < baseStart_7780424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780425 : List Nat := [1, 2, 1, 1, 2, 2, 6, 3, 1, 1, 3]
def baseStart_7780425 : Nat := 118140960795 + 7780425 * 2 ^ 59
def prefixEnd_7780425 : Nat := 4983230072969 + 3 ^ 40 * 7780425 * 2
def baseEnd_7780425 : Nat := 3995097721257826785105983

theorem tailTrace_7780425 : CollatzResearch.WordTrace tailWord_7780425 prefixEnd_7780425 3995097721257826785105983 := by
  unfold tailWord_7780425
  simp only [CollatzResearch.WordTrace]
  refine ⟨283775412837856490644670729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189183608558570993763113819 283775412837856490644670729)
  ·
    refine ⟨212831559628392367983503047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283775412837856490644670729 212831559628392367983503047)
    ·
      refine ⟨319247339442588551975254571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212831559628392367983503047 319247339442588551975254571)
      ·
        refine ⟨478871009163882827962881857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319247339442588551975254571 478871009163882827962881857)
        ·
          refine ⟨359153256872912120972161393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478871009163882827962881857 359153256872912120972161393)
          ·
            refine ⟨269364942654684090729121045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359153256872912120972161393 269364942654684090729121045)
            ·
              refine ⟨12626481686938316752927549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269364942654684090729121045 12626481686938316752927549)
              ·
                refine ⟨4734930632601868782347831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12626481686938316752927549 4734930632601868782347831)
                ·
                  refine ⟨7102395948902803173521747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4734930632601868782347831 7102395948902803173521747)
                  ·
                    refine ⟨10653593923354204760282621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7102395948902803173521747 10653593923354204760282621)
                    ·
                      refine ⟨3995097721257826785105983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653593923354204760282621 3995097721257826785105983)
                      ·
                        rfl

theorem cell23_7780425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 1, 3].length) (baseStart_7780425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780425 prefixEnd_7780425 := by exact prefixLift 7780425
  have htrace : WordTrace (prefixWord ++ tailWord_7780425) baseStart_7780425 baseEnd_7780425 := by
    simpa [prefixWord, tailWord_7780425, baseEnd_7780425] using wordTrace_append hprefix tailTrace_7780425
  have hstable : (prefixWord ++ tailWord_7780425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780425).length < 2 ^ (prefixWord ++ tailWord_7780425).sum := by decide
  have hdescent : baseEnd_7780425 < baseStart_7780425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780428 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_7780428 : Nat := 118140960795 + 7780428 * 2 ^ 59
def prefixEnd_7780428 : Nat := 4983230072969 + 3 ^ 40 * 7780428 * 2
def baseEnd_7780428 : Nat := 1331699753899930091122823

theorem tailTrace_7780428 : CollatzResearch.WordTrace tailWord_7780428 prefixEnd_7780428 1331699753899930091122823 := by
  unfold tailWord_7780428
  simp only [CollatzResearch.WordTrace]
  refine ⟨141887761128422811078514969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189183681504563748104686625 141887761128422811078514969)
  ·
    refine ⟨106415820846317108308886227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141887761128422811078514969 106415820846317108308886227)
    ·
      refine ⟨159623731269475662463329341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106415820846317108308886227 159623731269475662463329341)
      ·
        refine ⟨59858899226053373423748503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159623731269475662463329341 59858899226053373423748503)
        ·
          refine ⟨89788348839080060135622755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59858899226053373423748503 89788348839080060135622755)
          ·
            refine ⟨134682523258620090203434133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89788348839080060135622755 134682523258620090203434133)
            ·
              refine ⟨6313243277747816728285975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134682523258620090203434133 6313243277747816728285975)
              ·
                refine ⟨9469864916621725092428963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6313243277747816728285975 9469864916621725092428963)
                ·
                  refine ⟨14204797374932587638643445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469864916621725092428963 14204797374932587638643445)
                  ·
                    refine ⟨1331699753899930091122823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14204797374932587638643445 1331699753899930091122823)
                    ·
                      rfl

theorem cell23_7780428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_7780428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780428 prefixEnd_7780428 := by exact prefixLift 7780428
  have htrace : WordTrace (prefixWord ++ tailWord_7780428) baseStart_7780428 baseEnd_7780428 := by
    simpa [prefixWord, tailWord_7780428, baseEnd_7780428] using wordTrace_append hprefix tailTrace_7780428
  have hstable : (prefixWord ++ tailWord_7780428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780428).length < 2 ^ (prefixWord ++ tailWord_7780428).sum := by decide
  have hdescent : baseEnd_7780428 < baseStart_7780428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780431 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 4]
def baseStart_7780431 : Nat := 118140960795 + 7780431 * 2 ^ 59
def prefixEnd_7780431 : Nat := 4983230072969 + 3 ^ 40 * 7780431 * 2
def baseEnd_7780431 : Nat := 3995100802141753761630955

theorem tailTrace_7780431 : CollatzResearch.WordTrace tailWord_7780431 prefixEnd_7780431 3995100802141753761630955 := by
  unfold tailWord_7780431
  simp only [CollatzResearch.WordTrace]
  refine ⟨283775631675834753669389147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189183754450556502446259431 283775631675834753669389147)
  ·
    refine ⟨425663447513752130504083721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283775631675834753669389147 425663447513752130504083721)
    ·
      refine ⟨319247585635314097878062791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425663447513752130504083721 319247585635314097878062791)
      ·
        refine ⟨478871378452971146817094187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319247585635314097878062791 478871378452971146817094187)
        ·
          refine ⟨718307067679456720225641281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478871378452971146817094187 718307067679456720225641281)
          ·
            refine ⟨538730300759592540169230961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718307067679456720225641281 538730300759592540169230961)
            ·
              refine ⟨404047725569694405126923221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538730300759592540169230961 404047725569694405126923221)
              ·
                refine ⟨9469868568039712620162263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 404047725569694405126923221 9469868568039712620162263)
                ·
                  refine ⟨14204802852059568930243395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469868568039712620162263 14204802852059568930243395)
                  ·
                    refine ⟨21307204278089353395365093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14204802852059568930243395 21307204278089353395365093)
                    ·
                      refine ⟨3995100802141753761630955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21307204278089353395365093 3995100802141753761630955)
                      ·
                        rfl

theorem cell23_7780431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 1, 4].length) (baseStart_7780431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780431 prefixEnd_7780431 := by exact prefixLift 7780431
  have htrace : WordTrace (prefixWord ++ tailWord_7780431) baseStart_7780431 baseEnd_7780431 := by
    simpa [prefixWord, tailWord_7780431, baseEnd_7780431] using wordTrace_append hprefix tailTrace_7780431
  have hstable : (prefixWord ++ tailWord_7780431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780431).length < 2 ^ (prefixWord ++ tailWord_7780431).sum := by decide
  have hdescent : baseEnd_7780431 < baseStart_7780431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780441 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 4, 4]
def baseStart_7780441 : Nat := 118140960795 + 7780441 * 2 ^ 59
def prefixEnd_7780441 : Nat := 4983230072969 + 3 ^ 40 * 7780441 * 2
def baseEnd_7780441 : Nat := 1331701978982766240835303

theorem tailTrace_7780441 : CollatzResearch.WordTrace tailWord_7780441 prefixEnd_7780441 1331701978982766240835303 := by
  unfold tailWord_7780441
  simp only [CollatzResearch.WordTrace]
  refine ⟨283775996405798525377253177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189183997603865683584835451 283775996405798525377253177)
  ·
    refine ⟨212831997304348894032939883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283775996405798525377253177 212831997304348894032939883)
    ·
      refine ⟨319247995956523341049409825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212831997304348894032939883 319247995956523341049409825)
      ·
        refine ⟨239435996967392505787057369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319247995956523341049409825 239435996967392505787057369)
        ·
          refine ⟨179576997725544379340293027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239435996967392505787057369 179576997725544379340293027)
          ·
            refine ⟨269365496588316569010439541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179576997725544379340293027 269365496588316569010439541)
            ·
              refine ⟨25253015305154678344728707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269365496588316569010439541 25253015305154678344728707)
              ·
                refine ⟨37879522957732017517093061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25253015305154678344728707 37879522957732017517093061)
                ·
                  refine ⟨7102410554574753284454949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37879522957732017517093061 7102410554574753284454949)
                  ·
                    refine ⟨1331701978982766240835303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7102410554574753284454949 1331701978982766240835303)
                    ·
                      rfl

theorem cell23_7780441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 4].length) (baseStart_7780441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780441 prefixEnd_7780441 := by exact prefixLift 7780441
  have htrace : WordTrace (prefixWord ++ tailWord_7780441) baseStart_7780441 baseEnd_7780441 := by
    simpa [prefixWord, tailWord_7780441, baseEnd_7780441] using wordTrace_append hprefix tailTrace_7780441
  have hstable : (prefixWord ++ tailWord_7780441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780441).length < 2 ^ (prefixWord ++ tailWord_7780441).sum := by decide
  have hdescent : baseEnd_7780441 < baseStart_7780441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780451 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 3]
def baseStart_7780451 : Nat := 118140960795 + 7780451 * 2 ^ 59
def prefixEnd_7780451 : Nat := 4983230072969 + 3 ^ 40 * 7780451 * 2
def baseEnd_7780451 : Nat := 3995111071754843683380863

theorem tailTrace_7780451 : CollatzResearch.WordTrace tailWord_7780451 prefixEnd_7780451 3995111071754843683380863 := by
  unfold tailWord_7780451
  simp only [CollatzResearch.WordTrace]
  refine ⟨283776361135762297085117207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189184240757174864723411471 283776361135762297085117207)
  ·
    refine ⟨425664541703643445627675811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283776361135762297085117207 425664541703643445627675811)
    ·
      refine ⟨638496812555465168441513717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425664541703643445627675811 638496812555465168441513717)
      ·
        refine ⟨59859076177074859541391911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 638496812555465168441513717 59859076177074859541391911)
        ·
          refine ⟨89788614265612289312087867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59859076177074859541391911 89788614265612289312087867)
          ·
            refine ⟨134682921398418433968131801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89788614265612289312087867 134682921398418433968131801)
            ·
              refine ⟨101012191048813825476098851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134682921398418433968131801 101012191048813825476098851)
              ·
                refine ⟨151518286573220738214148277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101012191048813825476098851 151518286573220738214148277)
                ·
                  refine ⟨14204839366239444207576401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151518286573220738214148277 14204839366239444207576401)
                  ·
                    refine ⟨10653629524679583155682301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14204839366239444207576401 10653629524679583155682301)
                    ·
                      refine ⟨3995111071754843683380863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653629524679583155682301 3995111071754843683380863)
                      ·
                        rfl

theorem cell23_7780451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_7780451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780451 prefixEnd_7780451 := by exact prefixLift 7780451
  have htrace : WordTrace (prefixWord ++ tailWord_7780451) baseStart_7780451 baseEnd_7780451 := by
    simpa [prefixWord, tailWord_7780451, baseEnd_7780451] using wordTrace_append hprefix tailTrace_7780451
  have hstable : (prefixWord ++ tailWord_7780451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780451).length < 2 ^ (prefixWord ++ tailWord_7780451).sum := by decide
  have hdescent : baseEnd_7780451 < baseStart_7780451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780461 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_7780461 : Nat := 118140960795 + 7780461 * 2 ^ 59
def prefixEnd_7780461 : Nat := 4983230072969 + 3 ^ 40 * 7780461 * 2
def baseEnd_7780461 : Nat := 3995116206561388644255817

theorem tailTrace_7780461 : CollatzResearch.WordTrace tailWord_7780461 prefixEnd_7780461 3995116206561388644255817 := by
  unfold tailWord_7780461
  simp only [CollatzResearch.WordTrace]
  refine ⟨283776725865726068792981237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189184483910484045861987491 283776725865726068792981237)
  ·
    refine ⟨26604068049911818949341991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283776725865726068792981237 26604068049911818949341991)
    ·
      refine ⟨39906102074867728424012987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26604068049911818949341991 39906102074867728424012987)
      ·
        refine ⟨59859153112301592636019481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39906102074867728424012987 59859153112301592636019481)
        ·
          refine ⟨44894364834226194477014611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59859153112301592636019481 44894364834226194477014611)
          ·
            refine ⟨67341547251339291715521917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44894364834226194477014611 67341547251339291715521917)
            ·
              refine ⟨25253080219252234393320719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67341547251339291715521917 25253080219252234393320719)
              ·
                refine ⟨37879620328878351589981079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25253080219252234393320719 37879620328878351589981079)
                ·
                  refine ⟨56819430493317527384971619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37879620328878351589981079 56819430493317527384971619)
                  ·
                    refine ⟨85229145739976291077457429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56819430493317527384971619 85229145739976291077457429)
                    ·
                      refine ⟨3995116206561388644255817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85229145739976291077457429 3995116206561388644255817)
                      ·
                        rfl

theorem cell23_7780461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_7780461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780461 prefixEnd_7780461 := by exact prefixLift 7780461
  have htrace : WordTrace (prefixWord ++ tailWord_7780461) baseStart_7780461 baseEnd_7780461 := by
    simpa [prefixWord, tailWord_7780461, baseEnd_7780461] using wordTrace_append hprefix tailTrace_7780461
  have hstable : (prefixWord ++ tailWord_7780461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780461).length < 2 ^ (prefixWord ++ tailWord_7780461).sum := by decide
  have hdescent : baseEnd_7780461 < baseStart_7780461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780471 : List Nat := [1, 1, 3, 1, 1, 5, 4, 7]
def baseStart_7780471 : Nat := 118140960795 + 7780471 * 2 ^ 59
def prefixEnd_7780471 : Nat := 4983230072969 + 3 ^ 40 * 7780471 * 2
def baseEnd_7780471 : Nat := 147967457087701244634473

theorem tailTrace_7780471 : CollatzResearch.WordTrace tailWord_7780471 prefixEnd_7780471 147967457087701244634473 := by
  unfold tailWord_7780471
  simp only [CollatzResearch.WordTrace]
  refine ⟨283777090595689840500845267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189184727063793227000563511 283777090595689840500845267)
  ·
    refine ⟨425665635893534760751267901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283777090595689840500845267 425665635893534760751267901)
    ·
      refine ⟨159624613460075535281725463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425665635893534760751267901 159624613460075535281725463)
      ·
        refine ⟨239436920190113302922588195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159624613460075535281725463 239436920190113302922588195)
        ·
          refine ⟨359155380285169954383882293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239436920190113302922588195 359155380285169954383882293)
          ·
            refine ⟨33670816901734683223488965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359155380285169954383882293 33670816901734683223488965)
            ·
              refine ⟨6313278169075253104404181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33670816901734683223488965 6313278169075253104404181)
              ·
                refine ⟨147967457087701244634473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6313278169075253104404181 147967457087701244634473)
                ·
                  rfl

theorem cell23_7780471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 7].length) (baseStart_7780471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780471 prefixEnd_7780471 := by exact prefixLift 7780471
  have htrace : WordTrace (prefixWord ++ tailWord_7780471) baseStart_7780471 baseEnd_7780471 := by
    simpa [prefixWord, tailWord_7780471, baseEnd_7780471] using wordTrace_append hprefix tailTrace_7780471
  have hstable : (prefixWord ++ tailWord_7780471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780471).length < 2 ^ (prefixWord ++ tailWord_7780471).sum := by decide
  have hdescent : baseEnd_7780471 < baseStart_7780471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780474 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_7780474 : Nat := 118140960795 + 7780474 * 2 ^ 59
def prefixEnd_7780474 : Nat := 4983230072969 + 3 ^ 40 * 7780474 * 2
def baseEnd_7780474 : Nat := 3995122881809897093393257

theorem tailTrace_7780474 : CollatzResearch.WordTrace tailWord_7780474 prefixEnd_7780474 3995122881809897093393257 := by
  unfold tailWord_7780474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70944300003669743003301119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189184800009785981342136317 70944300003669743003301119)
  ·
    refine ⟨106416450005504614504951679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70944300003669743003301119 106416450005504614504951679)
    ·
      refine ⟨159624675008256921757427519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106416450005504614504951679 159624675008256921757427519)
      ·
        refine ⟨239437012512385382636141279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159624675008256921757427519 239437012512385382636141279)
        ·
          refine ⟨359155518768578073954211919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239437012512385382636141279 359155518768578073954211919)
          ·
            refine ⟨538733278152867110931317879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359155518768578073954211919 538733278152867110931317879)
            ·
              refine ⟨808099917229300666396976819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538733278152867110931317879 808099917229300666396976819)
              ·
                refine ⟨1212149875843950999595465229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808099917229300666396976819 1212149875843950999595465229)
                ·
                  refine ⟨454556203441481624848299461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212149875843950999595465229 454556203441481624848299461)
                  ·
                    refine ⟨85229288145277804659056149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454556203441481624848299461 85229288145277804659056149)
                    ·
                      refine ⟨3995122881809897093393257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85229288145277804659056149 3995122881809897093393257)
                      ·
                        rfl

theorem cell23_7780474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_7780474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780474 prefixEnd_7780474 := by exact prefixLift 7780474
  have htrace : WordTrace (prefixWord ++ tailWord_7780474) baseStart_7780474 baseEnd_7780474 := by
    simpa [prefixWord, tailWord_7780474, baseEnd_7780474] using wordTrace_append hprefix tailTrace_7780474
  have hstable : (prefixWord ++ tailWord_7780474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780474).length < 2 ^ (prefixWord ++ tailWord_7780474).sum := by decide
  have hdescent : baseEnd_7780474 < baseStart_7780474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780519 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_7780519 : Nat := 118140960795 + 7780519 * 2 ^ 59
def prefixEnd_7780519 : Nat := 4983230072969 + 3 ^ 40 * 7780519 * 2
def baseEnd_7780519 : Nat := 3995145988439349417330551

theorem tailTrace_7780519 : CollatzResearch.WordTrace tailWord_7780519 prefixEnd_7780519 3995145988439349417330551 := by
  unfold tailWord_7780519
  simp only [CollatzResearch.WordTrace]
  refine ⟨283778841299515944698592611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189185894199677296465728407 283778841299515944698592611)
  ·
    refine ⟨425668261949273917047888917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283778841299515944698592611 425668261949273917047888917)
    ·
      refine ⟨19953199778872214861619793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 425668261949273917047888917 19953199778872214861619793)
      ·
        refine ⟨14964899834154161146214845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19953199778872214861619793 14964899834154161146214845)
        ·
          refine ⟨5611837437807810429830567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14964899834154161146214845 5611837437807810429830567)
          ·
            refine ⟨8417756156711715644745851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611837437807810429830567 8417756156711715644745851)
            ·
              refine ⟨12626634235067573467118777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8417756156711715644745851 12626634235067573467118777)
              ·
                refine ⟨9469975676300680100339083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12626634235067573467118777 9469975676300680100339083)
                ·
                  refine ⟨14204963514451020150508625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469975676300680100339083 14204963514451020150508625)
                  ·
                    refine ⟨10653722635838265112881469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14204963514451020150508625 10653722635838265112881469)
                    ·
                      refine ⟨3995145988439349417330551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653722635838265112881469 3995145988439349417330551)
                      ·
                        rfl

theorem cell23_7780519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_7780519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780519 prefixEnd_7780519 := by exact prefixLift 7780519
  have htrace : WordTrace (prefixWord ++ tailWord_7780519) baseStart_7780519 baseEnd_7780519 := by
    simpa [prefixWord, tailWord_7780519, baseEnd_7780519] using wordTrace_append hprefix tailTrace_7780519
  have hstable : (prefixWord ++ tailWord_7780519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780519).length < 2 ^ (prefixWord ++ tailWord_7780519).sum := by decide
  have hdescent : baseEnd_7780519 < baseStart_7780519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780538 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2]
def baseStart_7780538 : Nat := 118140960795 + 7780538 * 2 ^ 59
def prefixEnd_7780538 : Nat := 4983230072969 + 3 ^ 40 * 7780538 * 2
def baseEnd_7780538 : Nat := 3995155744571784842992963

theorem tailTrace_7780538 : CollatzResearch.WordTrace tailWord_7780538 prefixEnd_7780538 3995155744571784842992963 := by
  unfold tailWord_7780538
  simp only [CollatzResearch.WordTrace]
  refine ⟨70944883571611777735883567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189186356190964740629022845 70944883571611777735883567)
  ·
    refine ⟨106417325357417666603825351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70944883571611777735883567 106417325357417666603825351)
    ·
      refine ⟨159625988036126499905738027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106417325357417666603825351 159625988036126499905738027)
      ·
        refine ⟨239438982054189749858607041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159625988036126499905738027 239438982054189749858607041)
        ·
          refine ⟨179579236540642312393955281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239438982054189749858607041 179579236540642312393955281)
          ·
            refine ⟨134684427405481734295466461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179579236540642312393955281 134684427405481734295466461)
            ·
              refine ⟨50506660277055650360799923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134684427405481734295466461 50506660277055650360799923)
              ·
                refine ⟨75759990415583475541199885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50506660277055650360799923 75759990415583475541199885)
                ·
                  refine ⟨28409996405843803327949957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75759990415583475541199885 28409996405843803327949957)
                  ·
                    refine ⟨5326874326095713123990617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28409996405843803327949957 5326874326095713123990617)
                    ·
                      refine ⟨3995155744571784842992963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5326874326095713123990617 3995155744571784842992963)
                      ·
                        rfl

theorem cell23_7780538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_7780538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780538 prefixEnd_7780538 := by exact prefixLift 7780538
  have htrace : WordTrace (prefixWord ++ tailWord_7780538) baseStart_7780538 baseEnd_7780538 := by
    simpa [prefixWord, tailWord_7780538, baseEnd_7780538] using wordTrace_append hprefix tailTrace_7780538
  have hstable : (prefixWord ++ tailWord_7780538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780538).length < 2 ^ (prefixWord ++ tailWord_7780538).sum := by decide
  have hdescent : baseEnd_7780538 < baseStart_7780538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780558 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_7780558 : Nat := 118140960795 + 7780558 * 2 ^ 59
def prefixEnd_7780558 : Nat := 4983230072969 + 3 ^ 40 * 7780558 * 2
def baseEnd_7780558 : Nat := 3995166014184874764742871

theorem tailTrace_7780558 : CollatzResearch.WordTrace tailWord_7780558 prefixEnd_7780558 3995166014184874764742871 := by
  unfold tailWord_7780558
  simp only [CollatzResearch.WordTrace]
  refine ⟨35472532968296831794907791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189186842497583102906174885 35472532968296831794907791)
  ·
    refine ⟨53208799452445247692361687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35472532968296831794907791 53208799452445247692361687)
    ·
      refine ⟨79813199178667871538542531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53208799452445247692361687 79813199178667871538542531)
      ·
        refine ⟨119719798768001807307813797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79813199178667871538542531 119719798768001807307813797)
        ·
          refine ⟨22447462269000338870215087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119719798768001807307813797 22447462269000338870215087)
          ·
            refine ⟨33671193403500508305322631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22447462269000338870215087 33671193403500508305322631)
            ·
              refine ⟨50506790105250762457983947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33671193403500508305322631 50506790105250762457983947)
              ·
                refine ⟨75760185157876143686975921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50506790105250762457983947 75760185157876143686975921)
                ·
                  refine ⟨56820138868407107765231941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75760185157876143686975921 56820138868407107765231941)
                  ·
                    refine ⟨10653776037826332705980989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56820138868407107765231941 10653776037826332705980989)
                    ·
                      refine ⟨3995166014184874764742871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653776037826332705980989 3995166014184874764742871)
                      ·
                        rfl

theorem cell23_7780558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_7780558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780558 prefixEnd_7780558 := by exact prefixLift 7780558
  have htrace : WordTrace (prefixWord ++ tailWord_7780558) baseStart_7780558 baseEnd_7780558 := by
    simpa [prefixWord, tailWord_7780558, baseEnd_7780558] using wordTrace_append hprefix tailTrace_7780558
  have hstable : (prefixWord ++ tailWord_7780558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780558).length < 2 ^ (prefixWord ++ tailWord_7780558).sum := by decide
  have hdescent : baseEnd_7780558 < baseStart_7780558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780568 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_7780568 : Nat := 118140960795 + 7780568 * 2 ^ 59
def prefixEnd_7780568 : Nat := 4983230072969 + 3 ^ 40 * 7780568 * 2
def baseEnd_7780568 : Nat := 3995171148991419725617825

theorem tailTrace_7780568 : CollatzResearch.WordTrace tailWord_7780568 prefixEnd_7780568 3995171148991419725617825 := by
  unfold tailWord_7780568
  simp only [CollatzResearch.WordTrace]
  refine ⟨141890314238169213033563179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189187085650892284044750905 141890314238169213033563179)
  ·
    refine ⟨212835471357253819550344769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141890314238169213033563179 212835471357253819550344769)
    ·
      refine ⟨159626603517940364662758577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212835471357253819550344769 159626603517940364662758577)
      ·
        refine ⟨119719952638455273497068933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159626603517940364662758577 119719952638455273497068933)
        ·
          refine ⟨22447491119710363780700425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119719952638455273497068933 22447491119710363780700425)
          ·
            refine ⟨16835618339782772835525319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22447491119710363780700425 16835618339782772835525319)
            ·
              refine ⟨25253427509674159253287979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16835618339782772835525319 25253427509674159253287979)
              ·
                refine ⟨37880141264511238879931969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25253427509674159253287979 37880141264511238879931969)
                ·
                  refine ⟨28410105948383429159948977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37880141264511238879931969 28410105948383429159948977)
                  ·
                    refine ⟨21307579461287571869961733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28410105948383429159948977 21307579461287571869961733)
                    ·
                      refine ⟨3995171148991419725617825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21307579461287571869961733 3995171148991419725617825)
                      ·
                        rfl

theorem cell23_7780568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_7780568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780568 prefixEnd_7780568 := by exact prefixLift 7780568
  have htrace : WordTrace (prefixWord ++ tailWord_7780568) baseStart_7780568 baseEnd_7780568 := by
    simpa [prefixWord, tailWord_7780568, baseEnd_7780568] using wordTrace_append hprefix tailTrace_7780568
  have hstable : (prefixWord ++ tailWord_7780568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780568).length < 2 ^ (prefixWord ++ tailWord_7780568).sum := by decide
  have hdescent : baseEnd_7780568 < baseStart_7780568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780571 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 3]
def baseStart_7780571 : Nat := 118140960795 + 7780571 * 2 ^ 59
def prefixEnd_7780571 : Nat := 4983230072969 + 3 ^ 40 * 7780571 * 2
def baseEnd_7780571 : Nat := 3995172689433383213880311

theorem tailTrace_7780571 : CollatzResearch.WordTrace tailWord_7780571 prefixEnd_7780571 3995172689433383213880311 := by
  unfold tailWord_7780571
  simp only [CollatzResearch.WordTrace]
  refine ⟨283780737895327557579485567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189187158596885038386323711 283780737895327557579485567)
  ·
    refine ⟨425671106842991336369228351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283780737895327557579485567 425671106842991336369228351)
    ·
      refine ⟨638506660264487004553842527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425671106842991336369228351 638506660264487004553842527)
      ·
        refine ⟨957759990396730506830763791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638506660264487004553842527 957759990396730506830763791)
        ·
          refine ⟨1436639985595095760246145687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957759990396730506830763791 1436639985595095760246145687)
          ·
            refine ⟨2154959978392643640369218531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436639985595095760246145687 2154959978392643640369218531)
            ·
              refine ⟨3232439967588965460553827797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154959978392643640369218531 3232439967588965460553827797)
              ·
                refine ⟨75760311740366377981730339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3232439967588965460553827797 75760311740366377981730339)
                ·
                  refine ⟨113640467610549566972595509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75760311740366377981730339 113640467610549566972595509)
                  ·
                    refine ⟨10653793838489021903680829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113640467610549566972595509 10653793838489021903680829)
                    ·
                      refine ⟨3995172689433383213880311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653793838489021903680829 3995172689433383213880311)
                      ·
                        rfl

theorem cell23_7780571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 3].length) (baseStart_7780571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780571 prefixEnd_7780571 := by exact prefixLift 7780571
  have htrace : WordTrace (prefixWord ++ tailWord_7780571) baseStart_7780571 baseEnd_7780571 := by
    simpa [prefixWord, tailWord_7780571, baseEnd_7780571] using wordTrace_append hprefix tailTrace_7780571
  have hstable : (prefixWord ++ tailWord_7780571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780571).length < 2 ^ (prefixWord ++ tailWord_7780571).sum := by decide
  have hdescent : baseEnd_7780571 < baseStart_7780571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780601 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_7780601 : Nat := 118140960795 + 7780601 * 2 ^ 59
def prefixEnd_7780601 : Nat := 4983230072969 + 3 ^ 40 * 7780601 * 2
def baseEnd_7780601 : Nat := 3995188093853018096505173

theorem tailTrace_7780601 : CollatzResearch.WordTrace tailWord_7780601 prefixEnd_7780601 3995188093853018096505173 := by
  unfold tailWord_7780601
  simp only [CollatzResearch.WordTrace]
  refine ⟨283781832085218872703077657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189187888056812581802051771 283781832085218872703077657)
  ·
    refine ⟨212836374063914154527308243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283781832085218872703077657 212836374063914154527308243)
    ·
      refine ⟨319254561095871231790962365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212836374063914154527308243 319254561095871231790962365)
      ·
        refine ⟨119720460410951711921610887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319254561095871231790962365 119720460410951711921610887)
        ·
          refine ⟨179580690616427567882416331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119720460410951711921610887 179580690616427567882416331)
          ·
            refine ⟨269371035924641351823624497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179580690616427567882416331 269371035924641351823624497)
            ·
              refine ⟨202028276943481013867718373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269371035924641351823624497 202028276943481013867718373)
              ·
                refine ⟨37880301926902690100197195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202028276943481013867718373 37880301926902690100197195)
                ·
                  refine ⟨56820452890354035150295793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37880301926902690100197195 56820452890354035150295793)
                  ·
                    refine ⟨42615339667765526362721845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56820452890354035150295793 42615339667765526362721845)
                    ·
                      refine ⟨3995188093853018096505173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42615339667765526362721845 3995188093853018096505173)
                      ·
                        rfl

theorem cell23_7780601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_7780601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780601 prefixEnd_7780601 := by exact prefixLift 7780601
  have htrace : WordTrace (prefixWord ++ tailWord_7780601) baseStart_7780601 baseEnd_7780601 := by
    simpa [prefixWord, tailWord_7780601, baseEnd_7780601] using wordTrace_append hprefix tailTrace_7780601
  have hstable : (prefixWord ++ tailWord_7780601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780601).length < 2 ^ (prefixWord ++ tailWord_7780601).sum := by decide
  have hdescent : baseEnd_7780601 < baseStart_7780601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780665 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7780665 : Nat := 118140960795 + 7780665 * 2 ^ 59
def prefixEnd_7780665 : Nat := 4983230072969 + 3 ^ 40 * 7780665 * 2
def baseEnd_7780665 : Nat := 3995220956614905846104879

theorem tailTrace_7780665 : CollatzResearch.WordTrace tailWord_7780665 prefixEnd_7780665 3995220956614905846104879 := by
  unfold tailWord_7780665
  simp only [CollatzResearch.WordTrace]
  refine ⟨283784166356987011633407449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189189444237991341088938299 283784166356987011633407449)
  ·
    refine ⟨212838124767740258725055587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283784166356987011633407449 212838124767740258725055587)
    ·
      refine ⟨319257187151610388087583381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212838124767740258725055587 319257187151610388087583381)
      ·
        refine ⟨14965180647731736941605471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 319257187151610388087583381 14965180647731736941605471)
        ·
          refine ⟨22447770971597605412408207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14965180647731736941605471 22447770971597605412408207)
          ·
            refine ⟨33671656457396408118612311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22447770971597605412408207 33671656457396408118612311)
            ·
              refine ⟨50507484686094612177918467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33671656457396408118612311 50507484686094612177918467)
              ·
                refine ⟨75761227029141918266877701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50507484686094612177918467 75761227029141918266877701)
                ·
                  refine ⟨14205230067964109675039569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75761227029141918266877701 14205230067964109675039569)
                  ·
                    refine ⟨10653922550973082256279677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14205230067964109675039569 10653922550973082256279677)
                    ·
                      refine ⟨3995220956614905846104879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653922550973082256279677 3995220956614905846104879)
                      ·
                        rfl

theorem cell23_7780665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7780665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780665 prefixEnd_7780665 := by exact prefixLift 7780665
  have htrace : WordTrace (prefixWord ++ tailWord_7780665) baseStart_7780665 baseEnd_7780665 := by
    simpa [prefixWord, tailWord_7780665, baseEnd_7780665] using wordTrace_append hprefix tailTrace_7780665
  have hstable : (prefixWord ++ tailWord_7780665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780665).length < 2 ^ (prefixWord ++ tailWord_7780665).sum := by decide
  have hdescent : baseEnd_7780665 < baseStart_7780665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780668 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 6]
def baseStart_7780668 : Nat := 118140960795 + 7780668 * 2 ^ 59
def prefixEnd_7780668 : Nat := 4983230072969 + 3 ^ 40 * 7780668 * 2
def baseEnd_7780668 : Nat := 443913610784096592707485

theorem tailTrace_7780668 : CollatzResearch.WordTrace tailWord_7780668 prefixEnd_7780668 443913610784096592707485 := by
  unfold tailWord_7780668
  simp only [CollatzResearch.WordTrace]
  refine ⟨141892137887988071572883329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189189517183984095430511105 141892137887988071572883329)
  ·
    refine ⟨106419103415991053679662497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141892137887988071572883329 106419103415991053679662497)
    ·
      refine ⟨79814327561993290259746873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106419103415991053679662497 79814327561993290259746873)
      ·
        refine ⟨59860745671494967694810155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79814327561993290259746873 59860745671494967694810155)
        ·
          refine ⟨89791118507242451542215233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59860745671494967694810155 89791118507242451542215233)
          ·
            refine ⟨67343338880431838656661425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89791118507242451542215233 67343338880431838656661425)
            ·
              refine ⟨50507504160323878992496069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67343338880431838656661425 50507504160323878992496069)
              ·
                refine ⟨9470157030060727311093013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50507504160323878992496069 9470157030060727311093013)
                ·
                  refine ⟨443913610784096592707485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9470157030060727311093013 443913610784096592707485)
                  ·
                    rfl

theorem cell23_7780668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_7780668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780668 prefixEnd_7780668 := by exact prefixLift 7780668
  have htrace : WordTrace (prefixWord ++ tailWord_7780668) baseStart_7780668 baseEnd_7780668 := by
    simpa [prefixWord, tailWord_7780668, baseEnd_7780668] using wordTrace_append hprefix tailTrace_7780668
  have hstable : (prefixWord ++ tailWord_7780668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780668).length < 2 ^ (prefixWord ++ tailWord_7780668).sum := by decide
  have hdescent : baseEnd_7780668 < baseStart_7780668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780681 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 2, 9]
def baseStart_7780681 : Nat := 118140960795 + 7780681 * 2 ^ 59
def prefixEnd_7780681 : Nat := 4983230072969 + 3 ^ 40 * 7780681 * 2
def baseEnd_7780681 : Nat := 1331743057435125927834935

theorem tailTrace_7780681 : CollatzResearch.WordTrace tailWord_7780681 prefixEnd_7780681 1331743057435125927834935 := by
  unfold tailWord_7780681
  simp only [CollatzResearch.WordTrace]
  refine ⟨283784749924929046365989897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189189833283286030910659931 283784749924929046365989897)
  ·
    refine ⟨212838562443696784774492423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283784749924929046365989897 212838562443696784774492423)
    ·
      refine ⟨319257843665545177161738635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212838562443696784774492423 319257843665545177161738635)
      ·
        refine ⟨478886765498317765742607953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319257843665545177161738635 478886765498317765742607953)
        ·
          refine ⟨359165074123738324306955965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478886765498317765742607953 359165074123738324306955965)
          ·
            refine ⟨134686902796401871615108487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359165074123738324306955965 134686902796401871615108487)
            ·
              refine ⟨202030354194602807422662731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134686902796401871615108487 202030354194602807422662731)
              ·
                refine ⟨303045531291904211133994097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202030354194602807422662731 303045531291904211133994097)
                ·
                  refine ⟨227284148468928158350495573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303045531291904211133994097 227284148468928158350495573)
                  ·
                    refine ⟨1331743057435125927834935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227284148468928158350495573 1331743057435125927834935)
                    ·
                      rfl

theorem cell23_7780681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_7780681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780681 prefixEnd_7780681 := by exact prefixLift 7780681
  have htrace : WordTrace (prefixWord ++ tailWord_7780681) baseStart_7780681 baseEnd_7780681 := by
    simpa [prefixWord, tailWord_7780681, baseEnd_7780681] using wordTrace_append hprefix tailTrace_7780681
  have hstable : (prefixWord ++ tailWord_7780681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780681).length < 2 ^ (prefixWord ++ tailWord_7780681).sum := by decide
  have hdescent : baseEnd_7780681 < baseStart_7780681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780691 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 7]
def baseStart_7780691 : Nat := 118140960795 + 7780691 * 2 ^ 59
def prefixEnd_7780691 : Nat := 4983230072969 + 3 ^ 40 * 7780691 * 2
def baseEnd_7780691 : Nat := 3995234307111922744379759

theorem tailTrace_7780691 : CollatzResearch.WordTrace tailWord_7780691 prefixEnd_7780691 3995234307111922744379759 := by
  unfold tailWord_7780691
  simp only [CollatzResearch.WordTrace]
  refine ⟨283785114654892818073853927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189190076436595212049235951 283785114654892818073853927)
  ·
    refine ⟨425677671982339227110780891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283785114654892818073853927 425677671982339227110780891)
    ·
      refine ⟨638516507973508840666171337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425677671982339227110780891 638516507973508840666171337)
      ·
        refine ⟨478887380980131630499628503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638516507973508840666171337 478887380980131630499628503)
        ·
          refine ⟨718331071470197445749442755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478887380980131630499628503 718331071470197445749442755)
          ·
            refine ⟨1077496607205296168624164133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718331071470197445749442755 1077496607205296168624164133)
            ·
              refine ⟨202030613850993031617030775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1077496607205296168624164133 202030613850993031617030775)
              ·
                refine ⟨303045920776489547425546163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202030613850993031617030775 303045920776489547425546163)
                ·
                  refine ⟨454568881164734321138319245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303045920776489547425546163 454568881164734321138319245)
                  ·
                    refine ⟨170463330436775370426869717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454568881164734321138319245 170463330436775370426869717)
                    ·
                      refine ⟨3995234307111922744379759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170463330436775370426869717 3995234307111922744379759)
                      ·
                        rfl

theorem cell23_7780691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_7780691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780691 prefixEnd_7780691 := by exact prefixLift 7780691
  have htrace : WordTrace (prefixWord ++ tailWord_7780691) baseStart_7780691 baseEnd_7780691 := by
    simpa [prefixWord, tailWord_7780691, baseEnd_7780691] using wordTrace_append hprefix tailTrace_7780691
  have hstable : (prefixWord ++ tailWord_7780691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780691).length < 2 ^ (prefixWord ++ tailWord_7780691).sum := by decide
  have hdescent : baseEnd_7780691 < baseStart_7780691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780695 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_7780695 : Nat := 118140960795 + 7780695 * 2 ^ 59
def prefixEnd_7780695 : Nat := 4983230072969 + 3 ^ 40 * 7780695 * 2
def baseEnd_7780695 : Nat := 3995236361034540728729741

theorem tailTrace_7780695 : CollatzResearch.WordTrace tailWord_7780695 prefixEnd_7780695 3995236361034540728729741 := by
  unfold tailWord_7780695
  simp only [CollatzResearch.WordTrace]
  refine ⟨283785260546878326756999539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189190173697918884504666359 283785260546878326756999539)
  ·
    refine ⟨425677890820317490135499309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283785260546878326756999539 425677890820317490135499309)
    ·
      refine ⟨159629209057619058800812241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425677890820317490135499309 159629209057619058800812241)
      ·
        refine ⟨119721906793214294100609181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159629209057619058800812241 119721906793214294100609181)
        ·
          refine ⟨44895715047455360287728443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119721906793214294100609181 44895715047455360287728443)
          ·
            refine ⟨67343572571183040431592665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44895715047455360287728443 67343572571183040431592665)
            ·
              refine ⟨50507679428387280323694499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67343572571183040431592665 50507679428387280323694499)
              ·
                refine ⟨75761519142580920485541749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50507679428387280323694499 75761519142580920485541749)
                ·
                  refine ⟨7102642419616961295519539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75761519142580920485541749 7102642419616961295519539)
                  ·
                    refine ⟨10653963629425441943279309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7102642419616961295519539 10653963629425441943279309)
                    ·
                      refine ⟨3995236361034540728729741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10653963629425441943279309 3995236361034540728729741)
                      ·
                        rfl

theorem cell23_7780695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_7780695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780695 prefixEnd_7780695 := by exact prefixLift 7780695
  have htrace : WordTrace (prefixWord ++ tailWord_7780695) baseStart_7780695 baseEnd_7780695 := by
    simpa [prefixWord, tailWord_7780695, baseEnd_7780695] using wordTrace_append hprefix tailTrace_7780695
  have hstable : (prefixWord ++ tailWord_7780695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780695).length < 2 ^ (prefixWord ++ tailWord_7780695).sum := by decide
  have hdescent : baseEnd_7780695 < baseStart_7780695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780722 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_7780722 : Nat := 118140960795 + 7780722 * 2 ^ 59
def prefixEnd_7780722 : Nat := 4983230072969 + 3 ^ 40 * 7780722 * 2
def baseEnd_7780722 : Nat := 3995250225012212123092117

theorem tailTrace_7780722 : CollatzResearch.WordTrace tailWord_7780722 prefixEnd_7780722 3995250225012212123092117 := by
  unfold tailWord_7780722
  simp only [CollatzResearch.WordTrace]
  refine ⟨70946561329445127592058105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189190830211853673578821613 70946561329445127592058105)
  ·
    refine ⟨53209920997083845694043579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70946561329445127592058105 53209920997083845694043579)
    ·
      refine ⟨79814881495625768541065369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53209920997083845694043579 79814881495625768541065369)
      ·
        refine ⟨59861161121719326405799027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79814881495625768541065369 59861161121719326405799027)
        ·
          refine ⟨89791741682578989608698541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59861161121719326405799027 89791741682578989608698541)
          ·
            refine ⟨33671903130967121103261953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89791741682578989608698541 33671903130967121103261953)
            ·
              refine ⟨25253927348225340827446465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33671903130967121103261953 25253927348225340827446465)
              ·
                refine ⟨18940445511169005620584849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25253927348225340827446465 18940445511169005620584849)
                ·
                  refine ⟨14205334133376754215438637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18940445511169005620584849 14205334133376754215438637)
                  ·
                    refine ⟨5327000300016282830789489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14205334133376754215438637 5327000300016282830789489)
                    ·
                      refine ⟨3995250225012212123092117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327000300016282830789489 3995250225012212123092117)
                      ·
                        rfl

theorem cell23_7780722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_7780722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780722 prefixEnd_7780722 := by exact prefixLift 7780722
  have htrace : WordTrace (prefixWord ++ tailWord_7780722) baseStart_7780722 baseEnd_7780722 := by
    simpa [prefixWord, tailWord_7780722, baseEnd_7780722] using wordTrace_append hprefix tailTrace_7780722
  have hstable : (prefixWord ++ tailWord_7780722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780722).length < 2 ^ (prefixWord ++ tailWord_7780722).sum := by decide
  have hdescent : baseEnd_7780722 < baseStart_7780722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780745 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 1, 6]
def baseStart_7780745 : Nat := 118140960795 + 7780745 * 2 ^ 59
def prefixEnd_7780745 : Nat := 4983230072969 + 3 ^ 40 * 7780745 * 2
def baseEnd_7780745 : Nat := 1331754011689088511034837

theorem tailTrace_7780745 : CollatzResearch.WordTrace tailWord_7780745 prefixEnd_7780745 1331754011689088511034837 := by
  unfold tailWord_7780745
  simp only [CollatzResearch.WordTrace]
  refine ⟨283787084196697185296319689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189191389464464790197546459 283787084196697185296319689)
  ·
    refine ⟨212840313147522888972239767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283787084196697185296319689 212840313147522888972239767)
    ·
      refine ⟨319260469721284333458359651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212840313147522888972239767 319260469721284333458359651)
      ·
        refine ⟨478890704581926500187539477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319260469721284333458359651 478890704581926500187539477)
        ·
          refine ⟨22448001777277804696290913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 478890704581926500187539477 22448001777277804696290913)
          ·
            refine ⟨16836001332958353522218185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22448001777277804696290913 16836001332958353522218185)
            ·
              refine ⟨12627000999718765141663639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16836001332958353522218185 12627000999718765141663639)
              ·
                refine ⟨18940501499578147712495459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12627000999718765141663639 18940501499578147712495459)
                ·
                  refine ⟨28410752249367221568743189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18940501499578147712495459 28410752249367221568743189)
                  ·
                    refine ⟨1331754011689088511034837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28410752249367221568743189 1331754011689088511034837)
                    ·
                      rfl

theorem cell23_7780745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_7780745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780745 prefixEnd_7780745 := by exact prefixLift 7780745
  have htrace : WordTrace (prefixWord ++ tailWord_7780745) baseStart_7780745 baseEnd_7780745 := by
    simpa [prefixWord, tailWord_7780745, baseEnd_7780745] using wordTrace_append hprefix tailTrace_7780745
  have hstable : (prefixWord ++ tailWord_7780745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780745).length < 2 ^ (prefixWord ++ tailWord_7780745).sum := by decide
  have hdescent : baseEnd_7780745 < baseStart_7780745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780756 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_7780756 : Nat := 118140960795 + 7780756 * 2 ^ 59
def prefixEnd_7780756 : Nat := 4983230072969 + 3 ^ 40 * 7780756 * 2
def baseEnd_7780756 : Nat := 3995267683354464990066961

theorem tailTrace_7780756 : CollatzResearch.WordTrace tailWord_7780756 prefixEnd_7780756 3995267683354464990066961 := by
  unfold tailWord_7780756
  simp only [CollatzResearch.WordTrace]
  refine ⟨141893742699828667087485061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189191656933104889449980081 141893742699828667087485061)
  ·
    refine ⟨26605076756217875078903449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141893742699828667087485061 26605076756217875078903449)
    ·
      refine ⟨19953807567163406309177587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26605076756217875078903449 19953807567163406309177587)
      ·
        refine ⟨29930711350745109463766381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19953807567163406309177587 29930711350745109463766381)
        ·
          refine ⟨11224016756529416048912393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29930711350745109463766381 11224016756529416048912393)
          ·
            refine ⟨8418012567397062036684295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11224016756529416048912393 8418012567397062036684295)
            ·
              refine ⟨12627018851095593055026443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8418012567397062036684295 12627018851095593055026443)
              ·
                refine ⟨18940528276643389582539665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12627018851095593055026443 18940528276643389582539665)
                ·
                  refine ⟨14205396207482542186904749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18940528276643389582539665 14205396207482542186904749)
                  ·
                    refine ⟨5327023577805953320089281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14205396207482542186904749 5327023577805953320089281)
                    ·
                      refine ⟨3995267683354464990066961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327023577805953320089281 3995267683354464990066961)
                      ·
                        rfl

theorem cell23_7780756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_7780756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780756 prefixEnd_7780756 := by exact prefixLift 7780756
  have htrace : WordTrace (prefixWord ++ tailWord_7780756) baseStart_7780756 baseEnd_7780756 := by
    simpa [prefixWord, tailWord_7780756, baseEnd_7780756] using wordTrace_append hprefix tailTrace_7780756
  have hstable : (prefixWord ++ tailWord_7780756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780756).length < 2 ^ (prefixWord ++ tailWord_7780756).sum := by decide
  have hdescent : baseEnd_7780756 < baseStart_7780756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780766 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7780766 : Nat := 118140960795 + 7780766 * 2 ^ 59
def prefixEnd_7780766 : Nat := 4983230072969 + 3 ^ 40 * 7780766 * 2
def baseEnd_7780766 : Nat := 1331757606053669983647305

theorem tailTrace_7780766 : CollatzResearch.WordTrace tailWord_7780766 prefixEnd_7780766 1331757606053669983647305 := by
  unfold tailWord_7780766
  simp only [CollatzResearch.WordTrace]
  refine ⟨35473481266202638235354269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189191900086414070588556101 35473481266202638235354269)
  ·
    refine ⟨13302555474825989338257851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35473481266202638235354269 13302555474825989338257851)
    ·
      refine ⟨19953833212238984007386777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13302555474825989338257851 19953833212238984007386777)
      ·
        refine ⟨14965374909179238005540083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19953833212238984007386777 14965374909179238005540083)
        ·
          refine ⟨22448062363768857008310125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14965374909179238005540083 22448062363768857008310125)
          ·
            refine ⟨8418023386413321378116297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22448062363768857008310125 8418023386413321378116297)
            ·
              refine ⟨6313517539809991033587223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8418023386413321378116297 6313517539809991033587223)
              ·
                refine ⟨9470276309714986550380835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6313517539809991033587223 9470276309714986550380835)
                ·
                  refine ⟨14205414464572479825571253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9470276309714986550380835 14205414464572479825571253)
                  ·
                    refine ⟨1331757606053669983647305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14205414464572479825571253 1331757606053669983647305)
                    ·
                      rfl

theorem cell23_7780766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7780766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780766 prefixEnd_7780766 := by exact prefixLift 7780766
  have htrace : WordTrace (prefixWord ++ tailWord_7780766) baseStart_7780766 baseEnd_7780766 := by
    simpa [prefixWord, tailWord_7780766, baseEnd_7780766] using wordTrace_append hprefix tailTrace_7780766
  have hstable : (prefixWord ++ tailWord_7780766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780766).length < 2 ^ (prefixWord ++ tailWord_7780766).sum := by decide
  have hdescent : baseEnd_7780766 < baseStart_7780766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780769 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7780769 : Nat := 118140960795 + 7780769 * 2 ^ 59
def prefixEnd_7780769 : Nat := 4983230072969 + 3 ^ 40 * 7780769 * 2
def baseEnd_7780769 : Nat := 3995274358602973439204401

theorem tailTrace_7780769 : CollatzResearch.WordTrace tailWord_7780769 prefixEnd_7780769 3995274358602973439204401 := by
  unfold tailWord_7780769
  simp only [CollatzResearch.WordTrace]
  refine ⟨283787959548610237395193361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189191973032406824930128907 283787959548610237395193361)
  ·
    refine ⟨212840969661457678046395021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283787959548610237395193361 212840969661457678046395021)
    ·
      refine ⟨79815363623046629267398133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212840969661457678046395021 79815363623046629267398133)
      ·
        refine ⟨7482690339660621493818575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79815363623046629267398133 7482690339660621493818575)
        ·
          refine ⟨11224035509490932240727863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7482690339660621493818575 11224035509490932240727863)
          ·
            refine ⟨16836053264236398361091795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11224035509490932240727863 16836053264236398361091795)
            ·
              refine ⟨25254079896354597541637693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16836053264236398361091795 25254079896354597541637693)
              ·
                refine ⟨9470279961132974078114135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25254079896354597541637693 9470279961132974078114135)
                ·
                  refine ⟨14205419941699461117171203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9470279961132974078114135 14205419941699461117171203)
                  ·
                    refine ⟨21308129912549191675756805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14205419941699461117171203 21308129912549191675756805)
                    ·
                      refine ⟨3995274358602973439204401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21308129912549191675756805 3995274358602973439204401)
                      ·
                        rfl

theorem cell23_7780769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7780769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780769 prefixEnd_7780769 := by exact prefixLift 7780769
  have htrace : WordTrace (prefixWord ++ tailWord_7780769) baseStart_7780769 baseEnd_7780769 := by
    simpa [prefixWord, tailWord_7780769, baseEnd_7780769] using wordTrace_append hprefix tailTrace_7780769
  have hstable : (prefixWord ++ tailWord_7780769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780769).length < 2 ^ (prefixWord ++ tailWord_7780769).sum := by decide
  have hdescent : baseEnd_7780769 < baseStart_7780769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780829 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_7780829 : Nat := 118140960795 + 7780829 * 2 ^ 59
def prefixEnd_7780829 : Nat := 4983230072969 + 3 ^ 40 * 7780829 * 2
def baseEnd_7780829 : Nat := 3995305167442243204454125

theorem tailTrace_7780829 : CollatzResearch.WordTrace tailWord_7780829 prefixEnd_7780829 3995305167442243204454125 := by
  unfold tailWord_7780829
  simp only [CollatzResearch.WordTrace]
  refine ⟨283790147928392867642377541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189193431952261911761585027 283790147928392867642377541)
  ·
    refine ⟨53210652736573662682945789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283790147928392867642377541 53210652736573662682945789)
    ·
      refine ⟨19953994776215123506104671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53210652736573662682945789 19953994776215123506104671)
      ·
        refine ⟨29930992164322685259157007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19953994776215123506104671 29930992164322685259157007)
        ·
          refine ⟨44896488246484027888735511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29930992164322685259157007 44896488246484027888735511)
          ·
            refine ⟨67344732369726041833103267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44896488246484027888735511 67344732369726041833103267)
            ·
              refine ⟨101017098554589062749654901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67344732369726041833103267 101017098554589062749654901)
              ·
                refine ⟨9470352989492724632780147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101017098554589062749654901 9470352989492724632780147)
                ·
                  refine ⟨14205529484239086949170221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9470352989492724632780147 14205529484239086949170221)
                  ·
                    refine ⟨5327073556589657605938833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14205529484239086949170221 5327073556589657605938833)
                    ·
                      refine ⟨3995305167442243204454125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327073556589657605938833 3995305167442243204454125)
                      ·
                        rfl

theorem cell23_7780829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_7780829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780829 prefixEnd_7780829 := by exact prefixLift 7780829
  have htrace : WordTrace (prefixWord ++ tailWord_7780829) baseStart_7780829 baseEnd_7780829 := by
    simpa [prefixWord, tailWord_7780829, baseEnd_7780829] using wordTrace_append hprefix tailTrace_7780829
  have hstable : (prefixWord ++ tailWord_7780829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780829).length < 2 ^ (prefixWord ++ tailWord_7780829).sum := by decide
  have hdescent : baseEnd_7780829 < baseStart_7780829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780899 : List Nat := [1, 1, 1, 4, 4, 1, 4, 2, 5]
def baseStart_7780899 : Nat := 118140960795 + 7780899 * 2 ^ 59
def prefixEnd_7780899 : Nat := 4983230072969 + 3 ^ 40 * 7780899 * 2
def baseEnd_7780899 : Nat := 443926790120895325619867

theorem tailTrace_7780899 : CollatzResearch.WordTrace tailWord_7780899 prefixEnd_7780899 443926790120895325619867 := by
  unfold tailWord_7780899
  simp only [CollatzResearch.WordTrace]
  refine ⟨283792701038139269597425751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189195134025426179731617167 283792701038139269597425751)
  ·
    refine ⟨425689051557208904396138627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283792701038139269597425751 425689051557208904396138627)
    ·
      refine ⟨638533577335813356594207941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425689051557208904396138627 638533577335813356594207941)
      ·
        refine ⟨119725045750465004361413989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 638533577335813356594207941 119725045750465004361413989)
        ·
          refine ⟨22448446078212188317765123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119725045750465004361413989 22448446078212188317765123)
          ·
            refine ⟨33672669117318282476647685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22448446078212188317765123 33672669117318282476647685)
            ·
              refine ⟨6313625459497177964371441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33672669117318282476647685 6313625459497177964371441)
              ·
                refine ⟨4735219094622883473278581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6313625459497177964371441 4735219094622883473278581)
                ·
                  refine ⟨443926790120895325619867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4735219094622883473278581 443926790120895325619867)
                  ·
                    rfl

theorem cell23_7780899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 5].length) (baseStart_7780899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780899 prefixEnd_7780899 := by exact prefixLift 7780899
  have htrace : WordTrace (prefixWord ++ tailWord_7780899) baseStart_7780899 baseEnd_7780899 := by
    simpa [prefixWord, tailWord_7780899, baseEnd_7780899] using wordTrace_append hprefix tailTrace_7780899
  have hstable : (prefixWord ++ tailWord_7780899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780899).length < 2 ^ (prefixWord ++ tailWord_7780899).sum := by decide
  have hdescent : baseEnd_7780899 < baseStart_7780899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780915 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 4]
def baseStart_7780915 : Nat := 118140960795 + 7780915 * 2 ^ 59
def prefixEnd_7780915 : Nat := 4983230072969 + 3 ^ 40 * 7780915 * 2
def baseEnd_7780915 : Nat := 3995349326778529867978729

theorem tailTrace_7780915 : CollatzResearch.WordTrace tailWord_7780915 prefixEnd_7780915 3995349326778529867978729 := by
  unfold tailWord_7780915
  simp only [CollatzResearch.WordTrace]
  refine ⟨283793284606081304330008199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189195523070720869553338799 283793284606081304330008199)
  ·
    refine ⟨425689926909121956495012299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283793284606081304330008199 425689926909121956495012299)
    ·
      refine ⟨638534890363682934742518449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425689926909121956495012299 638534890363682934742518449)
      ·
        refine ⟨478901167772762201056888837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638534890363682934742518449 478901167772762201056888837)
        ·
          refine ⟨89793968957392912698166657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 478901167772762201056888837 89793968957392912698166657)
          ·
            refine ⟨67345476718044684523624993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89793968957392912698166657 67345476718044684523624993)
            ·
              refine ⟨50509107538533513392718745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67345476718044684523624993 50509107538533513392718745)
              ·
                refine ⟨37881830653900135044539059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50509107538533513392718745 37881830653900135044539059)
                ·
                  refine ⟨56822745980850202566808589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37881830653900135044539059 56822745980850202566808589)
                  ·
                    refine ⟨21308529742818825962553221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56822745980850202566808589 21308529742818825962553221)
                    ·
                      refine ⟨3995349326778529867978729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21308529742818825962553221 3995349326778529867978729)
                      ·
                        rfl

theorem cell23_7780915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_7780915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780915 prefixEnd_7780915 := by exact prefixLift 7780915
  have htrace : WordTrace (prefixWord ++ tailWord_7780915) baseStart_7780915 baseEnd_7780915 := by
    simpa [prefixWord, tailWord_7780915, baseEnd_7780915] using wordTrace_append hprefix tailTrace_7780915
  have hstable : (prefixWord ++ tailWord_7780915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780915).length < 2 ^ (prefixWord ++ tailWord_7780915).sum := by decide
  have hdescent : baseEnd_7780915 < baseStart_7780915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780929 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7780929 : Nat := 118140960795 + 7780929 * 2 ^ 59
def prefixEnd_7780929 : Nat := 4983230072969 + 3 ^ 40 * 7780929 * 2
def baseEnd_7780929 : Nat := 1331785505169230937734555

theorem tailTrace_7780929 : CollatzResearch.WordTrace tailWord_7780929 prefixEnd_7780929 1331785505169230937734555 := by
  unfold tailWord_7780929
  simp only [CollatzResearch.WordTrace]
  refine ⟨283793795228030584721017841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189195863485353723147345227 283793795228030584721017841)
  ·
    refine ⟨212845346421022938540763381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283793795228030584721017841 212845346421022938540763381)
    ·
      refine ⟨19954251226970900488196567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212845346421022938540763381 19954251226970900488196567)
      ·
        refine ⟨29931376840456350732294851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19954251226970900488196567 29931376840456350732294851)
        ·
          refine ⟨44897065260684526098442277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29931376840456350732294851 44897065260684526098442277)
          ·
            refine ⟨8418199736378348643457927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44897065260684526098442277 8418199736378348643457927)
            ·
              refine ⟨12627299604567522965186891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8418199736378348643457927 12627299604567522965186891)
              ·
                refine ⟨18940949406851284447780337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12627299604567522965186891 18940949406851284447780337)
                ·
                  refine ⟨14205712055138463335835253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18940949406851284447780337 14205712055138463335835253)
                  ·
                    refine ⟨1331785505169230937734555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14205712055138463335835253 1331785505169230937734555)
                    ·
                      rfl

theorem cell23_7780929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7780929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780929 prefixEnd_7780929 := by exact prefixLift 7780929
  have htrace : WordTrace (prefixWord ++ tailWord_7780929) baseStart_7780929 baseEnd_7780929 := by
    simpa [prefixWord, tailWord_7780929, baseEnd_7780929] using wordTrace_append hprefix tailTrace_7780929
  have hstable : (prefixWord ++ tailWord_7780929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780929).length < 2 ^ (prefixWord ++ tailWord_7780929).sum := by decide
  have hdescent : baseEnd_7780929 < baseStart_7780929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780945 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_7780945 : Nat := 118140960795 + 7780945 * 2 ^ 59
def prefixEnd_7780945 : Nat := 4983230072969 + 3 ^ 40 * 7780945 * 2
def baseEnd_7780945 : Nat := 3995364731198164750603591

theorem tailTrace_7780945 : CollatzResearch.WordTrace tailWord_7780945 prefixEnd_7780945 3995364731198164750603591 := by
  unfold tailWord_7780945
  simp only [CollatzResearch.WordTrace]
  refine ⟨283794378795972619453600289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189196252530648412969066859 283794378795972619453600289)
  ·
    refine ⟨212845784096979464590200217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283794378795972619453600289 212845784096979464590200217)
    ·
      refine ⟨159634338072734598442650163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212845784096979464590200217 159634338072734598442650163)
      ·
        refine ⟨239451507109101897663975245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159634338072734598442650163 239451507109101897663975245)
        ·
          refine ⟨89794315165913211623990717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239451507109101897663975245 89794315165913211623990717)
          ·
            refine ⟨33672868187217454358996519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89794315165913211623990717 33672868187217454358996519)
            ·
              refine ⟨50509302280826181538494779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33672868187217454358996519 50509302280826181538494779)
              ·
                refine ⟨75763953421239272307742169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50509302280826181538494779 75763953421239272307742169)
                ·
                  refine ⟨56822965065929454230806627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75763953421239272307742169 56822965065929454230806627)
                  ·
                    refine ⟨85234447598894181346209941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56822965065929454230806627 85234447598894181346209941)
                    ·
                      refine ⟨3995364731198164750603591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85234447598894181346209941 3995364731198164750603591)
                      ·
                        rfl

theorem cell23_7780945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_7780945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780945 prefixEnd_7780945 := by exact prefixLift 7780945
  have htrace : WordTrace (prefixWord ++ tailWord_7780945) baseStart_7780945 baseEnd_7780945 := by
    simpa [prefixWord, tailWord_7780945, baseEnd_7780945] using wordTrace_append hprefix tailTrace_7780945
  have hstable : (prefixWord ++ tailWord_7780945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780945).length < 2 ^ (prefixWord ++ tailWord_7780945).sum := by decide
  have hdescent : baseEnd_7780945 < baseStart_7780945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7780952 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_7780952 : Nat := 118140960795 + 7780952 * 2 ^ 59
def prefixEnd_7780952 : Nat := 4983230072969 + 3 ^ 40 * 7780952 * 2
def baseEnd_7780952 : Nat := 3995368325562746223216059

theorem tailTrace_7780952 : CollatzResearch.WordTrace tailWord_7780952 prefixEnd_7780952 3995368325562746223216059 := by
  unfold tailWord_7780952
  simp only [CollatzResearch.WordTrace]
  refine ⟨141897317053473629824552555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189196422737964839766070073 141897317053473629824552555)
  ·
    refine ⟨212845975580210444736828833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141897317053473629824552555 212845975580210444736828833)
    ·
      refine ⟨159634481685157833552621625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212845975580210444736828833 159634481685157833552621625)
      ·
        refine ⟨119725861263868375164466219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159634481685157833552621625 119725861263868375164466219)
        ·
          refine ⟨179588791895802562746699329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119725861263868375164466219 179588791895802562746699329)
          ·
            refine ⟨134691593921851922060024497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179588791895802562746699329 134691593921851922060024497)
            ·
              refine ⟨101018695441388941545018373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134691593921851922060024497 101018695441388941545018373)
              ·
                refine ⟨18941005395260426539690945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101018695441388941545018373 18941005395260426539690945)
                ·
                  refine ⟨14205754046445319904768209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18941005395260426539690945 14205754046445319904768209)
                  ·
                    refine ⟨10654315534833989928576157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14205754046445319904768209 10654315534833989928576157)
                    ·
                      refine ⟨3995368325562746223216059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10654315534833989928576157 3995368325562746223216059)
                      ·
                        rfl

theorem cell23_7780952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_7780952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7780952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7780952 prefixEnd_7780952 := by exact prefixLift 7780952
  have htrace : WordTrace (prefixWord ++ tailWord_7780952) baseStart_7780952 baseEnd_7780952 := by
    simpa [prefixWord, tailWord_7780952, baseEnd_7780952] using wordTrace_append hprefix tailTrace_7780952
  have hstable : (prefixWord ++ tailWord_7780952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7780952).length < 2 ^ (prefixWord ++ tailWord_7780952).sum := by decide
  have hdescent : baseEnd_7780952 < baseStart_7780952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7780952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781039 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 4]
def baseStart_7781039 : Nat := 118140960795 + 7781039 * 2 ^ 59
def prefixEnd_7781039 : Nat := 4983230072969 + 3 ^ 40 * 7781039 * 2
def baseEnd_7781039 : Nat := 3995412998379687382828159

theorem tailTrace_7781039 : CollatzResearch.WordTrace tailWord_7781039 prefixEnd_7781039 3995412998379687382828159 := by
  unfold tailWord_7781039
  simp only [CollatzResearch.WordTrace]
  refine ⟨283797807257632073507522171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189198538171754715671681447 283797807257632073507522171)
  ·
    refine ⟨425696710886448110261283257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283797807257632073507522171 425696710886448110261283257)
    ·
      refine ⟨319272533164836082695962443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425696710886448110261283257 319272533164836082695962443)
      ·
        refine ⟨478908799747254124043943665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319272533164836082695962443 478908799747254124043943665)
        ·
          refine ⟨359181599810440593032957749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478908799747254124043943665 359181599810440593032957749)
          ·
            refine ⟨33673274982228805596839789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359181599810440593032957749 33673274982228805596839789)
            ·
              refine ⟨12627478118335802098814921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33673274982228805596839789 12627478118335802098814921)
              ·
                refine ⟨9470608588751851574111191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12627478118335802098814921 9470608588751851574111191)
                ·
                  refine ⟨14205912883127777361166787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9470608588751851574111191 14205912883127777361166787)
                  ·
                    refine ⟨21308869324691666041750181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14205912883127777361166787 21308869324691666041750181)
                    ·
                      refine ⟨3995412998379687382828159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21308869324691666041750181 3995412998379687382828159)
                      ·
                        rfl

theorem cell23_7781039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 1, 4].length) (baseStart_7781039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781039 prefixEnd_7781039 := by exact prefixLift 7781039
  have htrace : WordTrace (prefixWord ++ tailWord_7781039) baseStart_7781039 baseEnd_7781039 := by
    simpa [prefixWord, tailWord_7781039, baseEnd_7781039] using wordTrace_append hprefix tailTrace_7781039
  have hstable : (prefixWord ++ tailWord_7781039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781039).length < 2 ^ (prefixWord ++ tailWord_7781039).sum := by decide
  have hdescent : baseEnd_7781039 < baseStart_7781039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781056 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 1, 1, 4]
def baseStart_7781056 : Nat := 118140960795 + 7781056 * 2 ^ 59
def prefixEnd_7781056 : Nat := 4983230072969 + 3 ^ 40 * 7781056 * 2
def baseEnd_7781056 : Nat := 3995421727550813816315581

theorem tailTrace_7781056 : CollatzResearch.WordTrace tailWord_7781056 prefixEnd_7781056 3995421727550813816315581 := by
  unfold tailWord_7781056
  simp only [CollatzResearch.WordTrace]
  refine ⟨141899213649285242705445511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189198951532380323607260681 141899213649285242705445511)
  ·
    refine ⟨212848820473927864058168267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141899213649285242705445511 212848820473927864058168267)
    ·
      refine ⟨319273230710891796087252401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212848820473927864058168267 319273230710891796087252401)
      ·
        refine ⟨239454923033168847065439301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319273230710891796087252401 239454923033168847065439301)
        ·
          refine ⟨44897798068719158824769869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239454923033168847065439301 44897798068719158824769869)
          ·
            refine ⟨16836674275769684559288701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44897798068719158824769869 16836674275769684559288701)
            ·
              refine ⟨6313752853413631709733263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16836674275769684559288701 6313752853413631709733263)
              ·
                refine ⟨9470629280120447564599895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6313752853413631709733263 9470629280120447564599895)
                ·
                  refine ⟨14205943920180671346899843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9470629280120447564599895 14205943920180671346899843)
                  ·
                    refine ⟨21308915880271007020349765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14205943920180671346899843 21308915880271007020349765)
                    ·
                      refine ⟨3995421727550813816315581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21308915880271007020349765 3995421727550813816315581)
                      ·
                        rfl

theorem cell23_7781056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_7781056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781056 prefixEnd_7781056 := by exact prefixLift 7781056
  have htrace : WordTrace (prefixWord ++ tailWord_7781056) baseStart_7781056 baseEnd_7781056 := by
    simpa [prefixWord, tailWord_7781056, baseEnd_7781056] using wordTrace_append hprefix tailTrace_7781056
  have hstable : (prefixWord ++ tailWord_7781056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781056).length < 2 ^ (prefixWord ++ tailWord_7781056).sum := by decide
  have hdescent : baseEnd_7781056 < baseStart_7781056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781065 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_7781065 : Nat := 118140960795 + 7781065 * 2 ^ 59
def prefixEnd_7781065 : Nat := 4983230072969 + 3 ^ 40 * 7781065 * 2
def baseEnd_7781065 : Nat := 3995426348876704281103039

theorem tailTrace_7781065 : CollatzResearch.WordTrace tailWord_7781065 prefixEnd_7781065 3995426348876704281103039 := by
  unfold tailWord_7781065
  simp only [CollatzResearch.WordTrace]
  refine ⟨283798755555537879947968649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189199170370358586631979099 283798755555537879947968649)
  ·
    refine ⟨212849066666653409960976487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283798755555537879947968649 212849066666653409960976487)
    ·
      refine ⟨319273599999980114941464731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212849066666653409960976487 319273599999980114941464731)
      ·
        refine ⟨478910399999970172412197097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319273599999980114941464731 478910399999970172412197097)
        ·
          refine ⟨359182799999977629309147823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478910399999970172412197097 359182799999977629309147823)
          ·
            refine ⟨538774199999966443963721735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359182799999977629309147823 538774199999966443963721735)
            ·
              refine ⟨808161299999949665945582603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538774199999966443963721735 808161299999949665945582603)
              ·
                refine ⟨1212241949999924498918373905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808161299999949665945582603 1212241949999924498918373905)
                ·
                  refine ⟨909181462499943374188780429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1212241949999924498918373905 909181462499943374188780429)
                  ·
                    refine ⟨340943048437478765320792661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909181462499943374188780429 340943048437478765320792661)
                    ·
                      refine ⟨3995426348876704281103039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 340943048437478765320792661 3995426348876704281103039)
                      ·
                        rfl

theorem cell23_7781065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_7781065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781065 prefixEnd_7781065 := by exact prefixLift 7781065
  have htrace : WordTrace (prefixWord ++ tailWord_7781065) baseStart_7781065 baseEnd_7781065 := by
    simpa [prefixWord, tailWord_7781065, baseEnd_7781065] using wordTrace_append hprefix tailTrace_7781065
  have hstable : (prefixWord ++ tailWord_7781065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781065).length < 2 ^ (prefixWord ++ tailWord_7781065).sum := by decide
  have hdescent : baseEnd_7781065 < baseStart_7781065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781066 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_7781066 : Nat := 118140960795 + 7781066 * 2 ^ 59
def prefixEnd_7781066 : Nat := 4983230072969 + 3 ^ 40 * 7781066 * 2
def baseEnd_7781066 : Nat := 1331808954119119592396845

theorem tailTrace_7781066 : CollatzResearch.WordTrace tailWord_7781066 prefixEnd_7781066 1331808954119119592396845 := by
  unfold tailWord_7781066
  simp only [CollatzResearch.WordTrace]
  refine ⟨70949698007133564279688763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189199194685689504745836701 70949698007133564279688763)
  ·
    refine ⟨106424547010700346419533145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70949698007133564279688763 106424547010700346419533145)
    ·
      refine ⟨79818410258025259814649859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106424547010700346419533145 79818410258025259814649859)
      ·
        refine ⟨119727615387037889721974789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79818410258025259814649859 119727615387037889721974789)
        ·
          refine ⟨22448927885069604322870273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119727615387037889721974789 22448927885069604322870273)
          ·
            refine ⟨16836695913802203242152705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22448927885069604322870273 16836695913802203242152705)
            ·
              refine ⟨12627521935351652431614529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16836695913802203242152705 12627521935351652431614529)
              ·
                refine ⟨9470641451513739323710897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12627521935351652431614529 9470641451513739323710897)
                ·
                  refine ⟨7102981088635304492783173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9470641451513739323710897 7102981088635304492783173)
                  ·
                    refine ⟨1331808954119119592396845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7102981088635304492783173 1331808954119119592396845)
                    ·
                      rfl

theorem cell23_7781066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_7781066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781066 prefixEnd_7781066 := by exact prefixLift 7781066
  have htrace : WordTrace (prefixWord ++ tailWord_7781066) baseStart_7781066 baseEnd_7781066 := by
    simpa [prefixWord, tailWord_7781066, baseEnd_7781066] using wordTrace_append hprefix tailTrace_7781066
  have hstable : (prefixWord ++ tailWord_7781066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781066).length < 2 ^ (prefixWord ++ tailWord_7781066).sum := by decide
  have hdescent : baseEnd_7781066 < baseStart_7781066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781073 : List Nat := [1, 2, 2, 1, 2, 3, 3, 4, 1, 2, 2]
def baseStart_7781073 : Nat := 118140960795 + 7781073 * 2 ^ 59
def prefixEnd_7781073 : Nat := 4983230072969 + 3 ^ 40 * 7781073 * 2
def baseEnd_7781073 : Nat := 3995430456721940249803003

theorem tailTrace_7781073 : CollatzResearch.WordTrace tailWord_7781073 prefixEnd_7781073 3995430456721940249803003 := by
  unfold tailWord_7781073
  simp only [CollatzResearch.WordTrace]
  refine ⟨283799047339508897314259873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189199364893005931542839915 283799047339508897314259873)
  ·
    refine ⟨212849285504631672985694905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283799047339508897314259873 212849285504631672985694905)
    ·
      refine ⟨159636964128473754739271179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212849285504631672985694905 159636964128473754739271179)
      ·
        refine ⟨239455446192710632108906769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159636964128473754739271179 239455446192710632108906769)
        ·
          refine ⟨179591584644532974081680077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239455446192710632108906769 179591584644532974081680077)
          ·
            refine ⟨67346844241699865280630029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179591584644532974081680077 67346844241699865280630029)
            ·
              refine ⟨25255066590637449480236261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67346844241699865280630029 25255066590637449480236261)
              ·
                refine ⟨4735324985744521777544299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25255066590637449480236261 4735324985744521777544299)
                ·
                  refine ⟨7102987478616782666316449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735324985744521777544299 7102987478616782666316449)
                  ·
                    refine ⟨5327240608962586999737337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7102987478616782666316449 5327240608962586999737337)
                    ·
                      refine ⟨3995430456721940249803003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327240608962586999737337 3995430456721940249803003)
                      ·
                        rfl

theorem cell23_7781073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_7781073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781073 prefixEnd_7781073 := by exact prefixLift 7781073
  have htrace : WordTrace (prefixWord ++ tailWord_7781073) baseStart_7781073 baseEnd_7781073 := by
    simpa [prefixWord, tailWord_7781073, baseEnd_7781073] using wordTrace_append hprefix tailTrace_7781073
  have hstable : (prefixWord ++ tailWord_7781073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781073).length < 2 ^ (prefixWord ++ tailWord_7781073).sum := by decide
  have hdescent : baseEnd_7781073 < baseStart_7781073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781089 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_7781089 : Nat := 118140960795 + 7781089 * 2 ^ 59
def prefixEnd_7781089 : Nat := 4983230072969 + 3 ^ 40 * 7781089 * 2
def baseEnd_7781089 : Nat := 3995438672412412187202929

theorem tailTrace_7781089 : CollatzResearch.WordTrace tailWord_7781089 prefixEnd_7781089 3995438672412412187202929 := by
  unfold tailWord_7781089
  simp only [CollatzResearch.WordTrace]
  refine ⟨283799630907450932046842321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189199753938300621364561547 283799630907450932046842321)
  ·
    refine ⟨212849723180588199035131741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283799630907450932046842321 212849723180588199035131741)
    ·
      refine ⟨79818646192720574638174403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212849723180588199035131741 79818646192720574638174403)
      ·
        refine ⟨119727969289080861957261605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79818646192720574638174403 119727969289080861957261605)
        ·
          refine ⟨22448994241702661616986551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119727969289080861957261605 22448994241702661616986551)
          ·
            refine ⟨33673491362553992425479827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22448994241702661616986551 33673491362553992425479827)
            ·
              refine ⟨50510237043830988638219741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33673491362553992425479827 50510237043830988638219741)
              ·
                refine ⟨18941338891436620739332403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50510237043830988638219741 18941338891436620739332403)
                ·
                  refine ⟨28412008337154931108998605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18941338891436620739332403 28412008337154931108998605)
                  ·
                    refine ⟨10654503126433099165874477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28412008337154931108998605 10654503126433099165874477)
                    ·
                      refine ⟨3995438672412412187202929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10654503126433099165874477 3995438672412412187202929)
                      ·
                        rfl

theorem cell23_7781089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_7781089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781089 prefixEnd_7781089 := by exact prefixLift 7781089
  have htrace : WordTrace (prefixWord ++ tailWord_7781089) baseStart_7781089 baseEnd_7781089 := by
    simpa [prefixWord, tailWord_7781089, baseEnd_7781089] using wordTrace_append hprefix tailTrace_7781089
  have hstable : (prefixWord ++ tailWord_7781089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781089).length < 2 ^ (prefixWord ++ tailWord_7781089).sum := by decide
  have hdescent : baseEnd_7781089 < baseStart_7781089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781129 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 3, 4, 2]
def baseStart_7781129 : Nat := 118140960795 + 7781129 * 2 ^ 59
def prefixEnd_7781129 : Nat := 4983230072969 + 3 ^ 40 * 7781129 * 2
def baseEnd_7781129 : Nat := 3995459211638592030702745

theorem tailTrace_7781129 : CollatzResearch.WordTrace tailWord_7781129 prefixEnd_7781129 3995459211638592030702745 := by
  unfold tailWord_7781129
  simp only [CollatzResearch.WordTrace]
  refine ⟨283801089827306018878298441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189200726551537345918865627 283801089827306018878298441)
  ·
    refine ⟨212850817370479514158723831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283801089827306018878298441 212850817370479514158723831)
    ·
      refine ⟨319276226055719271238085747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212850817370479514158723831 319276226055719271238085747)
      ·
        refine ⟨478914339083578906857128621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319276226055719271238085747 478914339083578906857128621)
        ·
          refine ⟨179592877156342090071423233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478914339083578906857128621 179592877156342090071423233)
          ·
            refine ⟨134694657867256567553567425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179592877156342090071423233 134694657867256567553567425)
            ·
              refine ⟨101020993400442425665175569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134694657867256567553567425 101020993400442425665175569)
              ·
                refine ⟨75765745050331819248881677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101020993400442425665175569 75765745050331819248881677)
                ·
                  refine ⟨28412154393874432218330629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75765745050331819248881677 28412154393874432218330629)
                  ·
                    refine ⟨5327278948851456040936993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28412154393874432218330629 5327278948851456040936993)
                    ·
                      refine ⟨3995459211638592030702745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327278948851456040936993 3995459211638592030702745)
                      ·
                        rfl

theorem cell23_7781129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 4, 2].length) (baseStart_7781129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781129 prefixEnd_7781129 := by exact prefixLift 7781129
  have htrace : WordTrace (prefixWord ++ tailWord_7781129) baseStart_7781129 baseEnd_7781129 := by
    simpa [prefixWord, tailWord_7781129, baseEnd_7781129] using wordTrace_append hprefix tailTrace_7781129
  have hstable : (prefixWord ++ tailWord_7781129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781129).length < 2 ^ (prefixWord ++ tailWord_7781129).sum := by decide
  have hdescent : baseEnd_7781129 < baseStart_7781129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781132 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_7781132 : Nat := 118140960795 + 7781132 * 2 ^ 59
def prefixEnd_7781132 : Nat := 4983230072969 + 3 ^ 40 * 7781132 * 2
def baseEnd_7781132 : Nat := 3995460752080555518965231

theorem tailTrace_7781132 : CollatzResearch.WordTrace tailWord_7781132 prefixEnd_7781132 3995460752080555518965231 := by
  unfold tailWord_7781132
  simp only [CollatzResearch.WordTrace]
  refine ⟨141900599623147575195328825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189200799497530100260438433 141900599623147575195328825)
  ·
    refine ⟨106425449717360681396496619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141900599623147575195328825 106425449717360681396496619)
    ·
      refine ⟨159638174576041022094744929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106425449717360681396496619 159638174576041022094744929)
      ·
        refine ⟨119728630932030766571058697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159638174576041022094744929 119728630932030766571058697)
        ·
          refine ⟨89796473199023074928294023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119728630932030766571058697 89796473199023074928294023)
          ·
            refine ⟨134694709798534612392441035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89796473199023074928294023 134694709798534612392441035)
            ·
              refine ⟨202042064697801918588661553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134694709798534612392441035 202042064697801918588661553)
              ·
                refine ⟨151531548523351438941496165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202042064697801918588661553 151531548523351438941496165)
                ·
                  refine ⟨28412165348128394801530531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151531548523351438941496165 28412165348128394801530531)
                  ·
                    refine ⟨42618248022192592202295797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28412165348128394801530531 42618248022192592202295797)
                    ·
                      refine ⟨3995460752080555518965231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42618248022192592202295797 3995460752080555518965231)
                      ·
                        rfl

theorem cell23_7781132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_7781132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781132 prefixEnd_7781132 := by exact prefixLift 7781132
  have htrace : WordTrace (prefixWord ++ tailWord_7781132) baseStart_7781132 baseEnd_7781132 := by
    simpa [prefixWord, tailWord_7781132, baseEnd_7781132] using wordTrace_append hprefix tailTrace_7781132
  have hstable : (prefixWord ++ tailWord_7781132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781132).length < 2 ^ (prefixWord ++ tailWord_7781132).sum := by decide
  have hdescent : baseEnd_7781132 < baseStart_7781132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781166 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7781166 : Nat := 118140960795 + 7781166 * 2 ^ 59
def prefixEnd_7781166 : Nat := 4983230072969 + 3 ^ 40 * 7781166 * 2
def baseEnd_7781166 : Nat := 3995478210422808385940075

theorem tailTrace_7781166 : CollatzResearch.WordTrace tailWord_7781166 prefixEnd_7781166 3995478210422808385940075 := by
  unfold tailWord_7781166
  simp only [CollatzResearch.WordTrace]
  refine ⟨35475304916021496774674419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189201626218781316131596901 35475304916021496774674419)
  ·
    refine ⟨53212957374032245162011629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35475304916021496774674419 53212957374032245162011629)
    ·
      refine ⟨19954859015262091935754361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53212957374032245162011629 19954859015262091935754361)
      ·
        refine ⟨14966144261446568951815771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19954859015262091935754361 14966144261446568951815771)
        ·
          refine ⟨22449216392169853427723657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14966144261446568951815771 22449216392169853427723657)
          ·
            refine ⟨16836912294127390070792743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22449216392169853427723657 16836912294127390070792743)
            ·
              refine ⟨25255368441191085106189115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16836912294127390070792743 25255368441191085106189115)
              ·
                refine ⟨37883052661786627659283673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25255368441191085106189115 37883052661786627659283673)
                ·
                  refine ⟨28412289496339970744462755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37883052661786627659283673 28412289496339970744462755)
                  ·
                    refine ⟨42618434244509956116694133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28412289496339970744462755 42618434244509956116694133)
                    ·
                      refine ⟨3995478210422808385940075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42618434244509956116694133 3995478210422808385940075)
                      ·
                        rfl

theorem cell23_7781166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7781166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781166 prefixEnd_7781166 := by exact prefixLift 7781166
  have htrace : WordTrace (prefixWord ++ tailWord_7781166) baseStart_7781166 baseEnd_7781166 := by
    simpa [prefixWord, tailWord_7781166, baseEnd_7781166] using wordTrace_append hprefix tailTrace_7781166
  have hstable : (prefixWord ++ tailWord_7781166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781166).length < 2 ^ (prefixWord ++ tailWord_7781166).sum := by decide
  have hdescent : baseEnd_7781166 < baseStart_7781166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781197 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_7781197 : Nat := 118140960795 + 7781197 * 2 ^ 59
def prefixEnd_7781197 : Nat := 4983230072969 + 3 ^ 40 * 7781197 * 2
def baseEnd_7781197 : Nat := 3995494128323097764652433

theorem tailTrace_7781197 : CollatzResearch.WordTrace tailWord_7781197 prefixEnd_7781197 3995494128323097764652433 := by
  unfold tailWord_7781197
  simp only [CollatzResearch.WordTrace]
  refine ⟨283803569991059666491773845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189202379994039777661182563 283803569991059666491773845)
  ·
    refine ⟨13303292343330921866801899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 283803569991059666491773845 13303292343330921866801899)
    ·
      refine ⟨19954938514996382800202849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13303292343330921866801899 19954938514996382800202849)
      ·
        refine ⟨14966203886247287100152137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19954938514996382800202849 14966203886247287100152137)
        ·
          refine ⟨11224652914685465325114103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14966203886247287100152137 11224652914685465325114103)
          ·
            refine ⟨16836979372028197987671155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11224652914685465325114103 16836979372028197987671155)
            ·
              refine ⟨25255469058042296981506733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16836979372028197987671155 25255469058042296981506733)
              ·
                refine ⟨9470800896765861368065025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25255469058042296981506733 9470800896765861368065025)
                ·
                  refine ⟨7103100672574396026048769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9470800896765861368065025 7103100672574396026048769)
                  ·
                    refine ⟨5327325504430797019536577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7103100672574396026048769 5327325504430797019536577)
                    ·
                      refine ⟨3995494128323097764652433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327325504430797019536577 3995494128323097764652433)
                      ·
                        rfl

theorem cell23_7781197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_7781197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781197 prefixEnd_7781197 := by exact prefixLift 7781197
  have htrace : WordTrace (prefixWord ++ tailWord_7781197) baseStart_7781197 baseEnd_7781197 := by
    simpa [prefixWord, tailWord_7781197, baseEnd_7781197] using wordTrace_append hprefix tailTrace_7781197
  have hstable : (prefixWord ++ tailWord_7781197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781197).length < 2 ^ (prefixWord ++ tailWord_7781197).sum := by decide
  have hdescent : baseEnd_7781197 < baseStart_7781197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781259 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 6]
def baseStart_7781259 : Nat := 118140960795 + 7781259 * 2 ^ 59
def prefixEnd_7781259 : Nat := 4983230072969 + 3 ^ 40 * 7781259 * 2
def baseEnd_7781259 : Nat := 443947329347075169119683

theorem tailTrace_7781259 : CollatzResearch.WordTrace tailWord_7781259 prefixEnd_7781259 443947329347075169119683 := by
  unfold tailWord_7781259
  simp only [CollatzResearch.WordTrace]
  refine ⟨283805831316835051080530831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189203887544556700720353887 283805831316835051080530831)
  ·
    refine ⟨425708746975252576620796247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283805831316835051080530831 425708746975252576620796247)
    ·
      refine ⟨638563120462878864931194371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425708746975252576620796247 638563120462878864931194371)
      ·
        refine ⟨957844680694318297396791557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638563120462878864931194371 957844680694318297396791557)
        ·
          refine ⟨179595877630184680761898417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 957844680694318297396791557 179595877630184680761898417)
          ·
            refine ⟨134696908222638510571423813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179595877630184680761898417 134696908222638510571423813)
            ·
              refine ⟨25255670291744720732141965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134696908222638510571423813 25255670291744720732141965)
              ·
                refine ⟨9470876359404270274553237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25255670291744720732141965 9470876359404270274553237)
                ·
                  refine ⟨443947329347075169119683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9470876359404270274553237 443947329347075169119683)
                  ·
                    rfl

theorem cell23_7781259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 6].length) (baseStart_7781259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781259 prefixEnd_7781259 := by exact prefixLift 7781259
  have htrace : WordTrace (prefixWord ++ tailWord_7781259) baseStart_7781259 baseEnd_7781259 := by
    simpa [prefixWord, tailWord_7781259, baseEnd_7781259] using wordTrace_append hprefix tailTrace_7781259
  have hstable : (prefixWord ++ tailWord_7781259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781259).length < 2 ^ (prefixWord ++ tailWord_7781259).sum := by decide
  have hdescent : baseEnd_7781259 < baseStart_7781259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781270 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7781270 : Nat := 118140960795 + 7781270 * 2 ^ 59
def prefixEnd_7781270 : Nat := 4983230072969 + 3 ^ 40 * 7781270 * 2
def baseEnd_7781270 : Nat := 3995531612410875979039597

theorem tailTrace_7781270 : CollatzResearch.WordTrace tailWord_7781270 prefixEnd_7781270 3995531612410875979039597 := by
  unfold tailWord_7781270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17737889532487199997448829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189204155013196799972787509 17737889532487199997448829)
  ·
    refine ⟨6651708574682699999043311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17737889532487199997448829 6651708574682699999043311)
    ·
      refine ⟨9977562862024049998564967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651708574682699999043311 9977562862024049998564967)
      ·
        refine ⟨14966344293036074997847451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9977562862024049998564967 14966344293036074997847451)
        ·
          refine ⟨22449516439554112496771177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14966344293036074997847451 22449516439554112496771177)
          ·
            refine ⟨16837137329665584372578383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22449516439554112496771177 16837137329665584372578383)
            ·
              refine ⟨25255705994498376558867575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16837137329665584372578383 25255705994498376558867575)
              ·
                refine ⟨37883558991747564838301363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25255705994498376558867575 37883558991747564838301363)
                ·
                  refine ⟨56825338487621347257452045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37883558991747564838301363 56825338487621347257452045)
                  ·
                    refine ⟨21309501932858005221544517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56825338487621347257452045 21309501932858005221544517)
                    ·
                      refine ⟨3995531612410875979039597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21309501932858005221544517 3995531612410875979039597)
                      ·
                        rfl

theorem cell23_7781270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7781270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781270 prefixEnd_7781270 := by exact prefixLift 7781270
  have htrace : WordTrace (prefixWord ++ tailWord_7781270) baseStart_7781270 baseEnd_7781270 := by
    simpa [prefixWord, tailWord_7781270, baseEnd_7781270] using wordTrace_append hprefix tailTrace_7781270
  have hstable : (prefixWord ++ tailWord_7781270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781270).length < 2 ^ (prefixWord ++ tailWord_7781270).sum := by decide
  have hdescent : baseEnd_7781270 < baseStart_7781270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781293 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 8]
def baseStart_7781293 : Nat := 118140960795 + 7781293 * 2 ^ 59
def prefixEnd_7781293 : Nat := 4983230072969 + 3 ^ 40 * 7781293 * 2
def baseEnd_7781293 : Nat := 443949269162881043227999

theorem tailTrace_7781293 : CollatzResearch.WordTrace tailWord_7781293 prefixEnd_7781293 443949269162881043227999 := by
  unfold tailWord_7781293
  simp only [CollatzResearch.WordTrace]
  refine ⟨283807071398711874887268533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189204714265807916591512355 283807071398711874887268533)
  ·
    refine ⟨26606912943629238270681425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283807071398711874887268533 26606912943629238270681425)
    ·
      refine ⟨19955184707721928703011069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26606912943629238270681425 19955184707721928703011069)
      ·
        refine ⟨7483194265395723263629151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19955184707721928703011069 7483194265395723263629151)
        ·
          refine ⟨11224791398093584895443727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483194265395723263629151 11224791398093584895443727)
          ·
            refine ⟨16837187097140377343165591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11224791398093584895443727 16837187097140377343165591)
            ·
              refine ⟨25255780645710566014748387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16837187097140377343165591 25255780645710566014748387)
              ·
                refine ⟨37883670968565849022122581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25255780645710566014748387 37883670968565849022122581)
                ·
                  refine ⟨443949269162881043227999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37883670968565849022122581 443949269162881043227999)
                  ·
                    rfl

theorem cell23_7781293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_7781293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781293 prefixEnd_7781293 := by exact prefixLift 7781293
  have htrace : WordTrace (prefixWord ++ tailWord_7781293) baseStart_7781293 baseEnd_7781293 := by
    simpa [prefixWord, tailWord_7781293, baseEnd_7781293] using wordTrace_append hprefix tailTrace_7781293
  have hstable : (prefixWord ++ tailWord_7781293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781293).length < 2 ^ (prefixWord ++ tailWord_7781293).sum := by decide
  have hdescent : baseEnd_7781293 < baseStart_7781293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781329 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_7781329 : Nat := 118140960795 + 7781329 * 2 ^ 59
def prefixEnd_7781329 : Nat := 4983230072969 + 3 ^ 40 * 7781329 * 2
def baseEnd_7781329 : Nat := 3995561907769491248201825

theorem tailTrace_7781329 : CollatzResearch.WordTrace tailWord_7781329 prefixEnd_7781329 3995561907769491248201825 := by
  unfold tailWord_7781329
  simp only [CollatzResearch.WordTrace]
  refine ⟨283808384426581453035579041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189205589617720968690386027 283808384426581453035579041)
  ·
    refine ⟨212856288319936089776684281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283808384426581453035579041 212856288319936089776684281)
    ·
      refine ⟨159642216239952067332513211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212856288319936089776684281 159642216239952067332513211)
      ·
        refine ⟨239463324359928100998769817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159642216239952067332513211 239463324359928100998769817)
        ·
          refine ⟨179597493269946075749077363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239463324359928100998769817 179597493269946075749077363)
          ·
            refine ⟨269396239904919113623616045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179597493269946075749077363 269396239904919113623616045)
            ·
              refine ⟨101023589964344667608856017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269396239904919113623616045 101023589964344667608856017)
              ·
                refine ⟨75767692473258500706642013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101023589964344667608856017 75767692473258500706642013)
                ·
                  refine ⟨28412884677471937764990755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75767692473258500706642013 28412884677471937764990755)
                  ·
                    refine ⟨42619327016207906647486133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28412884677471937764990755 42619327016207906647486133)
                    ·
                      refine ⟨3995561907769491248201825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42619327016207906647486133 3995561907769491248201825)
                      ·
                        rfl

theorem cell23_7781329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_7781329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781329 prefixEnd_7781329 := by exact prefixLift 7781329
  have htrace : WordTrace (prefixWord ++ tailWord_7781329) baseStart_7781329 baseEnd_7781329 := by
    simpa [prefixWord, tailWord_7781329, baseEnd_7781329] using wordTrace_append hprefix tailTrace_7781329
  have hstable : (prefixWord ++ tailWord_7781329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781329).length < 2 ^ (prefixWord ++ tailWord_7781329).sum := by decide
  have hdescent : baseEnd_7781329 < baseStart_7781329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781336 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 4, 4]
def baseStart_7781336 : Nat := 118140960795 + 7781336 * 2 ^ 59
def prefixEnd_7781336 : Nat := 4983230072969 + 3 ^ 40 * 7781336 * 2
def baseEnd_7781336 : Nat := 1331855167378024240271431

theorem tailTrace_7781336 : CollatzResearch.WordTrace tailWord_7781336 prefixEnd_7781336 1331855167378024240271431 := by
  unfold tailWord_7781336
  simp only [CollatzResearch.WordTrace]
  refine ⟨141904319868778046615541931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189205759825037395487389241 141904319868778046615541931)
  ·
    refine ⟨212856479803167069923312897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141904319868778046615541931 212856479803167069923312897)
    ·
      refine ⟨159642359852375302442484673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212856479803167069923312897 159642359852375302442484673)
      ·
        refine ⟨119731769889281476831863505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159642359852375302442484673 119731769889281476831863505)
        ·
          refine ⟨89798827416961107623897629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119731769889281476831863505 89798827416961107623897629)
          ·
            refine ⟨33674560281360415358961611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89798827416961107623897629 33674560281360415358961611)
            ·
              refine ⟨50511840422040623038442417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33674560281360415358961611 50511840422040623038442417)
              ·
                refine ⟨37883880316530467278831813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50511840422040623038442417 37883880316530467278831813)
                ·
                  refine ⟨7103227559349462614780965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37883880316530467278831813 7103227559349462614780965)
                  ·
                    refine ⟨1331855167378024240271431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103227559349462614780965 1331855167378024240271431)
                    ·
                      rfl

theorem cell23_7781336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_7781336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781336 prefixEnd_7781336 := by exact prefixLift 7781336
  have htrace : WordTrace (prefixWord ++ tailWord_7781336) baseStart_7781336 baseEnd_7781336 := by
    simpa [prefixWord, tailWord_7781336, baseEnd_7781336] using wordTrace_append hprefix tailTrace_7781336
  have hstable : (prefixWord ++ tailWord_7781336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781336).length < 2 ^ (prefixWord ++ tailWord_7781336).sum := by decide
  have hdescent : baseEnd_7781336 < baseStart_7781336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781337 : List Nat := [1, 2, 1, 2, 5, 3, 1, 3, 1, 1, 3]
def baseStart_7781337 : Nat := 118140960795 + 7781337 * 2 ^ 59
def prefixEnd_7781337 : Nat := 4983230072969 + 3 ^ 40 * 7781337 * 2
def baseEnd_7781337 : Nat := 3995566015614727216901789

theorem tailTrace_7781337 : CollatzResearch.WordTrace tailWord_7781337 prefixEnd_7781337 3995566015614727216901789 := by
  unfold tailWord_7781337
  simp only [CollatzResearch.WordTrace]
  refine ⟨283808676210552470401870265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189205784140368313601246843 283808676210552470401870265)
  ·
    refine ⟨212856507157914352801402699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283808676210552470401870265 212856507157914352801402699)
    ·
      refine ⟨319284760736871529202104049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212856507157914352801402699 319284760736871529202104049)
      ·
        refine ⟨239463570552653646901578037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319284760736871529202104049 239463570552653646901578037)
        ·
          refine ⟨22449709739311279397022941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239463570552653646901578037 22449709739311279397022941)
          ·
            refine ⟨8418641152241729773883603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22449709739311279397022941 8418641152241729773883603)
            ·
              refine ⟨12627961728362594660825405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8418641152241729773883603 12627961728362594660825405)
              ·
                refine ⟨4735485648135972997809527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12627961728362594660825405 4735485648135972997809527)
                ·
                  refine ⟨7103228472203959496714291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735485648135972997809527 7103228472203959496714291)
                  ·
                    refine ⟨10654842708305939245071437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7103228472203959496714291 10654842708305939245071437)
                    ·
                      refine ⟨3995566015614727216901789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10654842708305939245071437 3995566015614727216901789)
                      ·
                        rfl

theorem cell23_7781337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_7781337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781337 prefixEnd_7781337 := by exact prefixLift 7781337
  have htrace : WordTrace (prefixWord ++ tailWord_7781337) baseStart_7781337 baseEnd_7781337 := by
    simpa [prefixWord, tailWord_7781337, baseEnd_7781337] using wordTrace_append hprefix tailTrace_7781337
  have hstable : (prefixWord ++ tailWord_7781337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781337).length < 2 ^ (prefixWord ++ tailWord_7781337).sum := by decide
  have hdescent : baseEnd_7781337 < baseStart_7781337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781366 : List Nat := [5, 1, 1, 1, 3, 1, 1, 10]
def baseStart_7781366 : Nat := 118140960795 + 7781366 * 2 ^ 59
def prefixEnd_7781366 : Nat := 4983230072969 + 3 ^ 40 * 7781366 * 2
def baseEnd_7781366 : Nat := 147984478020507689016265

theorem tailTrace_7781366 : CollatzResearch.WordTrace tailWord_7781366 prefixEnd_7781366 147984478020507689016265 := by
  unfold tailWord_7781366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738108370465463022167247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189206489284964938903117301 17738108370465463022167247)
  ·
    refine ⟨26607162555698194533250871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17738108370465463022167247 26607162555698194533250871)
    ·
      refine ⟨39910743833547291799876307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26607162555698194533250871 39910743833547291799876307)
      ·
        refine ⟨59866115750320937699814461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39910743833547291799876307 59866115750320937699814461)
        ·
          refine ⟨22449793406370351637430423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59866115750320937699814461 22449793406370351637430423)
          ·
            refine ⟨33674690109555527456145635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22449793406370351637430423 33674690109555527456145635)
            ·
              refine ⟨50512035164333291184218453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33674690109555527456145635 50512035164333291184218453)
              ·
                refine ⟨147984478020507689016265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50512035164333291184218453 147984478020507689016265)
                ·
                  rfl

theorem cell23_7781366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_7781366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781366 prefixEnd_7781366 := by exact prefixLift 7781366
  have htrace : WordTrace (prefixWord ++ tailWord_7781366) baseStart_7781366 baseEnd_7781366 := by
    simpa [prefixWord, tailWord_7781366, baseEnd_7781366] using wordTrace_append hprefix tailTrace_7781366
  have hstable : (prefixWord ++ tailWord_7781366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781366).length < 2 ^ (prefixWord ++ tailWord_7781366).sum := by decide
  have hdescent : baseEnd_7781366 < baseStart_7781366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781369 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_7781369 : Nat := 118140960795 + 7781369 * 2 ^ 59
def prefixEnd_7781369 : Nat := 4983230072969 + 3 ^ 40 * 7781369 * 2
def baseEnd_7781369 : Nat := 3995582446995671091701641

theorem tailTrace_7781369 : CollatzResearch.WordTrace tailWord_7781369 prefixEnd_7781369 3995582446995671091701641 := by
  unfold tailWord_7781369
  simp only [CollatzResearch.WordTrace]
  refine ⟨283809843346436539867035161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189206562230957693244690107 283809843346436539867035161)
  ·
    refine ⟨212857382509827404900276371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283809843346436539867035161 212857382509827404900276371)
    ·
      refine ⟨319286073764741107350414557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212857382509827404900276371 319286073764741107350414557)
      ·
        refine ⟨119732277661777915256405459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319286073764741107350414557 119732277661777915256405459)
        ·
          refine ⟨179598416492666872884608189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119732277661777915256405459 179598416492666872884608189)
          ·
            refine ⟨67349406184750077331728071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179598416492666872884608189 67349406184750077331728071)
            ·
              refine ⟨101024109277125115997592107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67349406184750077331728071 101024109277125115997592107)
              ·
                refine ⟨151536163915687673996388161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101024109277125115997592107 151536163915687673996388161)
                ·
                  refine ⟨113652122936765755497291121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151536163915687673996388161 113652122936765755497291121)
                  ·
                    refine ⟨85239092202574316622968341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113652122936765755497291121 85239092202574316622968341)
                    ·
                      refine ⟨3995582446995671091701641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85239092202574316622968341 3995582446995671091701641)
                      ·
                        rfl

theorem cell23_7781369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_7781369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781369 prefixEnd_7781369 := by exact prefixLift 7781369
  have htrace : WordTrace (prefixWord ++ tailWord_7781369) baseStart_7781369 baseEnd_7781369 := by
    simpa [prefixWord, tailWord_7781369, baseEnd_7781369] using wordTrace_append hprefix tailTrace_7781369
  have hstable : (prefixWord ++ tailWord_7781369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781369).length < 2 ^ (prefixWord ++ tailWord_7781369).sum := by decide
  have hdescent : baseEnd_7781369 < baseStart_7781369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781410 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_7781410 : Nat := 118140960795 + 7781410 * 2 ^ 59
def prefixEnd_7781410 : Nat := 4983230072969 + 3 ^ 40 * 7781410 * 2
def baseEnd_7781410 : Nat := 3995603499702505431288953

theorem tailTrace_7781410 : CollatzResearch.WordTrace tailWord_7781410 prefixEnd_7781410 3995603499702505431288953 := by
  unfold tailWord_7781410
  simp only [CollatzResearch.WordTrace]
  refine ⟨70952834684822000967319421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189207559159525335912851789 70952834684822000967319421)
  ·
    refine ⟨26607313006808250362744783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70952834684822000967319421 26607313006808250362744783)
    ·
      refine ⟨39910969510212375544117175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26607313006808250362744783 39910969510212375544117175)
      ·
        refine ⟨59866454265318563316175763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39910969510212375544117175 59866454265318563316175763)
        ·
          refine ⟨89799681397977844974263645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59866454265318563316175763 89799681397977844974263645)
          ·
            refine ⟨33674880524241691865348867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89799681397977844974263645 33674880524241691865348867)
            ·
              refine ⟨50512320786362537798023301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33674880524241691865348867 50512320786362537798023301)
              ·
                refine ⟨9471060147442975837129369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50512320786362537798023301 9471060147442975837129369)
                ·
                  refine ⟨7103295110582231877847027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9471060147442975837129369 7103295110582231877847027)
                  ·
                    refine ⟨10654942665873347816770541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7103295110582231877847027 10654942665873347816770541)
                    ·
                      refine ⟨3995603499702505431288953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10654942665873347816770541 3995603499702505431288953)
                      ·
                        rfl

theorem cell23_7781410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_7781410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781410 prefixEnd_7781410 := by exact prefixLift 7781410
  have htrace : WordTrace (prefixWord ++ tailWord_7781410) baseStart_7781410 baseEnd_7781410 := by
    simpa [prefixWord, tailWord_7781410, baseEnd_7781410] using wordTrace_append hprefix tailTrace_7781410
  have hstable : (prefixWord ++ tailWord_7781410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781410).length < 2 ^ (prefixWord ++ tailWord_7781410).sum := by decide
  have hdescent : baseEnd_7781410 < baseStart_7781410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781426 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_7781426 : Nat := 118140960795 + 7781426 * 2 ^ 59
def prefixEnd_7781426 : Nat := 4983230072969 + 3 ^ 40 * 7781426 * 2
def baseEnd_7781426 : Nat := 1331870571797659122896293

theorem tailTrace_7781426 : CollatzResearch.WordTrace tailWord_7781426 prefixEnd_7781426 1331870571797659122896293 := by
  unfold tailWord_7781426
  simp only [CollatzResearch.WordTrace]
  refine ⟨70952980576807509650465033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189207948204820025734573421 70952980576807509650465033)
  ·
    refine ⟨53214735432605632237848775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70952980576807509650465033 53214735432605632237848775)
    ·
      refine ⟨79822103148908448356773163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53214735432605632237848775 79822103148908448356773163)
      ·
        refine ⟨119733154723362672535159745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79822103148908448356773163 119733154723362672535159745)
        ·
          refine ⟨89799866042522004401369809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119733154723362672535159745 89799866042522004401369809)
          ·
            refine ⟨67349899531891503301027357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89799866042522004401369809 67349899531891503301027357)
            ·
              refine ⟨25256212324459313737885259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67349899531891503301027357 25256212324459313737885259)
              ·
                refine ⟨37884318486688970606827889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25256212324459313737885259 37884318486688970606827889)
                ·
                  refine ⟨28413238865016727955120917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37884318486688970606827889 28413238865016727955120917)
                  ·
                    refine ⟨1331870571797659122896293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28413238865016727955120917 1331870571797659122896293)
                    ·
                      rfl

theorem cell23_7781426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_7781426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781426 prefixEnd_7781426 := by exact prefixLift 7781426
  have htrace : WordTrace (prefixWord ++ tailWord_7781426) baseStart_7781426 baseEnd_7781426 := by
    simpa [prefixWord, tailWord_7781426, baseEnd_7781426] using wordTrace_append hprefix tailTrace_7781426
  have hstable : (prefixWord ++ tailWord_7781426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781426).length < 2 ^ (prefixWord ++ tailWord_7781426).sum := by decide
  have hdescent : baseEnd_7781426 < baseStart_7781426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781473 : List Nat := [1, 2, 3, 1, 1, 2, 4, 4, 5]
def baseStart_7781473 : Nat := 118140960795 + 7781473 * 2 ^ 59
def prefixEnd_7781473 : Nat := 4983230072969 + 3 ^ 40 * 7781473 * 2
def baseEnd_7781473 : Nat := 443959538775970964977907

theorem tailTrace_7781473 : CollatzResearch.WordTrace tailWord_7781473 prefixEnd_7781473 443959538775970964977907 := by
  unfold tailWord_7781473
  simp only [CollatzResearch.WordTrace]
  refine ⟨283813636538059765628821073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189209091025373177085880715 283813636538059765628821073)
  ·
    refine ⟨212860227403544824221615805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283813636538059765628821073 212860227403544824221615805)
    ·
      refine ⟨79822585276329309083105927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212860227403544824221615805 79822585276329309083105927)
      ·
        refine ⟨119733877914493963624658891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79822585276329309083105927 119733877914493963624658891)
        ·
          refine ⟨179600816871740945436988337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119733877914493963624658891 179600816871740945436988337)
          ·
            refine ⟨134700612653805709077741253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179600816871740945436988337 134700612653805709077741253)
            ·
              refine ⟨25256364872588570452076485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134700612653805709077741253 25256364872588570452076485)
              ·
                refine ⟨4735568413610356959764341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25256364872588570452076485 4735568413610356959764341)
                ·
                  refine ⟨443959538775970964977907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4735568413610356959764341 443959538775970964977907)
                  ·
                    rfl

theorem cell23_7781473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 5].length) (baseStart_7781473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781473 prefixEnd_7781473 := by exact prefixLift 7781473
  have htrace : WordTrace (prefixWord ++ tailWord_7781473) baseStart_7781473 baseEnd_7781473 := by
    simpa [prefixWord, tailWord_7781473, baseEnd_7781473] using wordTrace_append hprefix tailTrace_7781473
  have hstable : (prefixWord ++ tailWord_7781473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781473).length < 2 ^ (prefixWord ++ tailWord_7781473).sum := by decide
  have hdescent : baseEnd_7781473 < baseStart_7781473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781523 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 4, 4, 2]
def baseStart_7781523 : Nat := 118140960795 + 7781523 * 2 ^ 59
def prefixEnd_7781523 : Nat := 4983230072969 + 3 ^ 40 * 7781523 * 2
def baseEnd_7781523 : Nat := 3995661523016463489175933

theorem tailTrace_7781523 : CollatzResearch.WordTrace tailWord_7781523 prefixEnd_7781523 3995661523016463489175933 := by
  unfold tailWord_7781523
  simp only [CollatzResearch.WordTrace]
  refine ⟨283815460187878624168141223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189210306791919082778760815 283815460187878624168141223)
  ·
    refine ⟨425723190281817936252211835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283815460187878624168141223 425723190281817936252211835)
    ·
      refine ⟨638584785422726904378317753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425723190281817936252211835 638584785422726904378317753)
      ·
        refine ⟨478938589067045178283738315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638584785422726904378317753 478938589067045178283738315)
        ·
          refine ⟨718407883600567767425607473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478938589067045178283738315 718407883600567767425607473)
          ·
            refine ⟨538805912700425825569205605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718407883600567767425607473 538805912700425825569205605)
            ·
              refine ⟨101026108631329842294226051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538805912700425825569205605 101026108631329842294226051)
              ·
                refine ⟨151539162946994763441339077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101026108631329842294226051 151539162946994763441339077)
                ·
                  refine ⟨28413593052561518145251077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151539162946994763441339077 28413593052561518145251077)
                  ·
                    refine ⟨5327548697355284652234577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28413593052561518145251077 5327548697355284652234577)
                    ·
                      refine ⟨3995661523016463489175933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327548697355284652234577 3995661523016463489175933)
                      ·
                        rfl

theorem cell23_7781523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 4, 2].length) (baseStart_7781523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781523 prefixEnd_7781523 := by exact prefixLift 7781523
  have htrace : WordTrace (prefixWord ++ tailWord_7781523) baseStart_7781523 baseEnd_7781523 := by
    simpa [prefixWord, tailWord_7781523, baseEnd_7781523] using wordTrace_append hprefix tailTrace_7781523
  have hstable : (prefixWord ++ tailWord_7781523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781523).length < 2 ^ (prefixWord ++ tailWord_7781523).sum := by decide
  have hdescent : baseEnd_7781523 < baseStart_7781523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781623 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 6, 4]
def baseStart_7781623 : Nat := 118140960795 + 7781623 * 2 ^ 59
def prefixEnd_7781623 : Nat := 4983230072969 + 3 ^ 40 * 7781623 * 2
def baseEnd_7781623 : Nat := 1331904290360637699308491

theorem tailTrace_7781623 : CollatzResearch.WordTrace tailWord_7781623 prefixEnd_7781623 1331904290360637699308491 := by
  unfold tailWord_7781623
  simp only [CollatzResearch.WordTrace]
  refine ⟨283819107487516341246781523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189212738325010894164521015 283819107487516341246781523)
  ·
    refine ⟨425728661231274511870172285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283819107487516341246781523 425728661231274511870172285)
    ·
      refine ⟨159648247961727941951314607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425728661231274511870172285 159648247961727941951314607)
      ·
        refine ⟨239472371942591912926971911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159648247961727941951314607 239472371942591912926971911)
        ·
          refine ⟨359208557913887869390457867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239472371942591912926971911 359208557913887869390457867)
          ·
            refine ⟨538812836870831804085686801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359208557913887869390457867 538812836870831804085686801)
            ·
              refine ⟨404109627653123853064265101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538812836870831804085686801 404109627653123853064265101)
              ·
                refine ⟨151541110369921444899099413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404109627653123853064265101 151541110369921444899099413)
                ·
                  refine ⟨7103489548590067729645285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151541110369921444899099413 7103489548590067729645285)
                  ·
                    refine ⟨1331904290360637699308491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103489548590067729645285 1331904290360637699308491)
                    ·
                      rfl

theorem cell23_7781623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_7781623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781623 prefixEnd_7781623 := by exact prefixLift 7781623
  have htrace : WordTrace (prefixWord ++ tailWord_7781623) baseStart_7781623 baseEnd_7781623 := by
    simpa [prefixWord, tailWord_7781623, baseEnd_7781623] using wordTrace_append hprefix tailTrace_7781623
  have hstable : (prefixWord ++ tailWord_7781623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781623).length < 2 ^ (prefixWord ++ tailWord_7781623).sum := by decide
  have hdescent : baseEnd_7781623 < baseStart_7781623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781660 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_7781660 : Nat := 118140960795 + 7781660 * 2 ^ 59
def prefixEnd_7781660 : Nat := 4983230072969 + 3 ^ 40 * 7781660 * 2
def baseEnd_7781660 : Nat := 3995731869866129453162803

theorem tailTrace_7781660 : CollatzResearch.WordTrace tailWord_7781660 prefixEnd_7781660 3995731869866129453162803 := by
  unfold tailWord_7781660
  simp only [CollatzResearch.WordTrace]
  refine ⟨141910228494191148282939217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189213637992254864377252289 141910228494191148282939217)
  ·
    refine ⟨106432671370643361212204413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141910228494191148282939217 106432671370643361212204413)
    ·
      refine ⟨39912251763991260454576655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106432671370643361212204413 39912251763991260454576655)
      ·
        refine ⟨59868377645986890681864983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39912251763991260454576655 59868377645986890681864983)
        ·
          refine ⟨89802566468980336022797475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59868377645986890681864983 89802566468980336022797475)
          ·
            refine ⟨134703849703470504034196213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89802566468980336022797475 134703849703470504034196213)
            ·
              refine ⟨12628485909700359753205895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134703849703470504034196213 12628485909700359753205895)
              ·
                refine ⟨18942728864550539629808843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12628485909700359753205895 18942728864550539629808843)
                ·
                  refine ⟨28414093296825809444713265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18942728864550539629808843 28414093296825809444713265)
                  ·
                    refine ⟨21310569972619357083534949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28414093296825809444713265 21310569972619357083534949)
                    ·
                      refine ⟨3995731869866129453162803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21310569972619357083534949 3995731869866129453162803)
                      ·
                        rfl

theorem cell23_7781660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_7781660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781660 prefixEnd_7781660 := by exact prefixLift 7781660
  have htrace : WordTrace (prefixWord ++ tailWord_7781660) baseStart_7781660 baseEnd_7781660 := by
    simpa [prefixWord, tailWord_7781660, baseEnd_7781660] using wordTrace_append hprefix tailTrace_7781660
  have hstable : (prefixWord ++ tailWord_7781660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781660).length < 2 ^ (prefixWord ++ tailWord_7781660).sum := by decide
  have hdescent : baseEnd_7781660 < baseStart_7781660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781667 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 3]
def baseStart_7781667 : Nat := 118140960795 + 7781667 * 2 ^ 59
def prefixEnd_7781667 : Nat := 4983230072969 + 3 ^ 40 * 7781667 * 2
def baseEnd_7781667 : Nat := 3995735464230710925775271

theorem tailTrace_7781667 : CollatzResearch.WordTrace tailWord_7781667 prefixEnd_7781667 3995735464230710925775271 := by
  unfold tailWord_7781667
  simp only [CollatzResearch.WordTrace]
  refine ⟨283820712299356936761383255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189213808199571291174255503 283820712299356936761383255)
  ·
    refine ⟨425731068449035405142074883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283820712299356936761383255 425731068449035405142074883)
    ·
      refine ⟨638596602673553107713112325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425731068449035405142074883 638596602673553107713112325)
      ·
        refine ⟨119736863001291207696208561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 638596602673553107713112325 119736863001291207696208561)
        ·
          refine ⟨89802647250968405772156421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119736863001291207696208561 89802647250968405772156421)
          ·
            refine ⟨16837996359556576082279329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89802647250968405772156421 16837996359556576082279329)
            ·
              refine ⟨12628497269667432061709497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16837996359556576082279329 12628497269667432061709497)
              ·
                refine ⟨9471372952250574046282123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12628497269667432061709497 9471372952250574046282123)
                ·
                  refine ⟨14207059428375861069423185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9471372952250574046282123 14207059428375861069423185)
                  ·
                    refine ⟨10655294571281895802067389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14207059428375861069423185 10655294571281895802067389)
                    ·
                      refine ⟨3995735464230710925775271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10655294571281895802067389 3995735464230710925775271)
                      ·
                        rfl

theorem cell23_7781667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_7781667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781667 prefixEnd_7781667 := by exact prefixLift 7781667
  have htrace : WordTrace (prefixWord ++ tailWord_7781667) baseStart_7781667 baseEnd_7781667 := by
    simpa [prefixWord, tailWord_7781667, baseEnd_7781667] using wordTrace_append hprefix tailTrace_7781667
  have hstable : (prefixWord ++ tailWord_7781667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781667).length < 2 ^ (prefixWord ++ tailWord_7781667).sum := by decide
  have hdescent : baseEnd_7781667 < baseStart_7781667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781680 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 6, 1, 3]
def baseStart_7781680 : Nat := 118140960795 + 7781680 * 2 ^ 59
def prefixEnd_7781680 : Nat := 4983230072969 + 3 ^ 40 * 7781680 * 2
def baseEnd_7781680 : Nat := 3995742139479219374912711

theorem tailTrace_7781680 : CollatzResearch.WordTrace tailWord_7781680 prefixEnd_7781680 3995742139479219374912711 := by
  unfold tailWord_7781680
  simp only [CollatzResearch.WordTrace]
  refine ⟨141910593224154919990803247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189214124298873226654404329 141910593224154919990803247)
  ·
    refine ⟨212865889836232379986204871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141910593224154919990803247 212865889836232379986204871)
    ·
      refine ⟨319298834754348569979307307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212865889836232379986204871 319298834754348569979307307)
      ·
        refine ⟨478948252131522854968960961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319298834754348569979307307 478948252131522854968960961)
        ·
          refine ⟨359211189098642141226720721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478948252131522854968960961 359211189098642141226720721)
          ·
            refine ⟨269408391823981605920040541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359211189098642141226720721 269408391823981605920040541)
            ·
              refine ⟨101028146933993102220015203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269408391823981605920040541 101028146933993102220015203)
              ·
                refine ⟨151542220400989653330022805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101028146933993102220015203 151542220400989653330022805)
                ·
                  refine ⟨7103541581296389999844819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151542220400989653330022805 7103541581296389999844819)
                  ·
                    refine ⟨10655312371944584999767229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7103541581296389999844819 10655312371944584999767229)
                    ·
                      refine ⟨3995742139479219374912711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10655312371944584999767229 3995742139479219374912711)
                      ·
                        rfl

theorem cell23_7781680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 1, 3].length) (baseStart_7781680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781680 prefixEnd_7781680 := by exact prefixLift 7781680
  have htrace : WordTrace (prefixWord ++ tailWord_7781680) baseStart_7781680 baseEnd_7781680 := by
    simpa [prefixWord, tailWord_7781680, baseEnd_7781680] using wordTrace_append hprefix tailTrace_7781680
  have hstable : (prefixWord ++ tailWord_7781680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781680).length < 2 ^ (prefixWord ++ tailWord_7781680).sum := by decide
  have hdescent : baseEnd_7781680 < baseStart_7781680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781681 : List Nat := [1, 2, 2, 3, 3, 1, 3, 3, 1, 2, 2]
def baseStart_7781681 : Nat := 118140960795 + 7781681 * 2 ^ 59
def prefixEnd_7781681 : Nat := 4983230072969 + 3 ^ 40 * 7781681 * 2
def baseEnd_7781681 : Nat := 3995742652959873871000207

theorem tailTrace_7781681 : CollatzResearch.WordTrace tailWord_7781681 prefixEnd_7781681 3995742652959873871000207 := by
  unfold tailWord_7781681
  simp only [CollatzResearch.WordTrace]
  refine ⟨283821222921306217152392897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189214148614204144768261931 283821222921306217152392897)
  ·
    refine ⟨212865917190979662864294673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283821222921306217152392897 212865917190979662864294673)
    ·
      refine ⟨159649437893234747148221005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212865917190979662864294673 159649437893234747148221005)
      ·
        refine ⟨59868539209963030180582877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159649437893234747148221005 59868539209963030180582877)
        ·
          refine ⟨22450702203736136317718579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59868539209963030180582877 22450702203736136317718579)
          ·
            refine ⟨33676053305604204476577869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22450702203736136317718579 33676053305604204476577869)
            ·
              refine ⟨12628519989601576678716701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33676053305604204476577869 12628519989601576678716701)
              ·
                refine ⟨4735694996100591254518763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12628519989601576678716701 4735694996100591254518763)
                ·
                  refine ⟨7103542494150886881778145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735694996100591254518763 7103542494150886881778145)
                  ·
                    refine ⟨5327656870613165161333609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7103542494150886881778145 5327656870613165161333609)
                    ·
                      refine ⟨3995742652959873871000207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327656870613165161333609 3995742652959873871000207)
                      ·
                        rfl

theorem cell23_7781681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_7781681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781681 prefixEnd_7781681 := by exact prefixLift 7781681
  have htrace : WordTrace (prefixWord ++ tailWord_7781681) baseStart_7781681 baseEnd_7781681 := by
    simpa [prefixWord, tailWord_7781681, baseEnd_7781681] using wordTrace_append hprefix tailTrace_7781681
  have hstable : (prefixWord ++ tailWord_7781681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781681).length < 2 ^ (prefixWord ++ tailWord_7781681).sum := by decide
  have hdescent : baseEnd_7781681 < baseStart_7781681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781713 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 1, 8]
def baseStart_7781713 : Nat := 118140960795 + 7781713 * 2 ^ 59
def prefixEnd_7781713 : Nat := 4983230072969 + 3 ^ 40 * 7781713 * 2
def baseEnd_7781713 : Nat := 1331919694780272581933353

theorem tailTrace_7781713 : CollatzResearch.WordTrace tailWord_7781713 prefixEnd_7781713 1331919694780272581933353 := by
  unfold tailWord_7781713
  simp only [CollatzResearch.WordTrace]
  refine ⟨283822390057190286617557793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189214926704793524411705195 283822390057190286617557793)
  ·
    refine ⟨212866792542892714963168345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283822390057190286617557793 212866792542892714963168345)
    ·
      refine ⟨159650094407169536222376259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212866792542892714963168345 159650094407169536222376259)
      ·
        refine ⟨239475141610754304333564389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159650094407169536222376259 239475141610754304333564389)
        ·
          refine ⟨44901589052016432062543323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239475141610754304333564389 44901589052016432062543323)
          ·
            refine ⟨67352383578024648093814985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44901589052016432062543323 67352383578024648093814985)
            ·
              refine ⟨50514287683518486070361239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67352383578024648093814985 50514287683518486070361239)
              ·
                refine ⟨75771431525277729105541859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50514287683518486070361239 75771431525277729105541859)
                ·
                  refine ⟨113657147287916593658312789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75771431525277729105541859 113657147287916593658312789)
                  ·
                    refine ⟨1331919694780272581933353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113657147287916593658312789 1331919694780272581933353)
                    ·
                      rfl

theorem cell23_7781713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_7781713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781713 prefixEnd_7781713 := by exact prefixLift 7781713
  have htrace : WordTrace (prefixWord ++ tailWord_7781713) baseStart_7781713 baseEnd_7781713 := by
    simpa [prefixWord, tailWord_7781713, baseEnd_7781713] using wordTrace_append hprefix tailTrace_7781713
  have hstable : (prefixWord ++ tailWord_7781713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781713).length < 2 ^ (prefixWord ++ tailWord_7781713).sum := by decide
  have hdescent : baseEnd_7781713 < baseStart_7781713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781718 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7781718 : Nat := 118140960795 + 7781718 * 2 ^ 59
def prefixEnd_7781718 : Nat := 4983230072969 + 3 ^ 40 * 7781718 * 2
def baseEnd_7781718 : Nat := 3995761651744090226237537

theorem tailTrace_7781718 : CollatzResearch.WordTrace tailWord_7781718 prefixEnd_7781718 3995761651744090226237537 := by
  unfold tailWord_7781718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738910776385760779468113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189215048281448114980993205 17738910776385760779468113)
  ·
    refine ⟨13304183082289320584601085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17738910776385760779468113 13304183082289320584601085)
    ·
      refine ⟨4989068655858495219225407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13304183082289320584601085 4989068655858495219225407)
      ·
        refine ⟨7483602983787742828838111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989068655858495219225407 7483602983787742828838111)
        ·
          refine ⟨11225404475681614243257167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483602983787742828838111 11225404475681614243257167)
          ·
            refine ⟨16838106713522421364885751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11225404475681614243257167 16838106713522421364885751)
            ·
              refine ⟨25257160070283632047328627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16838106713522421364885751 25257160070283632047328627)
              ·
                refine ⟨37885740105425448070992941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25257160070283632047328627 37885740105425448070992941)
                ·
                  refine ⟨14207152539534543026622353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37885740105425448070992941 14207152539534543026622353)
                  ·
                    refine ⟨10655364404650907269966765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14207152539534543026622353 10655364404650907269966765)
                    ·
                      refine ⟨3995761651744090226237537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10655364404650907269966765 3995761651744090226237537)
                      ·
                        rfl

theorem cell23_7781718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7781718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781718 prefixEnd_7781718 := by exact prefixLift 7781718
  have htrace : WordTrace (prefixWord ++ tailWord_7781718) baseStart_7781718 baseEnd_7781718 := by
    simpa [prefixWord, tailWord_7781718, baseEnd_7781718] using wordTrace_append hprefix tailTrace_7781718
  have hstable : (prefixWord ++ tailWord_7781718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781718).length < 2 ^ (prefixWord ++ tailWord_7781718).sum := by decide
  have hdescent : baseEnd_7781718 < baseStart_7781718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781737 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 4, 2, 2]
def baseStart_7781737 : Nat := 118140960795 + 7781737 * 2 ^ 59
def prefixEnd_7781737 : Nat := 4983230072969 + 3 ^ 40 * 7781737 * 2
def baseEnd_7781737 : Nat := 3995771407876525651899949

theorem tailTrace_7781737 : CollatzResearch.WordTrace tailWord_7781737 prefixEnd_7781737 3995771407876525651899949 := by
  unfold tailWord_7781737
  simp only [CollatzResearch.WordTrace]
  refine ⟨283823265409103338716431465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189215510272735559144287643 283823265409103338716431465)
  ·
    refine ⟨212867449056827504037323599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283823265409103338716431465 212867449056827504037323599)
    ·
      refine ⟨319301173585241256055985399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212867449056827504037323599 319301173585241256055985399)
      ·
        refine ⟨478951760377861884083978099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319301173585241256055985399 478951760377861884083978099)
        ·
          refine ⟨718427640566792826125967149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478951760377861884083978099 718427640566792826125967149)
          ·
            refine ⟨269410365212547309797237681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 718427640566792826125967149 269410365212547309797237681)
            ·
              refine ⟨202057773909410482347928261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269410365212547309797237681 202057773909410482347928261)
              ·
                refine ⟨37885832608014465440236549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202057773909410482347928261 37885832608014465440236549)
                ·
                  refine ⟨7103593614002712270044353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37885832608014465440236549 7103593614002712270044353)
                  ·
                    refine ⟨5327695210502034202533265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7103593614002712270044353 5327695210502034202533265)
                    ·
                      refine ⟨3995771407876525651899949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327695210502034202533265 3995771407876525651899949)
                      ·
                        rfl

theorem cell23_7781737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 2, 2].length) (baseStart_7781737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781737 prefixEnd_7781737 := by exact prefixLift 7781737
  have htrace : WordTrace (prefixWord ++ tailWord_7781737) baseStart_7781737 baseEnd_7781737 := by
    simpa [prefixWord, tailWord_7781737, baseEnd_7781737] using wordTrace_append hprefix tailTrace_7781737
  have hstable : (prefixWord ++ tailWord_7781737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781737).length < 2 ^ (prefixWord ++ tailWord_7781737).sum := by decide
  have hdescent : baseEnd_7781737 < baseStart_7781737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781740 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_7781740 : Nat := 118140960795 + 7781740 * 2 ^ 59
def prefixEnd_7781740 : Nat := 4983230072969 + 3 ^ 40 * 7781740 * 2
def baseEnd_7781740 : Nat := 3995772948318489140162435

theorem tailTrace_7781740 : CollatzResearch.WordTrace tailWord_7781740 prefixEnd_7781740 3995772948318489140162435 := by
  unfold tailWord_7781740
  simp only [CollatzResearch.WordTrace]
  refine ⟨141911687414046235114395337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189215583218728313485860449 141911687414046235114395337)
  ·
    refine ⟨106433765560534676335796503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141911687414046235114395337 106433765560534676335796503)
    ·
      refine ⟨159650648340802014503694755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106433765560534676335796503 159650648340802014503694755)
      ·
        refine ⟨239475972511203021755542133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159650648340802014503694755 239475972511203021755542133)
        ·
          refine ⟨22450872422925283289582075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239475972511203021755542133 22450872422925283289582075)
          ·
            refine ⟨33676308634387924934373113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22450872422925283289582075 33676308634387924934373113)
            ·
              refine ⟨25257231475790943700779835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33676308634387924934373113 25257231475790943700779835)
              ·
                refine ⟨37885847213686415551169753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25257231475790943700779835 37885847213686415551169753)
                ·
                  refine ⟨28414385410264811663377315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37885847213686415551169753 28414385410264811663377315)
                  ·
                    refine ⟨42621578115397217495065973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28414385410264811663377315 42621578115397217495065973)
                    ·
                      refine ⟨3995772948318489140162435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42621578115397217495065973 3995772948318489140162435)
                      ·
                        rfl

theorem cell23_7781740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_7781740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781740 prefixEnd_7781740 := by exact prefixLift 7781740
  have htrace : WordTrace (prefixWord ++ tailWord_7781740) baseStart_7781740 baseEnd_7781740 := by
    simpa [prefixWord, tailWord_7781740, baseEnd_7781740] using wordTrace_append hprefix tailTrace_7781740
  have hstable : (prefixWord ++ tailWord_7781740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781740).length < 2 ^ (prefixWord ++ tailWord_7781740).sum := by decide
  have hdescent : baseEnd_7781740 < baseStart_7781740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781741 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_7781741 : Nat := 118140960795 + 7781741 * 2 ^ 59
def prefixEnd_7781741 : Nat := 4983230072969 + 3 ^ 40 * 7781741 * 2
def baseEnd_7781741 : Nat := 3995773461799143636249931

theorem tailTrace_7781741 : CollatzResearch.WordTrace tailWord_7781741 prefixEnd_7781741 3995773461799143636249931 := by
  unfold tailWord_7781741
  simp only [CollatzResearch.WordTrace]
  refine ⟨283823411301088847399577077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189215607534059231599718051 283823411301088847399577077)
  ·
    refine ⟨26608444809477079443710351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283823411301088847399577077 26608444809477079443710351)
    ·
      refine ⟨39912667214215619165565527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26608444809477079443710351 39912667214215619165565527)
      ·
        refine ⟨59869000821323428748348291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39912667214215619165565527 59869000821323428748348291)
        ·
          refine ⟨89803501231985143122522437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59869000821323428748348291 89803501231985143122522437)
          ·
            refine ⟨16838156480997214335472957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89803501231985143122522437 16838156480997214335472957)
            ·
              refine ⟨6314308680373955375802359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16838156480997214335472957 6314308680373955375802359)
              ·
                refine ⟨9471463020560933063703539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6314308680373955375802359 9471463020560933063703539)
                ·
                  refine ⟨14207194530841399595555309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9471463020560933063703539 14207194530841399595555309)
                  ·
                    refine ⟨5327697949065524848333241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14207194530841399595555309 5327697949065524848333241)
                    ·
                      refine ⟨3995773461799143636249931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327697949065524848333241 3995773461799143636249931)
                      ·
                        rfl

theorem cell23_7781741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_7781741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781741 prefixEnd_7781741 := by exact prefixLift 7781741
  have htrace : WordTrace (prefixWord ++ tailWord_7781741) baseStart_7781741 baseEnd_7781741 := by
    simpa [prefixWord, tailWord_7781741, baseEnd_7781741] using wordTrace_append hprefix tailTrace_7781741
  have hstable : (prefixWord ++ tailWord_7781741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781741).length < 2 ^ (prefixWord ++ tailWord_7781741).sum := by decide
  have hdescent : baseEnd_7781741 < baseStart_7781741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781753 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_7781753 : Nat := 118140960795 + 7781753 * 2 ^ 59
def prefixEnd_7781753 : Nat := 4983230072969 + 3 ^ 40 * 7781753 * 2
def baseEnd_7781753 : Nat := 3995779623566997589299875

theorem tailTrace_7781753 : CollatzResearch.WordTrace tailWord_7781753 prefixEnd_7781753 3995779623566997589299875 := by
  unfold tailWord_7781753
  simp only [CollatzResearch.WordTrace]
  refine ⟨283823848977045373449013913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189215899318030248966009275 283823848977045373449013913)
  ·
    refine ⟨212867886732784030086760435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283823848977045373449013913 212867886732784030086760435)
    ·
      refine ⟨319301830099176045130140653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212867886732784030086760435 319301830099176045130140653)
      ·
        refine ⟨119738186287191016923802745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319301830099176045130140653 119738186287191016923802745)
        ·
          refine ⟨89803639715393262692852059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119738186287191016923802745 89803639715393262692852059)
          ·
            refine ⟨134705459573089894039278089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89803639715393262692852059 134705459573089894039278089)
            ·
              refine ⟨101029094679817420529458567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134705459573089894039278089 101029094679817420529458567)
              ·
                refine ⟨151543642019726130794187851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101029094679817420529458567 151543642019726130794187851)
                ·
                  refine ⟨227315463029589196191281777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151543642019726130794187851 227315463029589196191281777)
                  ·
                    refine ⟨170486597272191897143461333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227315463029589196191281777 170486597272191897143461333)
                    ·
                      refine ⟨3995779623566997589299875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170486597272191897143461333 3995779623566997589299875)
                      ·
                        rfl

theorem cell23_7781753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_7781753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781753 prefixEnd_7781753 := by exact prefixLift 7781753
  have htrace : WordTrace (prefixWord ++ tailWord_7781753) baseStart_7781753 baseEnd_7781753 := by
    simpa [prefixWord, tailWord_7781753, baseEnd_7781753] using wordTrace_append hprefix tailTrace_7781753
  have hstable : (prefixWord ++ tailWord_7781753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781753).length < 2 ^ (prefixWord ++ tailWord_7781753).sum := by decide
  have hdescent : baseEnd_7781753 < baseStart_7781753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781794 : List Nat := [3, 3, 1, 2, 1, 3, 2, 3, 5]
def baseStart_7781794 : Nat := 118140960795 + 7781794 * 2 ^ 59
def prefixEnd_7781794 : Nat := 4983230072969 + 3 ^ 40 * 7781794 * 2
def baseEnd_7781794 : Nat := 443977852919314658765243

theorem tailTrace_7781794 : CollatzResearch.WordTrace tailWord_7781794 prefixEnd_7781794 443977852919314658765243 := by
  unfold tailWord_7781794
  simp only [CollatzResearch.WordTrace]
  refine ⟨70956336092474209362814109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189216896246597891634170957 70956336092474209362814109)
  ·
    refine ⟨26608626034677828511055291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70956336092474209362814109 26608626034677828511055291)
    ·
      refine ⟨39912939052016742766582937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26608626034677828511055291 39912939052016742766582937)
      ·
        refine ⟨29934704289012557074937203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39912939052016742766582937 29934704289012557074937203)
        ·
          refine ⟨44902056433518835612405805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29934704289012557074937203 44902056433518835612405805)
          ·
            refine ⟨16838271162569563354652177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44902056433518835612405805 16838271162569563354652177)
            ·
              refine ⟨12628703371927172515989133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16838271162569563354652177 12628703371927172515989133)
              ·
                refine ⟨4735763764472689693495925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12628703371927172515989133 4735763764472689693495925)
                ·
                  refine ⟨443977852919314658765243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4735763764472689693495925 443977852919314658765243)
                  ·
                    rfl

theorem cell23_7781794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_7781794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781794 prefixEnd_7781794 := by exact prefixLift 7781794
  have htrace : WordTrace (prefixWord ++ tailWord_7781794) baseStart_7781794 baseEnd_7781794 := by
    simpa [prefixWord, tailWord_7781794, baseEnd_7781794] using wordTrace_append hprefix tailTrace_7781794
  have hstable : (prefixWord ++ tailWord_7781794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781794).length < 2 ^ (prefixWord ++ tailWord_7781794).sum := by decide
  have hdescent : baseEnd_7781794 < baseStart_7781794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781827 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 2, 4, 2]
def baseStart_7781827 : Nat := 118140960795 + 7781827 * 2 ^ 59
def prefixEnd_7781827 : Nat := 4983230072969 + 3 ^ 40 * 7781827 * 2
def baseEnd_7781827 : Nat := 3995817621135430299774535

theorem tailTrace_7781827 : CollatzResearch.WordTrace tailWord_7781827 prefixEnd_7781827 3995817621135430299774535 := by
  unfold tailWord_7781827
  simp only [CollatzResearch.WordTrace]
  refine ⟨283826547978777284087207735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189217698652518189391471823 283826547978777284087207735)
  ·
    refine ⟨425739821968165926130811603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283826547978777284087207735 425739821968165926130811603)
    ·
      refine ⟨638609732952248889196217405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425739821968165926130811603 638609732952248889196217405)
      ·
        refine ⟨239478649857093333448581527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638609732952248889196217405 239478649857093333448581527)
        ·
          refine ⟨359217974785640000172872291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239478649857093333448581527 359217974785640000172872291)
          ·
            refine ⟨538826962178460000259308437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359217974785640000172872291 538826962178460000259308437)
            ·
              refine ⟨25257513852115312512155083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 538826962178460000259308437 25257513852115312512155083)
              ·
                refine ⟨37886270778172968768232625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25257513852115312512155083 37886270778172968768232625)
                ·
                  refine ⟨28414703083629726576174469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37886270778172968768232625 28414703083629726576174469)
                  ·
                    refine ⟨5327756828180573733032713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28414703083629726576174469 5327756828180573733032713)
                    ·
                      refine ⟨3995817621135430299774535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327756828180573733032713 3995817621135430299774535)
                      ·
                        rfl

theorem cell23_7781827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_7781827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781827 prefixEnd_7781827 := by exact prefixLift 7781827
  have htrace : WordTrace (prefixWord ++ tailWord_7781827) baseStart_7781827 baseEnd_7781827 := by
    simpa [prefixWord, tailWord_7781827, baseEnd_7781827] using wordTrace_append hprefix tailTrace_7781827
  have hstable : (prefixWord ++ tailWord_7781827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781827).length < 2 ^ (prefixWord ++ tailWord_7781827).sum := by decide
  have hdescent : baseEnd_7781827 < baseStart_7781827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781850 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 8]
def baseStart_7781850 : Nat := 118140960795 + 7781850 * 2 ^ 59
def prefixEnd_7781850 : Nat := 4983230072969 + 3 ^ 40 * 7781850 * 2
def baseEnd_7781850 : Nat := 443981047910053745531881

theorem tailTrace_7781850 : CollatzResearch.WordTrace tailWord_7781850 prefixEnd_7781850 443981047910053745531881 := by
  unfold tailWord_7781850
  simp only [CollatzResearch.WordTrace]
  refine ⟨70956846714423489753823751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189218257905129306010196669 70956846714423489753823751)
  ·
    refine ⟨106435270071635234630735627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70956846714423489753823751 106435270071635234630735627)
    ·
      refine ⟨159652905107452851946103441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106435270071635234630735627 159652905107452851946103441)
      ·
        refine ⟨119739678830589638959577581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159652905107452851946103441 119739678830589638959577581)
        ·
          refine ⟨44902379561471114609841593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119739678830589638959577581 44902379561471114609841593)
          ·
            refine ⟨33676784671103335957381195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44902379561471114609841593 33676784671103335957381195)
            ·
              refine ⟨50515177006655003936071793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33676784671103335957381195 50515177006655003936071793)
              ·
                refine ⟨37886382754991252952053845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50515177006655003936071793 37886382754991252952053845)
                ·
                  refine ⟨443981047910053745531881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37886382754991252952053845 443981047910053745531881)
                  ·
                    rfl

theorem cell23_7781850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_7781850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781850 prefixEnd_7781850 := by exact prefixLift 7781850
  have htrace : WordTrace (prefixWord ++ tailWord_7781850) baseStart_7781850 baseEnd_7781850 := by
    simpa [prefixWord, tailWord_7781850, baseEnd_7781850] using wordTrace_append hprefix tailTrace_7781850
  have hstable : (prefixWord ++ tailWord_7781850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781850).length < 2 ^ (prefixWord ++ tailWord_7781850).sum := by decide
  have hdescent : baseEnd_7781850 < baseStart_7781850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781887 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 1, 5, 2]
def baseStart_7781887 : Nat := 118140960795 + 7781887 * 2 ^ 59
def prefixEnd_7781887 : Nat := 4983230072969 + 3 ^ 40 * 7781887 * 2
def baseEnd_7781887 : Nat := 3995848429974700065024259

theorem tailTrace_7781887 : CollatzResearch.WordTrace tailWord_7781887 prefixEnd_7781887 3995848429974700065024259 := by
  unfold tailWord_7781887
  simp only [CollatzResearch.WordTrace]
  refine ⟨283828736358559914334391915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189219157572373276222927943 283828736358559914334391915)
  ·
    refine ⟨425743104537839871501587873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283828736358559914334391915 425743104537839871501587873)
    ·
      refine ⟨319307328403379903626190905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425743104537839871501587873 319307328403379903626190905)
      ·
        refine ⟨239480496302534927719643179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319307328403379903626190905 239480496302534927719643179)
        ·
          refine ⟨359220744453802391579464769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239480496302534927719643179 359220744453802391579464769)
          ·
            refine ⟨269415558340351793684598577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359220744453802391579464769 269415558340351793684598577)
            ·
              refine ⟨202061668755263845263448933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269415558340351793684598577 202061668755263845263448933)
              ·
                refine ⟨37886562891611970986896675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202061668755263845263448933 37886562891611970986896675)
                ·
                  refine ⟨56829844337417956480345013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37886562891611970986896675 56829844337417956480345013)
                  ·
                    refine ⟨5327797906632933420032345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56829844337417956480345013 5327797906632933420032345)
                    ·
                      refine ⟨3995848429974700065024259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327797906632933420032345 3995848429974700065024259)
                      ·
                        rfl

theorem cell23_7781887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_7781887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781887 prefixEnd_7781887 := by exact prefixLift 7781887
  have htrace : WordTrace (prefixWord ++ tailWord_7781887) baseStart_7781887 baseEnd_7781887 := by
    simpa [prefixWord, tailWord_7781887, baseEnd_7781887] using wordTrace_append hprefix tailTrace_7781887
  have hstable : (prefixWord ++ tailWord_7781887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781887).length < 2 ^ (prefixWord ++ tailWord_7781887).sum := by decide
  have hdescent : baseEnd_7781887 < baseStart_7781887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781934 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_7781934 : Nat := 118140960795 + 7781934 * 2 ^ 59
def prefixEnd_7781934 : Nat := 4983230072969 + 3 ^ 40 * 7781934 * 2
def baseEnd_7781934 : Nat := 3995872563565461381136543

theorem tailTrace_7781934 : CollatzResearch.WordTrace tailWord_7781934 prefixEnd_7781934 3995872563565461381136543 := by
  unfold tailWord_7781934
  simp only [CollatzResearch.WordTrace]
  refine ⟨35478806323673705170169107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189220300392926427574235237 35478806323673705170169107)
  ·
    refine ⟨53218209485510557755253661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35478806323673705170169107 53218209485510557755253661)
    ·
      refine ⟨19956828557066459158220123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53218209485510557755253661 19956828557066459158220123)
      ·
        refine ⟨29935242835599688737330185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19956828557066459158220123 29935242835599688737330185)
        ·
          refine ⟨22451432126699766552997639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29935242835599688737330185 22451432126699766552997639)
          ·
            refine ⟨33677148190049649829496459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22451432126699766552997639 33677148190049649829496459)
            ·
              refine ⟨50515722285074474744244689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33677148190049649829496459 50515722285074474744244689)
              ·
                refine ⟨37886791713805856058183517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50515722285074474744244689 37886791713805856058183517)
                ·
                  refine ⟨14207546892677196021818819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37886791713805856058183517 14207546892677196021818819)
                  ·
                    refine ⟨21311320339015794032728229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14207546892677196021818819 21311320339015794032728229)
                    ·
                      refine ⟨3995872563565461381136543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21311320339015794032728229 3995872563565461381136543)
                      ·
                        rfl

theorem cell23_7781934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_7781934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781934 prefixEnd_7781934 := by exact prefixLift 7781934
  have htrace : WordTrace (prefixWord ++ tailWord_7781934) baseStart_7781934 baseEnd_7781934 := by
    simpa [prefixWord, tailWord_7781934, baseEnd_7781934] using wordTrace_append hprefix tailTrace_7781934
  have hstable : (prefixWord ++ tailWord_7781934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781934).length < 2 ^ (prefixWord ++ tailWord_7781934).sum := by decide
  have hdescent : baseEnd_7781934 < baseStart_7781934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781944 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 2, 4]
def baseStart_7781944 : Nat := 118140960795 + 7781944 * 2 ^ 59
def prefixEnd_7781944 : Nat := 4983230072969 + 3 ^ 40 * 7781944 * 2
def baseEnd_7781944 : Nat := 1331959232790668780670499

theorem tailTrace_7781944 : CollatzResearch.WordTrace tailWord_7781944 prefixEnd_7781944 1331959232790668780670499 := by
  unfold tailWord_7781944
  simp only [CollatzResearch.WordTrace]
  refine ⟨141915407659676706534608443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189220543546235608712811257 141915407659676706534608443)
  ·
    refine ⟨212873111489515059801912665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141915407659676706534608443 212873111489515059801912665)
    ·
      refine ⟨159654833617136294851434499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212873111489515059801912665 159654833617136294851434499)
      ·
        refine ⟨239482250425704442277151749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159654833617136294851434499 239482250425704442277151749)
        ·
          refine ⟨44902921954819582926965953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239482250425704442277151749 44902921954819582926965953)
          ·
            refine ⟨33677191466114687195224465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44902921954819582926965953 33677191466114687195224465)
            ·
              refine ⟨25257893599586015396418349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33677191466114687195224465 25257893599586015396418349)
              ·
                refine ⟨9471710099844755773656881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25257893599586015396418349 9471710099844755773656881)
                ·
                  refine ⟨7103782574883566830242661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9471710099844755773656881 7103782574883566830242661)
                  ·
                    refine ⟨1331959232790668780670499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103782574883566830242661 1331959232790668780670499)
                    ·
                      rfl

theorem cell23_7781944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_7781944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781944 prefixEnd_7781944 := by exact prefixLift 7781944
  have htrace : WordTrace (prefixWord ++ tailWord_7781944) baseStart_7781944 baseEnd_7781944 := by
    simpa [prefixWord, tailWord_7781944, baseEnd_7781944] using wordTrace_append hprefix tailTrace_7781944
  have hstable : (prefixWord ++ tailWord_7781944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781944).length < 2 ^ (prefixWord ++ tailWord_7781944).sum := by decide
  have hdescent : baseEnd_7781944 < baseStart_7781944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
